# pick.ml

## Overview

Number of statements: 45

This file formalizes Pick's theorem, which relates the area of a simple polygon with integer vertex coordinates to the number of integer points inside and on the boundary of the polygon. It builds on the polytope, measure, and topology foundations from the multivariate analysis library. The file proves that the area of such a polygon equals the number of interior integer points plus half the number of boundary points minus one (A = I + B/2 - 1).

## COLLINEAR_IMP_NEGLIGIBLE

### COLLINEAR_IMP_NEGLIGIBLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let COLLINEAR_IMP_NEGLIGIBLE = prove
 (`!s:real^2->bool. collinear s ==> negligible s`,
  REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
  MESON_TAC[NEGLIGIBLE_AFFINE_HULL_2; NEGLIGIBLE_SUBSET]);;
```

### Informal statement
For any set $s$ in $\mathbb{R}^2$, if $s$ is collinear, then $s$ is negligible.

Precisely, if all points in a set $s \subseteq \mathbb{R}^2$ lie on a single line (i.e., $s$ is collinear), then $s$ has Lebesgue measure zero (i.e., $s$ is negligible).

### Informal proof
The proof proceeds as follows:

- First, we rewrite using the theorem `COLLINEAR_AFFINE_HULL`, which states that a set $s$ is collinear if and only if the affine hull of $s$ is contained in the affine hull of some set $\{a,b\}$ where $a,b \in \mathbb{R}^2$.

- This means that $s$ is a subset of the affine hull of two points in $\mathbb{R}^2$.

- We then use `NEGLIGIBLE_AFFINE_HULL_2`, which states that the affine hull of any two points in $\mathbb{R}^2$ is negligible (i.e., has measure zero).

- By `NEGLIGIBLE_SUBSET`, any subset of a negligible set is also negligible.

- Therefore, since $s$ is contained in the affine hull of two points, and this affine hull is negligible, $s$ must also be negligible.

### Mathematical insight
This theorem establishes an important connection between geometry and measure theory in $\mathbb{R}^2$. 

The key insight is that any collinear set in the plane (i.e., points lying on a straight line) has Lebesgue measure zero. This is intuitive because a line in $\mathbb{R}^2$ has "zero thickness" - it only extends in one dimension rather than two.

This result is useful in various geometric measure theory contexts and appears as a preliminary result in the development toward Pick's theorem, which relates the area of lattice polygons to the number of integer points they contain.

### Dependencies
#### Theorems
- `COLLINEAR_AFFINE_HULL`: Characterizes collinear sets in terms of their affine hull
- `NEGLIGIBLE_AFFINE_HULL_2`: Proves that the affine hull of two points in $\mathbb{R}^2$ is negligible
- `NEGLIGIBLE_SUBSET`: States that any subset of a negligible set is also negligible

### Porting notes
When porting this theorem:
- Ensure that your target system has a well-defined notion of "negligible" sets, typically meaning sets of Lebesgue measure zero
- The concept of "affine hull" should be properly defined
- The dimensionality of $\mathbb{R}^2$ is important here - this result relies on the fact that lines in a 2D space have measure zero

---

## CONVEX_HULL_3_0

### CONVEX_HULL_3_0

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONVEX_HULL_3_0 = prove
 (`!a b:real^N.
        convex hull {vec 0,a,b} =
        {x % a + y % b | &0 <= x /\ &0 <= y /\ x + y <= &1}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {a,b,c}`] THEN
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `y:real` THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_ARITH_TAC; EXISTS_TAC `&1 - x - y` THEN ASM_ARITH_TAC]);;
```

### Informal statement
For any vectors $a, b \in \mathbb{R}^N$, the convex hull of the set $\{0, a, b\}$ (where $0$ is the zero vector) is equal to the set:
$$\{x \cdot a + y \cdot b \mid 0 \leq x \land 0 \leq y \land x + y \leq 1\}$$

### Informal proof
We need to prove that the convex hull of $\{0, a, b\}$ equals the set of all linear combinations $\{x \cdot a + y \cdot b \mid 0 \leq x, 0 \leq y, x + y \leq 1\}$.

1. First, we rewrite $\{0, a, b\}$ as $\{a, b, 0\}$ using set equality.

2. We then apply the theorem `CONVEX_HULL_3`, which states that the convex hull of three points $\{a, b, c\}$ is the set of points that can be written as $u \cdot a + v \cdot b + w \cdot c$ where $u, v, w \geq 0$ and $u + v + w = 1$.

3. For our case, this means the convex hull of $\{a, b, 0\}$ is:
   $$\{u \cdot a + v \cdot b + w \cdot 0 \mid u, v, w \geq 0 \land u + v + w = 1\}$$

4. Since $w \cdot 0 = 0$, this simplifies to:
   $$\{u \cdot a + v \cdot b \mid u, v, w \geq 0 \land u + v + w = 1\}$$

5. To prove the equality of sets, we show both inclusions:
   - For the forward direction, if $u \cdot a + v \cdot b$ is in the convex hull with $u, v \geq 0$ and $u + v + w = 1$ (where $w \geq 0$), then $u + v \leq 1$. So this point is in our target set with $x = u$ and $y = v$.
   
   - For the reverse direction, if $x \cdot a + y \cdot b$ is in our target set with $x, y \geq 0$ and $x + y \leq 1$, then we can set $u = x$, $v = y$, and $w = 1 - x - y$ to get a point in the convex hull. Note that $w \geq 0$ since $x + y \leq 1$.

6. Both inclusions are proven, establishing the equality.

### Mathematical insight
This theorem gives an explicit parametric representation of the convex hull of three points where one is the origin. The result shows that this convex hull is a triangular region in $\mathbb{R}^N$ with vertices at the origin, $a$, and $b$.

The theorem simplifies the general representation of convex hulls by taking advantage of the special case where one point is the origin, making calculations and applications more straightforward.

In geometric terms, this represents a triangle (if $a$ and $b$ are linearly independent) or a line segment (if $a$ and $b$ are linearly dependent) with one vertex at the origin.

### Dependencies
- `CONVEX_HULL_3`: The general formula for the convex hull of three points.
- `SET_RULE`: A rule for set manipulation.
- Various vector arithmetic properties:
  - `VECTOR_MUL_RZERO`: Multiplication of a vector by zero.
  - `VECTOR_ADD_RID`: Addition of a vector with the zero vector.

### Porting notes
When porting this theorem:
- Ensure that your target system has a well-defined notion of convex hull.
- The proof relies heavily on set equality and vector arithmetic, so those foundations need to be in place.
- The parameterization of the convex hull using the coefficient constraints ($0 \leq x \land 0 \leq y \land x + y \leq 1$) should be preserved.
- Some systems might have different conventions for scalar-vector multiplication notation.

---

## INTERIOR_CONVEX_HULL_3_0

### INTERIOR_CONVEX_HULL_3_0
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INTERIOR_CONVEX_HULL_3_0 = prove
 (`!a b:real^2.
        ~(collinear {vec 0,a,b})
        ==> interior(convex hull {vec 0,a,b}) =
              {x % a + y % b | &0 < x /\ &0 < y /\ x + y < &1}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {a,b,c}`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3] THEN
  REWRITE_TAC[TAUT `a /\ x = &1 /\ b <=> x = &1 /\ a /\ b`] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `x + y + z = &1 <=> &1 - x - y = z`; UNWIND_THM1] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any vectors $a, b \in \mathbb{R}^2$, if the set $\{0, a, b\}$ is not collinear, then the interior of the convex hull of $\{0, a, b\}$ is equal to:
$$\text{interior}(\text{convex hull}(\{0, a, b\})) = \{x \cdot a + y \cdot b \mid 0 < x \land 0 < y \land x + y < 1\}$$

### Informal proof
The proof proceeds as follows:

- First, rewrite $\{0, a, b\}$ as $\{a, b, 0\}$ using the set theory rule that order doesn't matter.
- Apply `INTERIOR_CONVEX_HULL_3` to compute the interior of the convex hull of three non-collinear points.
- This theorem gives the interior as a set of convex combinations with strictly positive coefficients.
- Simplify by handling the zero vector explicitly:
  * When we have $x \cdot a + y \cdot b + z \cdot 0$ with $x + y + z = 1$, this reduces to $x \cdot a + y \cdot b$ with $x + y + z = 1$.
  * Since $0 \cdot 0 = 0$ and $v + 0 = v$, we can simplify further.
- Use arithmetic to rewrite $x + y + z = 1$ as $z = 1 - x - y$.
- Expand definitions and use extensionality to show set equality.
- The proof concludes with real arithmetic to establish the equivalence between:
  * The set of points $x \cdot a + y \cdot b + (1-x-y) \cdot 0$ where $0 < x$, $0 < y$, and $0 < 1-x-y$
  * The set $\{x \cdot a + y \cdot b \mid 0 < x \land 0 < y \land x + y < 1\}$

### Mathematical insight
This theorem provides a concrete characterization of the interior of a triangle with one vertex at the origin. The result expresses the interior points as strict convex combinations of the non-origin vertices, with the additional constraint that the sum of coefficients is less than 1.

This is a specialized version of a more general result about the interior of convex hulls, tailored for the specific case of a triangle with one vertex at the origin. The characterization is particularly useful in computational geometry, convex analysis, and when working with barycentric coordinates in a plane.

### Dependencies
- `INTERIOR_CONVEX_HULL_3`: Provides the general form of the interior of the convex hull of three non-collinear points
- `SET_RULE`: For basic set manipulations
- `VECTOR_MUL_RZERO`: Handles multiplication of a vector by zero
- `VECTOR_ADD_RID`: Handles addition of a vector with the zero vector

### Porting notes
When porting this theorem:
- Ensure that the target system has a way to represent vectors in $\mathbb{R}^2$ and operations on them
- The concept of collinearity needs to be defined in the target system
- The proof makes heavy use of real arithmetic, so the target system should have good automation for such reasoning
- Pay attention to how the target system handles convex combinations and convex hulls

---

## MEASURE_CONVEX_HULL_2_TRIVIAL

### Name of formal statement
MEASURE_CONVEX_HULL_2_TRIVIAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MEASURE_CONVEX_HULL_2_TRIVIAL = prove
 (`(!a:real^2. measure(convex hull {a}) = &0) /\
   (!a b:real^2. measure(convex hull {a,b}) = &0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_EQ_0 THEN
  MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; CONVEX_HULL_SING] THEN
  REWRITE_TAC[COLLINEAR_SING; COLLINEAR_SEGMENT]);;
```

### Informal statement
For any points in $\mathbb{R}^2$:
1. The measure of the convex hull of a singleton set $\{a\}$ is zero: $\text{measure}(\text{convex hull } \{a\}) = 0$
2. The measure of the convex hull of a set with two points $\{a,b\}$ is zero: $\text{measure}(\text{convex hull } \{a,b\}) = 0$

### Informal proof
The proof establishes that the convex hull of one or two points in $\mathbb{R}^2$ has measure zero by showing these sets are collinear, and therefore negligible.

1. For both cases (singleton and pair of points), we apply the same strategy:
   - Apply `MEASURE_EQ_0`, which states that negligible sets have measure zero
   - Use `COLLINEAR_IMP_NEGLIGIBLE`, which states that any collinear set in $\mathbb{R}^2$ is negligible

2. Then for each specific case:
   - For a singleton $\{a\}$, we use that `CONVEX_HULL_SING` shows the convex hull of a singleton is just the singleton itself
   - For a pair $\{a,b\}$, we use that `SEGMENT_CONVEX_HULL` shows the convex hull equals the line segment between the points

3. Finally, we apply:
   - `COLLINEAR_SING` which states that any singleton set is collinear
   - `COLLINEAR_SEGMENT` which states that any line segment is collinear

### Mathematical insight
This theorem establishes the intuitive fact that points and line segments in $\mathbb{R}^2$ have zero area (measure). This is important because:

1. It confirms that one-dimensional objects embedded in two-dimensional space have zero measure
2. It serves as a foundational result for measure theory in $\mathbb{R}^2$
3. It demonstrates that the convex hull operation preserves dimensionality when applied to low-dimensional objects

The result is trivial in the mathematical sense (hence "trivial" in the name), but formally proving such basic facts is necessary to build a rigorous foundation for computational geometry and measure theory.

### Dependencies
- **Theorems:**
  - `MEASURE_EQ_0`: If a set is negligible, then its measure is zero
  - `COLLINEAR_IMP_NEGLIGIBLE`: Any collinear set in $\mathbb{R}^2$ is negligible
  - `CONVEX_HULL_SING`: The convex hull of a singleton is the singleton itself
  - `SEGMENT_CONVEX_HULL`: The convex hull of two points is the line segment between them
  - `COLLINEAR_SING`: A singleton set is collinear
  - `COLLINEAR_SEGMENT`: A line segment is collinear

- **Definitions:**
  - `measure`: The measure of a set defined using the choice operator, as a value `m` such that the set `has_measure m`

### Porting notes
When porting this theorem:
1. Ensure the target system has appropriate definitions for measure, convex hull, negligibility, and collinearity
2. The proof relies on the fact that collinear sets are negligible in $\mathbb{R}^2$, which may need explicit formulation in other systems
3. The choice operator in the definition of `measure` might need alternative treatment in constructive systems

---

## NEGLIGIBLE_SEGMENT_2

### NEGLIGIBLE_SEGMENT_2
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let NEGLIGIBLE_SEGMENT_2 = prove
 (`!a b:real^2. negligible(segment[a,b])`,
  SIMP_TAC[COLLINEAR_IMP_NEGLIGIBLE; COLLINEAR_SEGMENT]);;
```

### Informal statement
The theorem states that for any two points $a$ and $b$ in $\mathbb{R}^2$, the line segment between them has negligible (zero) measure:

$$\forall a, b \in \mathbb{R}^2, \text{negligible}(\text{segment}[a,b])$$

Here, $\text{segment}[a,b]$ represents the closed line segment connecting points $a$ and $b$, and $\text{negligible}$ indicates a set with Lebesgue measure zero.

### Informal proof
The proof follows directly from two facts:
* Any collinear set in $\mathbb{R}^2$ is negligible (theorem `COLLINEAR_IMP_NEGLIGIBLE`)
* A line segment is collinear (theorem `COLLINEAR_SEGMENT`)

By applying these facts together using simplification tactics, we establish that any line segment in $\mathbb{R}^2$ has measure zero.

### Mathematical insight
This theorem captures the fundamental topological and measure-theoretic property that one-dimensional objects like line segments have zero measure in two-dimensional space. This is a canonical result in measure theory.

The result is important when working with integration in $\mathbb{R}^2$, as it confirms that line segments can be ignored when computing integrals. It's also relevant in probability theory, where it establishes that the probability of a random point in the plane falling exactly on a given line segment is zero.

### Dependencies
- `COLLINEAR_IMP_NEGLIGIBLE`: Proves that any collinear set in $\mathbb{R}^2$ has measure zero
- `COLLINEAR_SEGMENT`: Establishes that a line segment is a collinear set

### Porting notes
When porting this theorem to other proof assistants, ensure that:
1. The definitions of "negligible" (measure zero) and "segment" are consistent
2. The prerequisite theorems about collinearity implying negligible measure are established
3. In typed systems, the dimension constraints (specifically $\mathbb{R}^2$) are properly handled

---

## TRIANGLE_DECOMPOSITION

### Name of formal statement
TRIANGLE_DECOMPOSITION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_DECOMPOSITION = prove
 (`!a b c d:real^2.
        d IN convex hull {a,b,c}
        ==> (convex hull {a,b,c} =
             convex hull {d,b,c} UNION
             convex hull {d,a,c} UNION
             convex hull {d,a,b})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{a:real^2,b,c}`; `d:real^2`; `x:real^2`]
     IN_CONVEX_HULL_EXCHANGE) THEN
    ASM_REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY; IN_UNION] THEN
    REPEAT(MATCH_MP_TAC MONO_OR THEN CONJ_TAC) THEN
    SPEC_TAC(`x:real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    SIMP_TAC[SUBSET_HULL; CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[HULL_INC; IN_INSERT]]);;
```

### Informal statement
For any points $a, b, c, d \in \mathbb{R}^2$, if $d$ is in the convex hull of the set $\{a, b, c\}$, then the convex hull of $\{a, b, c\}$ equals the union of three convex hulls:
$$\text{conv}(\{a, b, c\}) = \text{conv}(\{d, b, c\}) \cup \text{conv}(\{d, a, c\}) \cup \text{conv}(\{d, a, b\})$$

### Informal proof
The proof shows that the two sets are equal by demonstrating that they are subsets of each other:

1. First, we show that $\text{conv}(\{a, b, c\}) \subseteq \text{conv}(\{d, b, c\}) \cup \text{conv}(\{d, a, c\}) \cup \text{conv}(\{d, a, b\})$:
   - For any $x \in \text{conv}(\{a, b, c\})$, we use the theorem `IN_CONVEX_HULL_EXCHANGE`, which states that if $d \in \text{conv}(S)$ and $x \in \text{conv}(S)$, then $x \in \text{conv}((S \setminus \{p\}) \cup \{d\})$ for some $p \in S$.
   - Since $d \in \text{conv}(\{a, b, c\})$ and $x \in \text{conv}(\{a, b, c\})$, we can replace some point in $\{a, b, c\}$ with $d$ and still have $x$ in the resulting convex hull.
   - This means $x$ must be in at least one of $\text{conv}(\{d, b, c\})$, $\text{conv}(\{d, a, c\})$, or $\text{conv}(\{d, a, b\})$.

2. Next, we show that $\text{conv}(\{d, b, c\}) \cup \text{conv}(\{d, a, c\}) \cup \text{conv}(\{d, a, b\}) \subseteq \text{conv}(\{a, b, c\})$:
   - We use the properties that convex hulls are convex and that the convex hull operation is monotonic with respect to subset inclusion.
   - Since $d \in \text{conv}(\{a, b, c\})$, and $a, b, c \in \text{conv}(\{a, b, c\})$ (by `HULL_INC`), all points in each of the three smaller convex hulls must also be in $\text{conv}(\{a, b, c\})$.

### Mathematical insight
This theorem provides a geometrical decomposition of a triangle (represented by the convex hull of three points $a$, $b$, and $c$) into three sub-triangles formed by connecting an internal point $d$ to each of the three vertices.

This is a fundamental result in computational geometry and has applications in:
1. Triangulation algorithms
2. Barycentric coordinate systems
3. Finite element methods

The theorem effectively states that if you place a point $d$ anywhere inside a triangle, you can divide the original triangle into three smaller triangles that completely cover the original one, with no gaps or overlaps.

### Dependencies
- `IN_CONVEX_HULL_EXCHANGE`: Theorem about exchanging points in convex hulls
- `HULL_MONO`: Monotonicity of the hull operation
- `HULL_INC`: Points are in their convex hull
- `CONVEX_CONVEX_HULL`: Convex hull is convex
- `SUBSET_HULL`: Relation between a set and its convex hull

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the definition of convex hull is compatible
2. Some systems might require explicit handling of the 2-dimensional vector space
3. The proof relies on set-theoretic manipulations and properties of convex sets, which might be formalized differently in other systems

---

## TRIANGLE_ADDITIVE_DECOMPOSITION

### Name of formal statement
TRIANGLE_ADDITIVE_DECOMPOSITION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TRIANGLE_ADDITIVE_DECOMPOSITION = prove
 (`!f:(real^2->bool)->real a b c d.
        (!s t. compact s /\ compact t
               ==> f(s UNION t) = f(s) + f(t) - f(s INTER t)) /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        ~affine_dependent {a,b,c} /\ d IN convex hull {a,b,c}
        ==> f(convex hull {a,b,c}) =
            (f(convex hull {a,b,d}) +
             f(convex hull {a,c,d}) +
             f(convex hull {b,c,d})) -
            (f(convex hull {a,d}) +
             f(convex hull {b,d}) +
             f(convex hull {c,d})) +
            f(convex hull {d})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP TRIANGLE_DECOMPOSITION) THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [COMPACT_UNION; COMPACT_INTER; COMPACT_CONVEX_HULL;
               FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY;
               UNION_OVER_INTER] THEN
  MP_TAC(ISPECL [`{a:real^2,b,c}`; `d:real^2`]
        CONVEX_HULL_EXCHANGE_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY;
           SET_RULE `s SUBSET u /\ t SUBSET u ==> (s INTER t) SUBSET u`] THEN
  ASM_REWRITE_TAC[INSERT_INTER; IN_INSERT; NOT_IN_EMPTY; INTER_EMPTY] THEN
  DISCH_TAC THEN REWRITE_TAC[INSERT_AC] THEN REAL_ARITH_TAC);;
```

### Informal statement
Let $f$ be a function from sets of points in $\mathbb{R}^2$ to $\mathbb{R}$ that satisfies the inclusion-exclusion property: for any compact sets $s$ and $t$, we have 
$$f(s \cup t) = f(s) + f(t) - f(s \cap t)$$

Let $a, b, c$ be three non-collinear points in $\mathbb{R}^2$ (i.e., not affine dependent) such that $a \neq b$, $a \neq c$, and $b \neq c$. If $d$ is a point in the convex hull of $\{a, b, c\}$, then:

$$f(\text{convex hull }\{a, b, c\}) = \begin{align} 
&(f(\text{convex hull }\{a, b, d\}) + f(\text{convex hull }\{a, c, d\}) + f(\text{convex hull }\{b, c, d\})) \\
&- (f(\text{convex hull }\{a, d\}) + f(\text{convex hull }\{b, d\}) + f(\text{convex hull }\{c, d\})) \\
&+ f(\text{convex hull }\{d\})
\end{align}$$

### Informal proof
The proof proceeds as follows:

1. We start by applying the `TRIANGLE_DECOMPOSITION` theorem to decompose the convex hull of $\{a, b, c\}$:
   
   Since $d \in \text{convex hull }\{a, b, c\}$, we have:
   $$\text{convex hull }\{a, b, c\} = \text{convex hull }\{d, b, c\} \cup \text{convex hull }\{d, a, c\} \cup \text{convex hull }\{d, a, b\}$$

2. We apply the inclusion-exclusion property of $f$ to this decomposition. This requires several steps:
   
   * First, we simplify by noting that unions and intersections of compact convex hulls remain compact.
   * We reorder the sets using commutativity and associativity of set operations.

3. We then need to calculate the intersections of these convex hulls. Using the `CONVEX_HULL_EXCHANGE_INTER` theorem, we analyze the intersections of the form:
   $$\text{convex hull }\{d, p, q\} \cap \text{convex hull }\{d, r, s\}$$
   where $p, q, r, s \in \{a, b, c\}$.

4. These intersections simplify to convex hulls of smaller sets, specifically:
   * The pairwise intersections are of the form $\text{convex hull }\{d, x\}$ where $x \in \{a, b, c\}$
   * The triple intersection is $\text{convex hull }\{d\}$

5. Finally, we apply real arithmetic to verify that the given formula holds by substituting all these terms into the inclusion-exclusion formula.

### Mathematical insight
This theorem establishes an additive decomposition formula for functions that satisfy the inclusion-exclusion principle when applied to triangular regions in the plane. It shows how to express the value of such a function on a triangle in terms of its values on subtriangles formed by connecting an interior point to the vertices.

This is particularly useful for:
1. Area calculations and other geometric measures
2. Recursive calculations of integrals over triangular regions
3. Numerical methods that decompose triangular domains

The formula expresses a kind of "telescoping" property with alternating signs based on dimension - triangles (dimension 2), then edges (dimension 1), then a single point (dimension 0).

### Dependencies
- Theorems:
  - `TRIANGLE_DECOMPOSITION`: States that if d is in the convex hull of {a,b,c}, then this convex hull equals the union of three convex hulls: {d,b,c}, {d,a,c}, and {d,a,b}
  - `CONVEX_HULL_EXCHANGE_INTER`: Used for analyzing intersections of convex hulls
  - Various theorems about compactness, unions, and intersections

### Porting notes
When porting this theorem:
1. Ensure that the target system has a good library for convex geometry and set operations
2. Pay attention to how the inclusion-exclusion principle is formalized in the target system
3. The proof relies heavily on set-theoretic manipulations, so ensure the target system has good automation for this
4. The theorem requires a notion of affine independence which might be formalized differently in other systems

---

## integral_vector

### Name of formal statement
integral_vector

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let integral_vector = define
 `integral_vector(x:real^N) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i)`;;
```

### Informal statement
$\text{integral\_vector}(x)$ is defined for a vector $x \in \mathbb{R}^N$ and means that all coordinates of $x$ are integers. Formally:

$$\text{integral\_vector}(x) \iff \forall i. (1 \leq i \wedge i \leq \text{dimindex}(:N)) \Rightarrow \text{integer}(x_i)$$

where:
- $x$ is a vector in $\mathbb{R}^N$
- $\text{dimindex}(:N)$ is the dimension of the vector space
- $x_i$ (denoted as $x\$i$ in HOL Light) is the $i$-th component of $x$
- $\text{integer}(x_i)$ means $x_i$ is an integer

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition formalizes the concept of integer vectors (vectors whose components are all integers). Such vectors form the integer lattice $\mathbb{Z}^N$ within $\mathbb{R}^N$.

Integer vectors are fundamental in many mathematical areas:
- Lattice theory
- Number theory
- Discrete geometry
- Computational geometry
- Linear Diophantine equations

The definition uses HOL Light's indexing convention for vectors, where components are accessed with indices starting at 1 up to the dimension of the vector space.

### Dependencies
#### Definitions
- `integer` - Predicate indicating that a real number is an integer
- `dimindex` - Function that returns the dimension of a type-indexed vector space

### Porting notes
When porting this definition:
1. Ensure that the target system has corresponding concepts for:
   - Vectors with real components
   - Indexing into vectors
   - Type-parameterized dimensions
   - Integer predicate for reals
2. Adjust for any differences in vector indexing conventions (0-based vs. 1-based)
3. The definition is straightforward but depends on the specific representation of vectors and type parameters in the target system

---

## INTEGRAL_VECTOR_VEC

### INTEGRAL_VECTOR_VEC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INTEGRAL_VECTOR_VEC = prove
 (`!n. integral_vector(vec n)`,
  REWRITE_TAC[integral_vector; VEC_COMPONENT; INTEGER_CLOSED]);;
```

### Informal statement
For all natural numbers $n$, the vector $\text{vec}(n)$ is an integral vector.

Here, an integral vector means a vector where all components are integers, and $\text{vec}(n)$ represents the vector of dimension $N$ with all components equal to $n$.

More formally: $\forall n. \text{integral\_vector}(\text{vec}(n))$

### Informal proof
The proof is straightforward:

1. We expand the definition of `integral_vector`, which states that a vector $x$ is integral if all of its components are integers.

2. We then use the fact that the components of $\text{vec}(n)$ are all equal to $n$ (using the property of `VEC_COMPONENT`).

3. Finally, we apply `INTEGER_CLOSED` to establish that $n$ is an integer, which completes the proof.

### Mathematical insight
This theorem establishes that constant vectors whose components are all equal to the same natural number are integral vectors. This is a basic but important property that connects the `vec` constructor with the `integral_vector` predicate.

The result is particularly useful in lattice theory, integer programming, and other areas where working with vectors having integer coordinates is important.

### Dependencies
- **Definitions**:
  - `integral_vector`: A predicate specifying that a vector has all integer components

- **Theorems**:
  - `VEC_COMPONENT`: Characterizes the components of a vector created by the `vec` constructor
  - `INTEGER_CLOSED`: Establishes that natural numbers are integers

### Porting notes
When porting to another system, ensure that:
1. The concept of an integral vector is defined similarly
2. The `vec` constructor creates a vector with all components equal to the given value
3. The system recognizes that natural numbers are integers

This should be a straightforward port in most theorem provers with basic vector support.

---

## INTEGRAL_VECTOR_STDBASIS

### Name of formal statement
INTEGRAL_VECTOR_STDBASIS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INTEGRAL_VECTOR_STDBASIS = prove
 (`!i. integral_vector(basis i:real^N)`,
  REWRITE_TAC[integral_vector] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BASIS_COMPONENT] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED]);;
```

### Informal statement
For all indices $i$, the standard basis vector $\text{basis}(i)$ in $\mathbb{R}^N$ is an integral vector.

Here, an integral vector means a vector where all components are integers.

### Informal proof
We need to show that for any standard basis vector $\text{basis}(i)$, all of its components are integers.

First, we unfold the definition of `integral_vector` which states that a vector $x \in \mathbb{R}^N$ is integral if all of its components $x_j$ for $1 \leq j \leq \dim(N)$ are integers.

Then, for any component $j$ of $\text{basis}(i)$, we apply the known property of basis vectors: the $j$-th component of $\text{basis}(i)$ is 1 if $j = i$, and 0 otherwise.

In both cases, the component is either 0 or 1, which are both integers. This is formalized by the theorem `INTEGER_CLOSED` which states that integers are closed under these specific values.

### Mathematical insight
This theorem establishes that the standard basis vectors, which form the fundamental building blocks of the vector space $\mathbb{R}^N$, are integral vectors. This is an important basic property that's often used when working with lattices, integer programming, or any context where we need to combine basis vectors to form other integral vectors.

The standard basis vectors are the most elementary integral vectors, with each having exactly one entry of 1 and all other entries being 0. This theorem formally confirms this property within the HOL Light system.

### Dependencies
#### Definitions
- `integral_vector`: Defines when a vector in $\mathbb{R}^N$ has all integer components

#### Theorems (implicit)
- `BASIS_COMPONENT`: Defines the components of basis vectors
- `INTEGER_CLOSED`: States that specific values (like 0 and 1) are integers

---

## INTEGRAL_VECTOR_ADD

### INTEGRAL_VECTOR_ADD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INTEGRAL_VECTOR_ADD = prove
 (`!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x + y)`,
  SIMP_TAC[integral_vector; VECTOR_ADD_COMPONENT; INTEGER_CLOSED]);;
```

### Informal statement
For any vectors $x, y \in \mathbb{R}^N$, if both $x$ and $y$ have integer components (i.e., $x$ and $y$ are integral vectors), then their sum $x + y$ also has integer components (i.e., is an integral vector).

Formally, for all $x, y \in \mathbb{R}^N$, if $\text{integral\_vector}(x)$ and $\text{integral\_vector}(y)$, then $\text{integral\_vector}(x + y)$.

### Informal proof
The proof follows directly from properties of integer arithmetic:

1. By definition, a vector is integral if all its components are integers.
2. For any component index $i$ (where $1 \leq i \leq \dim N$), the $i$-th component of $x + y$ is $(x + y)_i = x_i + y_i$.
3. Since $x$ and $y$ are integral vectors, both $x_i$ and $y_i$ are integers.
4. The sum of two integers is an integer (by the closure property of integers under addition).
5. Therefore, each component of $x + y$ is an integer, meaning $x + y$ is an integral vector.

### Mathematical insight
This theorem establishes that the set of vectors with integer components is closed under vector addition. This is a fundamental property that shows integral vectors form an additive subgroup of $\mathbb{R}^N$. This result is important for various applications in number theory, lattice theory, and discrete geometry, where integral vectors often represent points with integer coordinates in a Euclidean space.

### Dependencies
- Definitions:
  - `integral_vector`: Defines a vector in $\mathbb{R}^N$ to have integer components for all indices from 1 to dimindex(:N)

- Theorems used in the proof:
  - `VECTOR_ADD_COMPONENT`: States that the components of a vector sum are the sums of the corresponding components
  - `INTEGER_CLOSED`: States that integers are closed under addition (i.e., the sum of two integers is an integer)

### Porting notes
When porting this theorem to other proof assistants:
- Ensure that the definition of integral vectors matches (all components being integers)
- The proof relies on basic properties of vector addition and integer arithmetic, which should be available in most proof assistants with mathematical libraries
- The implementation might differ in systems with different indexing conventions (e.g., 0-based indexing instead of 1-based indexing)

---

## INTEGRAL_VECTOR_SUB

### INTEGRAL_VECTOR_SUB
- INTEGRAL_VECTOR_SUB

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INTEGRAL_VECTOR_SUB = prove
 (`!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x - y)`,
  SIMP_TAC[integral_vector; VECTOR_SUB_COMPONENT; INTEGER_CLOSED]);;
```

### Informal statement
For any vectors $x$ and $y$ in $\mathbb{R}^N$, if both $x$ and $y$ are integral vectors (meaning all their components are integers), then their difference $x - y$ is also an integral vector.

### Informal proof
The proof follows directly from:
- The definition of an integral vector: a vector is integral if all its components are integers
- The fact that the components of a vector difference are the differences of the corresponding components: $(x - y)_i = x_i - y_i$
- The closure of integers under subtraction: if $a$ and $b$ are integers, then $a - b$ is also an integer

The proof applies these facts by simplifying the goal using the definition of `integral_vector`, the component-wise nature of vector subtraction, and the closure property of integers under subtraction.

### Mathematical insight
This theorem establishes that the set of integral vectors (vectors with integer components) is closed under subtraction. This is a basic property needed to establish that integral vectors form a group under vector addition, which is important in various areas of mathematics such as lattice theory, number theory, and crystallography.

The result is part of a broader collection of properties about integral vectors, which together help formalize the algebraic structure of the integer lattice $\mathbb{Z}^N$ within the real vector space $\mathbb{R}^N$.

### Dependencies
- Definitions:
  - `integral_vector` - Defines when a real vector has all integer components
- Properties used:
  - `VECTOR_SUB_COMPONENT` - States that the components of a vector difference are the differences of the corresponding components
  - `INTEGER_CLOSED` - States that integers are closed under basic operations like subtraction

### Porting notes
When porting to other systems:
- Ensure that the target system has a compatible definition of vectors with components that can be accessed by index
- Verify that the integer closure properties are available in the target system's standard library
- The proof is straightforward and should translate easily to most proof assistants that have basic vector operations and integer properties

---

## INTEGRAL_VECTOR_ADD_LCANCEL

### INTEGRAL_VECTOR_ADD_LCANCEL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INTEGRAL_VECTOR_ADD_LCANCEL = prove
 (`!x y:real^N.
        integral_vector x ==> (integral_vector(x + y) <=> integral_vector y)`,
  MESON_TAC[INTEGRAL_VECTOR_ADD; INTEGRAL_VECTOR_SUB;
            VECTOR_ARITH `(x + y) - x:real^N = y`]);;
```

### Informal statement
For all vectors $x$ and $y$ in $\mathbb{R}^N$, if $x$ is an integral vector, then the vector sum $x + y$ is an integral vector if and only if $y$ is an integral vector.

Here, a vector is considered an "integral vector" if all of its components are integers.

### Informal proof
The proof follows from the properties of integral vectors and vector arithmetic:

- We already know from `INTEGRAL_VECTOR_ADD` that if both $x$ and $y$ are integral vectors, then their sum $x + y$ is also an integral vector. This gives us the "if" direction.

- For the "only if" direction, we need to show that if $x$ and $x + y$ are integral vectors, then $y$ must be an integral vector.
  - We can express $y$ as $(x + y) - x$ (which is a basic vector identity)
  - By `INTEGRAL_VECTOR_SUB`, if both $(x + y)$ and $x$ are integral vectors, then their difference $(x + y) - x = y$ is also an integral vector.

These arguments together establish the bidirectional implication.

### Mathematical insight
This theorem establishes a cancellation property for integral vectors. It shows that adding an integral vector to both sides of an equation preserves the property of being an integral vector.

This is analogous to the property in integer arithmetic where adding an integer to both sides of an equation preserves integrality. The result is useful for manipulating expressions involving integral vectors, allowing simplification and transformation of statements about integrality.

### Dependencies
- **Theorems**:
  - `INTEGRAL_VECTOR_ADD`: If $x$ and $y$ are integral vectors, then $x + y$ is an integral vector
  - `INTEGRAL_VECTOR_SUB`: If $x$ and $y$ are integral vectors, then $x - y$ is an integral vector
  - `VECTOR_ARITH`: Vector arithmetic identities, specifically $(x + y) - x = y$

- **Definitions**:
  - `integral_vector`: A vector whose components are all integers

### Porting notes
When porting this theorem, you'll need to ensure that:
1. Your system has a definition of integral vectors similar to HOL Light's
2. You have the corresponding theorems about preservation of integrality under vector addition and subtraction
3. Your system has basic vector arithmetic theorems, particularly the identity $(x + y) - x = y$

The proof is straightforward and should translate well to most systems, as it relies on basic algebraic properties.

---

## FINITE_BOUNDED_INTEGER_POINTS

### FINITE_BOUNDED_INTEGER_POINTS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FINITE_BOUNDED_INTEGER_POINTS = prove
 (`!s:real^N->bool. bounded s ==> FINITE {x | x IN s /\ integral_vector x}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL; integral_vector] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                       ==> integer(x$i) /\
                           (a:real^N)$i <= x$i /\ x$i <= (b:real^N)$i}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_INTSEG];
    ASM SET_TAC[]]);;
```

### Informal statement
For any set $s$ in $\mathbb{R}^N$, if $s$ is bounded, then the set of integral vectors in $s$ is finite.

More precisely, for any set $s \subseteq \mathbb{R}^N$, if $s$ is bounded, then the set $\{x \in s \mid x \text{ is an integral vector}\}$ is finite, where $x$ is an integral vector if each component of $x$ is an integer.

### Informal proof
The proof proceeds as follows:

- Since $s$ is bounded, by the theorem `BOUNDED_SUBSET_CLOSED_INTERVAL`, there exist vectors $a, b \in \mathbb{R}^N$ such that $s \subseteq [a,b]$, where $[a,b]$ represents the closed interval $\{x \in \mathbb{R}^N \mid a_i \leq x_i \leq b_i \text{ for all } 1 \leq i \leq N\}$.

- We want to show that the set $\{x \in s \mid x \text{ is an integral vector}\}$ is finite.

- We prove this by showing that it is a subset of a finite set. Specifically, we show it's a subset of:
  $\{x \in \mathbb{R}^N \mid \text{for all } 1 \leq i \leq N, \text{ integer}(x_i) \text{ and } a_i \leq x_i \leq b_i\}$

- This larger set is finite because:
  * For each component index $i$, the set of integers between $a_i$ and $b_i$ (inclusive) is finite.
  * The Cartesian product of finitely many finite sets is finite (theorem `FINITE_CART`).
  
- The subset of a finite set is finite, so our original set $\{x \in s \mid x \text{ is an integral vector}\}$ is finite.

### Mathematical insight
This theorem states an important but intuitively obvious fact: if you take a bounded region of $\mathbb{R}^N$ and look at the points with integer coordinates within that region, there are only finitely many such points.

This result is useful in many areas of mathematics:
- In number theory, it relates to counting lattice points in bounded regions
- In optimization, it's relevant to integer programming problems
- In geometric problems involving integer grids

The proof technique relies on the fundamental property that a bounded interval on the real line contains only finitely many integers, and then extends this to higher dimensions using the Cartesian product structure.

### Dependencies
- **Definitions**: 
  - `integral_vector`: Defines when a vector in $\mathbb{R}^N$ has all integer components
- **Theorems**:
  - `BOUNDED_SUBSET_CLOSED_INTERVAL`: States that any bounded set in $\mathbb{R}^N$ is contained in some closed interval
  - `FINITE_CART`: States that the Cartesian product of finite sets is finite
  - `FINITE_INTSEG`: States that a set of integers in an interval is finite
  - `FINITE_SUBSET`: States that any subset of a finite set is finite

### Porting notes
When porting this theorem:
- Ensure that the target system has a notion of bounded sets in $\mathbb{R}^N$
- Check how the target system represents vectors with integer components
- The theorem relies on properties of intervals in $\mathbb{R}^N$, so the target system should have a corresponding theory
- The final steps of the proof use set reasoning through `SET_TAC[]`, which might need to be expanded into more explicit steps in systems with different automation

---

## FINITE_TRIANGLE_INTEGER_POINTS

### FINITE_TRIANGLE_INTEGER_POINTS
- FINITE_TRIANGLE_INTEGER_POINTS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let FINITE_TRIANGLE_INTEGER_POINTS = prove
 (`!a b c:real^N. FINITE {x | x IN convex hull {a,b,c} /\ integral_vector x}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_BOUNDED_INTEGER_POINTS THEN
  SIMP_TAC[FINITE_IMP_BOUNDED_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY]);;
```

### Informal statement
For any three points $a, b, c \in \mathbb{R}^N$, the set of integer points within their convex hull is finite. Specifically:

$$\forall a,b,c \in \mathbb{R}^N, \quad \text{FINITE}(\{x \in \mathbb{R}^N \mid x \in \text{convex hull}(\{a,b,c\}) \land \text{integral\_vector}(x)\})$$

where $\text{integral\_vector}(x)$ means that all components of the vector $x$ are integers:

$$\text{integral\_vector}(x) \iff \forall i, 1 \leq i \leq \text{dimindex}(N) \Rightarrow \text{integer}(x_i)$$

### Informal proof
The proof follows by applying the theorem `FINITE_BOUNDED_INTEGER_POINTS`, which states that for any bounded set $s$ in $\mathbb{R}^N$, the set of integral vectors in $s$ is finite.

We just need to show that a convex hull of three points is bounded. This is established by applying `FINITE_IMP_BOUNDED_CONVEX_HULL`, which states that the convex hull of a finite set is bounded. The finiteness of the set $\{a,b,c\}$ is shown by applying `FINITE_INSERT` and `FINITE_EMPTY`, which confirms that $\{a,b,c\}$ is indeed a finite set.

### Mathematical insight
This theorem establishes a fundamental property connecting discrete and continuous mathematics: while a triangle (or more precisely, the convex hull of three points) in $\mathbb{R}^N$ contains uncountably many points, only finitely many of these points have integer coordinates.

This result is important in various areas:
- In discrete geometry and combinatorial optimization
- In number theory, particularly in counting lattice points in polytopes
- In computational geometry when dealing with integer programming problems

The result generalizes naturally to any bounded convex polytope, not just triangles, although this theorem specifically addresses the triangle case.

### Dependencies
- **Theorems**:
  - `FINITE_BOUNDED_INTEGER_POINTS`: If a set in $\mathbb{R}^N$ is bounded, then it contains only finitely many integral vectors
  - `FINITE_IMP_BOUNDED_CONVEX_HULL`: The convex hull of a finite set is bounded
  - `FINITE_INSERT`: Adding an element to a finite set produces a finite set
  - `FINITE_EMPTY`: The empty set is finite
- **Definitions**:
  - `integral_vector`: A vector whose components are all integers

### Porting notes
When porting to other proof assistants:
- The proof is straightforward and should translate readily to other systems
- The main requirement is having appropriate libraries for convex geometry and finite sets
- Different systems may have different ways of representing vectors and their components
- The concept of "boundedness" may be defined differently in other systems

---

## LINEAR_INTEGRAL_VECTOR

### Name of formal statement
LINEAR_INTEGRAL_VECTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LINEAR_INTEGRAL_VECTOR = prove
 (`!f:real^N->real^N.
        linear f
        ==> ((!x. integral_vector x ==> integral_vector(f x)) <=>
             (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N)
                    ==> integer(matrix f$i$j)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ONCE_REWRITE_TAC[GSYM(MATCH_MP MATRIX_WORKS th)]) THEN
  ABBREV_TAC `M = matrix(f:real^N->real^N)` THEN
  SIMP_TAC[integral_vector; matrix_vector_mul; LAMBDA_BETA] THEN
  EQ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `basis j:real^N`) THEN
    REWRITE_TAC[GSYM integral_vector; INTEGRAL_VECTOR_STDBASIS] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; COND_RAND; COND_RATOR] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; REAL_MUL_RID];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC INTEGER_SUM THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; IN_NUMSEG]]);;
```

### Informal statement
Let $f: \mathbb{R}^N \to \mathbb{R}^N$ be a linear transformation. Then, 
$f$ maps vectors with integer components to vectors with integer components if and only if all entries of the matrix representation of $f$ are integers.

Formally, if $f$ is linear, then:
$$\forall x. \text{integral\_vector}(x) \Rightarrow \text{integral\_vector}(f(x)) \iff \forall i,j. 1 \leq i \leq \text{dimindex}(:N) \land 1 \leq j \leq \text{dimindex}(:N) \Rightarrow \text{integer}(matrix(f)_{i,j})$$

where $\text{integral\_vector}(x)$ means that all components of vector $x$ are integers.

### Informal proof
Let $f: \mathbb{R}^N \to \mathbb{R}^N$ be a linear transformation.

First, we use the fact that $f(x) = M \cdot x$ where $M$ is the matrix representation of $f$. Then we use the definition of integral vector to reformulate the problem in terms of components.

The equivalence proof proceeds in both directions:

* ($\Rightarrow$) Assume that $f$ preserves integral vectors. We need to show all matrix entries are integers.
  * Take arbitrary indices $i, j$ with $1 \leq i \leq \text{dimindex}(:N)$ and $1 \leq j \leq \text{dimindex}(:N)$.
  * Consider the standard basis vector $e_j$ (represented as `basis j` in HOL Light).
  * Since $e_j$ has integer components (by theorem `INTEGRAL_VECTOR_STDBASIS`), $f(e_j)$ must have integer components by our assumption.
  * The $i$-th component of $f(e_j)$ is exactly $M_{i,j}$ since $f(e_j) = M \cdot e_j$.
  * This follows because the sum in the matrix-vector multiplication collapses to a single term when multiplying by a standard basis vector.
  * Therefore, $M_{i,j}$ is an integer.

* ($\Leftarrow$) Assume all entries $M_{i,j}$ of the matrix are integers. We need to show $f$ preserves integral vectors.
  * Let $x$ be any integral vector and $i$ be a valid index.
  * The $i$-th component of $f(x)$ is $\sum_{j=1}^N M_{i,j} \cdot x_j$.
  * Since each $M_{i,j}$ and each $x_j$ are integers, each product $M_{i,j} \cdot x_j$ is an integer.
  * By the theorem `INTEGER_SUM`, the sum of integers is an integer.
  * Therefore, each component of $f(x)$ is an integer, making $f(x)$ an integral vector.

### Mathematical insight
This theorem provides a simple characterization of linear transformations that preserve the integer lattice in $\mathbb{R}^N$. Such transformations are precisely those with integer matrices. 

This is a fundamental result in lattice theory and has applications in:
- Number theory when studying integral lattices
- Crystallography where integer lattice transformations represent symmetries
- Computer science applications like lattice-based cryptography

The result is intuitive: since the standard basis vectors span the integer lattice, it's sufficient and necessary to check that the images of these basis vectors have integer coordinates, which directly corresponds to the matrix entries being integers.

### Dependencies
#### Theorems
- `INTEGRAL_VECTOR_STDBASIS`: The standard basis vectors in $\mathbb{R}^N$ have integer components
- `MATRIX_WORKS`: Connects a linear transformation with its matrix representation
- `INTEGER_SUM`: The sum of integers is an integer
- `BASIS_COMPONENT`: Describes the components of a standard basis vector

#### Definitions
- `integral_vector`: A vector where all components are integers

### Porting notes
When porting this theorem:
1. Ensure that the matrix representation of a linear transformation follows the same convention as in HOL Light.
2. Make sure the representation of the standard basis is consistent.
3. The proof relies on the fact that applying a linear transformation to a basis vector extracts a column of the matrix - this should translate directly to other systems.

---

## INTEGRAL_BASIS_UNIMODULAR

### INTEGRAL_BASIS_UNIMODULAR
- `INTEGRAL_BASIS_UNIMODULAR`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let INTEGRAL_BASIS_UNIMODULAR = prove
 (`!f:real^N->real^N.
        linear f /\ IMAGE f integral_vector = integral_vector
        ==> abs(det(matrix f)) = &1`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN REWRITE_TAC[IN] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(f:real^N->real^N)$i$j)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[GSYM LINEAR_INTEGRAL_VECTOR]; ALL_TAC] THEN
  SUBGOAL_THEN
    `?g:real^N->real^N. linear g /\ (!x. g(f x) = x) /\ (!y. f(g y) = y)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]; ALL_TAC] THEN
    SUBGOAL_THEN `!y. y:real^N IN span(IMAGE f (:real^N))` MP_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[SPAN_LINEAR_IMAGE; SPAN_UNIV] THEN SET_TAC[]] THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC SPAN_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
    MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    ASM_MESON_TAC[INTEGRAL_VECTOR_STDBASIS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. 1 <= i /\ i <= dimindex(:N) /\
          1 <= j /\ j <= dimindex(:N)
          ==> integer(matrix(g:real^N->real^N)$i$j)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LINEAR_INTEGRAL_VECTOR] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `det(matrix(f:real^N->real^N)) * det(matrix(g:real^N->real^N)) =
    det(matrix(I:real^N->real^N))`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM DET_MUL; GSYM MATRIX_COMPOSE] THEN
    REPEAT AP_TERM_TAC THEN ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `abs:real->real`) THEN
  REWRITE_TAC[MATRIX_I; DET_I; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[INTEGER_DET; INTEGER_ABS_MUL_EQ_1]);;
```

### Informal statement
For any linear transformation $f: \mathbb{R}^N \to \mathbb{R}^N$, if $f$ maps the set of vectors with integer coordinates precisely to itself (i.e., $f(\mathbb{Z}^N) = \mathbb{Z}^N$), then the absolute value of the determinant of the matrix representation of $f$ is equal to 1, i.e., $|\det(f)| = 1$.

### Informal proof
We need to prove that for a linear transformation $f: \mathbb{R}^N \to \mathbb{R}^N$ where $f(\mathbb{Z}^N) = \mathbb{Z}^N$, we have $|\det(f)| = 1$.

The proof proceeds as follows:

- First, we reformulate $f(\mathbb{Z}^N) = \mathbb{Z}^N$ as the combination of two subset inclusions: $f(\mathbb{Z}^N) \subseteq \mathbb{Z}^N$ and $\mathbb{Z}^N \subseteq f(\mathbb{Z}^N)$.

- From $f(\mathbb{Z}^N) \subseteq \mathbb{Z}^N$, we deduce that all matrix entries of $f$ are integers using `LINEAR_INTEGRAL_VECTOR`. This theorem states that a linear map preserves integral vectors if and only if its matrix consists entirely of integer entries.

- Next, we show that there exists a linear transformation $g: \mathbb{R}^N \to \mathbb{R}^N$ that is the inverse of $f$, i.e., $g \circ f = f \circ g = I$ (identity function).
  - This follows from the fact that $f$ is bijective (both injective and surjective).
  - Surjectivity comes directly from the assumption $\mathbb{Z}^N \subseteq f(\mathbb{Z}^N)$.
  - For a linear transformation on a finite-dimensional vector space, surjectivity implies injectivity.
  - We also prove that $g$ preserves integral vectors.

- Similarly, we show that all matrix entries of $g$ are integers, again using `LINEAR_INTEGRAL_VECTOR`.

- Since $g \circ f = I$, we have $\det(g) \cdot \det(f) = \det(I) = 1$.

- Taking the absolute value, we get $|\det(g)| \cdot |\det(f)| = 1$.

- Since both matrices have integer entries, their determinants are integers. The product of absolute values of integers equals 1 only when both absolute values are 1.

- Therefore, $|\det(f)| = 1$.

### Mathematical insight
This theorem establishes an important characterization of linear transformations that map the integer lattice to itself. Such transformations are precisely the ones represented by matrices with integer entries having determinants of ±1, also known as unimodular matrices.

In number theory and lattice theory, these transformations are crucial because:

1. They represent the automorphisms of the integer lattice $\mathbb{Z}^N$.
2. They preserve volume (up to sign) in $\mathbb{R}^N$.
3. They correspond to "basis changes" for integral bases of $\mathbb{Z}$-modules.

This theorem connects linear algebra (determinants) with number theory (integer lattices) and is foundational in areas like algebraic number theory, crystallography, and geometry of numbers.

### Dependencies
- Definitions:
  - `integral_vector`: Defines a vector in $\mathbb{R}^N$ to have integer coordinates if all its components are integers.

- Theorems:
  - `INTEGRAL_VECTOR_STDBASIS`: Proves that the standard basis vectors have integer coordinates.
  - `LINEAR_INTEGRAL_VECTOR`: Shows that a linear transformation preserves vectors with integer coordinates if and only if all entries in its matrix representation are integers.

### Porting notes
When porting this theorem:
- Ensure the definition of `integral_vector` aligns with your system's representation of vectors with integer coordinates.
- You may need to establish that the matrix representation of a linear map has integer entries if and only if it maps integer vectors to integer vectors.
- The proof relies on the fact that surjectivity implies injectivity for linear maps in finite dimensions, which might need to be established separately.
- The manipulation of determinants and their properties (especially multiplicativity of determinants) is crucial for the proof.

---

## PICK_ELEMENTARY_TRIANGLE_0

### PICK_ELEMENTARY_TRIANGLE_0
- PICK_ELEMENTARY_TRIANGLE_0

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PICK_ELEMENTARY_TRIANGLE_0 = prove
 (`!a b:real^2.
        {x | x IN convex hull {vec 0,a,b} /\ integral_vector x} = {vec 0,a,b}
        ==> measure(convex hull {vec 0,a,b}) =
               if collinear {vec 0,a,b} then &0 else &1 / &2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; COLLINEAR_IMP_NEGLIGIBLE;
               COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
  POP_ASSUM MP_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^2 = vec 0`; `b:real^2 = vec 0`; `a:real^2 = b`] THEN
  DISCH_TAC THEN SUBGOAL_THEN `independent {a:real^2,b}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{vec 0:real^2, a, b}` THEN
    REWRITE_TAC[independent; CONTRAPOS_THM] THEN
    REWRITE_TAC[dependent; EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{c,a,b} = {c,b,a}`]; ALL_TAC] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `a IN s ==> s SUBSET t ==> a IN t`)) THEN
    MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `span{a,b} = (:real^2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^2)`; `{a:real^2,b}`] CARD_EQ_DIM) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; SUBSET; EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; DIM_UNIV; DIMINDEX_2; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_INSERT;
              FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\x:real^2. transp(vector[a;b]:real^2^2) ** x`
        INTEGRAL_BASIS_UNIMODULAR) THEN
  REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[DET_2; MEASURE_TRIANGLE; VECTOR_2; DET_TRANSP; VEC_COMPONENT] THEN
  ANTS_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN
    SIMP_TAC[LINEAR_INTEGRAL_VECTOR; MATRIX_VECTOR_MUL_LINEAR; LAMBDA_BETA;
             MATRIX_OF_MATRIX_VECTOR_MUL; transp; DIMINDEX_2; ARITH] THEN
    MAP_EVERY UNDISCH_TAC
     [`integral_vector(a:real^2)`; `integral_vector(b:real^2)`] THEN
    REWRITE_TAC[integral_vector; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP; FORALL_2; DIMINDEX_2; VECTOR_2] THEN
    REWRITE_TAC[CONJ_ACI];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN REWRITE_TAC[IN] THEN
  X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_VECTOR_2] THEN
  REWRITE_TAC[MATRIX_VECTOR_COLUMN; TRANSP_TRANSP] THEN
  REWRITE_TAC[DIMINDEX_2; VSUM_2; VECTOR_2; integral_vector; FORALL_2] THEN
  SUBGOAL_THEN `(x:real^2) IN span{a,b}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[SPAN_2; IN_UNIV; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real` THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `frac u % a + frac v % b:real^2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(&1 - frac u) % a + (&1 - frac v) % b:real^2`) THEN
  MATCH_MP_TAC(TAUT
   `b' /\ (b' ==> b) /\ (a \/ a') /\ (c \/ c' ==> x)
    ==> (a /\ b ==> c) ==> (a' /\ b' ==> c') ==> x`) THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `integral_vector(floor u % a + floor v % b:real^2)`
    MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`integral_vector(a:real^2)`; `integral_vector(b:real^2)`] THEN
      SIMP_TAC[integral_vector; DIMINDEX_2; FORALL_2;
               VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[FLOOR; INTEGER_CLOSED];
      UNDISCH_TAC `integral_vector(x:real^2)` THEN REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRAL_VECTOR_SUB) THEN
      ASM_REWRITE_TAC[VECTOR_ARITH
       `(x % a + y % b) - (u % a + v % b) = (x - u) % a + (y - v) % b`] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[REAL_ARITH `u - x:real = y <=> u = x + y`] THEN
      REWRITE_TAC[GSYM FLOOR_FRAC]];
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + (&1 - v) % b = (a + b) - (u % a + v % b)`] THEN
    ASM_SIMP_TAC[INTEGRAL_VECTOR_ADD; INTEGRAL_VECTOR_SUB];
    REWRITE_TAC[CONVEX_HULL_3_0; IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `&0 <= frac u /\ &0 <= frac v /\ frac u + frac v <= &1 \/
      &0 <= &1 - frac u /\ &0 <= &1 - frac v /\
      (&1 - frac u) + (&1 - frac v) <= &1`
    MP_TAC THENL
     [MP_TAC(SPEC `u:real` FLOOR_FRAC) THEN
      MP_TAC(SPEC `v:real` FLOOR_FRAC) THEN REAL_ARITH_TAC;
      MESON_TAC[]];
    REWRITE_TAC
     [VECTOR_ARITH `x % a + y % b = a <=> (x - &1) % a + y % b = vec 0`;
      VECTOR_ARITH `x % a + y % b = b <=> x % a + (y - &1) % b = vec 0`] THEN
    ASM_SIMP_TAC[INDEPENDENT_2; GSYM REAL_FRAC_EQ_0] THEN
    MP_TAC(SPEC `u:real` FLOOR_FRAC) THEN
    MP_TAC(SPEC `v:real` FLOOR_FRAC) THEN REAL_ARITH_TAC]);;
```

### Informal statement
The theorem states that for vectors $a, b \in \mathbb{R}^2$, if the set of integral points in the convex hull of $\{0, a, b\}$ equals exactly $\{0, a, b\}$, then:

$$\text{measure}(\text{convex hull} \{0, a, b\}) = 
\begin{cases}
0, & \text{if } \{0, a, b\} \text{ are collinear} \\
\frac{1}{2}, & \text{otherwise}
\end{cases}$$

Here, $\text{integral\_vector}$ refers to a vector with integer coordinates.

### Informal proof
This is a proof of Pick's theorem for the special case of an elementary triangle (one with exactly 3 integral points - its vertices).

The proof proceeds as follows:

* First, we handle the degenerate case: If the points $\{0, a, b\}$ are collinear, then the measure of their convex hull is 0, which follows from the fact that collinear sets are negligible.

* For the non-degenerate case, we first eliminate trivial cases where any two points might be equal.

* We establish that $a$ and $b$ are linearly independent. This follows from the fact that $\{0, a, b\}$ are not collinear.

* We show that $\text{span}\{a, b\} = \mathbb{R}^2$, using the fact that the dimension of $\mathbb{R}^2$ is 2 and we have 2 linearly independent vectors.

* The key step uses the theorem `INTEGRAL_BASIS_UNIMODULAR`: we construct the linear transformation represented by the matrix $[a | b]^T$ (the transpose of the matrix with columns $a$ and $b$).

* Since $a$ and $b$ are integral vectors (have integer coordinates), this transformation maps integral vectors to integral vectors.

* From the assumption that the only integral points in the convex hull are $\{0, a, b\}$, we deduce that this linear transformation has determinant with absolute value 1.

* The area of the triangle equals $\frac{|det([a|b]^T)|}{2} = \frac{1}{2}$, which completes the proof.

### Mathematical insight
This theorem establishes a special case of Pick's theorem for triangles that have exactly three integral points (the vertices). Such triangles are called "elementary" or "primitive" triangles. Pick's theorem generally relates the area of a polygon with integer vertex coordinates to the number of integral points inside and on the boundary of the polygon.

The result shows that all elementary triangles in the plane have area $\frac{1}{2}$ (if non-degenerate), regardless of their shape or size. This is a fundamental insight into the geometry of integral points in the plane.

The proof relies on the connection between the area of the triangle, the determinant of the matrix formed by its sides, and the property that this matrix represents a unimodular transformation (a linear transformation that preserves the lattice of integral points).

### Dependencies
- **Theorems**:
  - `MEASURE_EQ_0`: If a set is negligible, then its measure is 0
  - `MEASURE_TRIANGLE`: Formula for the area of a triangle in terms of coordinates
  - `COLLINEAR_IMP_NEGLIGIBLE`: Collinear sets are negligible
  - `CONVEX_HULL_3_0`: Representation of the convex hull of {0,a,b}
  - `INTEGRAL_VECTOR_ADD`: Sum of integral vectors is integral
  - `INTEGRAL_VECTOR_SUB`: Difference of integral vectors is integral
  - `LINEAR_INTEGRAL_VECTOR`: Characterization of linear maps preserving integral vectors
  - `INTEGRAL_BASIS_UNIMODULAR`: Linear maps preserving integral vectors have determinant with absolute value 1

- **Definitions**:
  - `measure`: The measure of a set
  - `integral_vector`: A vector with integer coordinates

### Porting notes
When porting this theorem:
1. The definition of `integral_vector` is fundamental - it refers to vectors with integer coordinates.
2. Care should be taken with the matrix representation of the linear transformation, particularly the transpose operation.
3. Systems with different approaches to vector components may require adjustments to the component-wise arguments.
4. The theorem relies on determinant calculations for measuring area, which is a standard approach but implementation details may vary across systems.

---

## PICK_ELEMENTARY_TRIANGLE

### PICK_ELEMENTARY_TRIANGLE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PICK_ELEMENTARY_TRIANGLE = prove
 (`!a b c:real^2.
        {x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}
        ==> measure(convex hull {a,b,c}) =
               if collinear {a,b,c} then &0 else &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `s = t ==> (!x. x IN s <=> x IN t) /\ s = t`)) THEN
  REWRITE_TAC[IMP_CONJ] THEN DISCH_THEN(MP_TAC o SPEC `a:real^2`) THEN
  REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN
  GEOM_ORIGIN_TAC `a:real^2`THEN
  SIMP_TAC[INTEGRAL_VECTOR_ADD_LCANCEL; VECTOR_ADD_RID] THEN
  REWRITE_TAC[PICK_ELEMENTARY_TRIANGLE_0]);;
```

### Informal statement
Let $a$, $b$, and $c$ be points in $\mathbb{R}^2$. If the set of integer points in the convex hull of $\{a,b,c\}$ is exactly $\{a,b,c\}$, then the measure (area) of this convex hull is:
$$\text{measure}(\text{convex hull}(\{a,b,c\})) = \begin{cases}
0 & \text{if } \{a,b,c\} \text{ is collinear} \\
\frac{1}{2} & \text{otherwise}
\end{cases}$$

Here, a point is considered an "integer point" (i.e., satisfies `integral_vector`) if all of its coordinates are integers.

### Informal proof
The proof proceeds as follows:

* First, apply a technique to translate the problem to the origin. After establishing that the hypothesis implies $a$, $b$, and $c$ are integer points, we can shift everything by $-a$, effectively making $a$ the origin (zero vector).

* After this translation, we have a new triangle with vertices $\{0, b-a, c-a\}$.

* The key insight is that this transformation preserves the property that the only integer points in the convex hull are exactly the vertices.

* When applying the vector addition property of integer vectors (`INTEGRAL_VECTOR_ADD_LCANCEL`), we show that the original condition transforms properly to the new origin-containing triangle.

* Finally, we apply the theorem `PICK_ELEMENTARY_TRIANGLE_0`, which handles the special case of triangles with one vertex at the origin.

* This theorem states that when the only integer points in a triangle with one vertex at the origin are exactly the vertices themselves, the area is either 0 (if the points are collinear) or 1/2 (otherwise).

### Mathematical insight
This theorem is a special case of Pick's theorem, which relates the area of a polygon with integer vertices to the number of integer points it contains. Specifically, this handles the case of a triangle with exactly 3 integer points (its vertices), showing that such triangles always have area 1/2 unless they are degenerate (collinear).

The theorem demonstrates that "primitive triangles" (triangles with integer vertices and no other integer points inside or on their boundary except the vertices) have a constant area of 1/2 square units. This is a fundamental result in discrete geometry and has applications in number theory and computational geometry.

### Dependencies
- **Theorems**
  - `INTEGRAL_VECTOR_ADD_LCANCEL`: If x is an integer vector, then x+y is an integer vector if and only if y is an integer vector
  - `PICK_ELEMENTARY_TRIANGLE_0`: The specialized case where one vertex is at the origin
- **Definitions**
  - `measure`: The Lebesgue measure of a set
  - `integral_vector`: A vector whose components are all integers

### Porting notes
When porting this theorem to another system:
1. Ensure that the target system has a well-defined notion of convex hull and Lebesgue measure
2. The proof relies on a technique called `GEOM_ORIGIN_TAC` which translates geometric problems to the origin - this might need a custom implementation in other systems
3. The underlying mathematical concept (Pick's theorem) is standard, but the formalization approach may differ between systems

---

## PICK_TRIANGLE_FLAT

### Name of formal statement
PICK_TRIANGLE_FLAT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PICK_TRIANGLE_FLAT = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c /\
        c IN segment[a,b]
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  SUBGOAL_THEN `convex hull {a:real^2,b,c} = segment[a,b]` SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC CONVEX_HULLS_EQ THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[ENDS_IN_SEGMENT; HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `measure(segment[a:real^2,b]) = &0` SUBST1_TAC THENL
   [MATCH_MP_TAC MEASURE_EQ_0 THEN
    MATCH_MP_TAC COLLINEAR_IMP_NEGLIGIBLE THEN
    REWRITE_TAC[COLLINEAR_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `&0 = c - (a + b + c) / &2 + &1 / &2 <=> a + b = c + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  SUBGOAL_THEN
   `segment[a:real^2,b] = segment[b,c] UNION segment[a,c]`
  SUBST1_TAC THENL [ASM_MESON_TAC[SEGMENT_SYM; UNION_SEGMENT]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
    `{x | x IN (s UNION t) /\ P x} =
     {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  SIMP_TAC[CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `z:num <= x /\ z = 1 ==> x + y = (x + y) - z + 1`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN SET_TAC[];
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
                          {x | x IN (s INTER t) /\ P x}`] THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment[a,c] = {c}`
    SUBST1_TAC THENL [ASM_MESON_TAC[INTER_SEGMENT; SEGMENT_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `{x:real^2 | x IN {c} /\ integral_vector x} = {c}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_EMPTY; ARITH; NOT_IN_EMPTY]]);;
```

### Informal statement
For any points $a$, $b$, and $c$ in $\mathbb{R}^2$, if all three points have integer coordinates (i.e., $a$, $b$, and $c$ are integral vectors) and $c$ lies on the line segment between $a$ and $b$ (i.e., $c \in \text{segment}[a,b]$), then:

$$\text{measure}(\text{convex hull }\{a,b,c\}) = \#(\text{convex hull }\{a,b,c\} \cap \mathbb{Z}^2) - \frac{\#(\text{convex hull }\{b,c\} \cap \mathbb{Z}^2) + \#(\text{convex hull }\{a,c\} \cap \mathbb{Z}^2) + \#(\text{convex hull }\{a,b\} \cap \mathbb{Z}^2)}{2} + \frac{1}{2}$$

Where $\#(S)$ denotes the cardinality of set $S$, and $\mathbb{Z}^2$ represents the set of points with integer coordinates.

### Informal proof
This theorem is a degenerate case of Pick's theorem for a "flat triangle" (where the three points are collinear).

1. First, we note that since $c$ lies on the segment between $a$ and $b$, the convex hull of $\{a,b,c\}$ is just the segment $[a,b]$:
   - We have $\text{convex hull }\{a,b,c\} = \text{segment}[a,b]$ since $c \in \text{segment}[a,b]$

2. The measure (area) of a line segment is zero:
   - By `COLLINEAR_IMP_NEGLIGIBLE`, any collinear set in $\mathbb{R}^2$ is negligible
   - By `MEASURE_EQ_0`, any negligible set has measure zero
   - Since line segments are collinear, $\text{measure}(\text{segment}[a,b]) = 0$

3. We rewrite the segment $[a,b]$ as the union of segments $[b,c]$ and $[a,c]$:
   - $\text{segment}[a,b] = \text{segment}[b,c] \cup \text{segment}[a,c]$

4. For the counting of integer points:
   - The set of integer points in the union is the union of integer points in each segment
   - The intersection of the two segments $[b,c]$ and $[a,c]$ is just the point $\{c\}$
   - Since $c$ is an integer point (by assumption), the intersection contains exactly one integer point

5. Using these facts and properties of cardinality of unions:
   - $\#(\text{segment}[a,b] \cap \mathbb{Z}^2) = \#(\text{segment}[b,c] \cap \mathbb{Z}^2) + \#(\text{segment}[a,c] \cap \mathbb{Z}^2) - 1$
   - This gives us the equation: $A + B = (A + B) - 1 + 1$ where $A$ and $B$ are the number of integer points in the two segments

6. Substituting this into the original formula and simplifying:
   - The left side is $0$ (measure of segment $[a,b]$)
   - The right side simplifies to $0$ when we make the appropriate substitutions

This verifies that the formula holds trivially in this degenerate case.

### Mathematical insight
This theorem addresses a degenerate case of Pick's theorem for a "flat triangle" - where the points are collinear making the triangle have zero area. Pick's theorem is a famous result that relates the area of a simple polygon with integer vertices to the number of integer points inside and on the boundary of the polygon.

In the general case, Pick's theorem states that the area of a simple polygon with integer vertices is:
$$A = I + \frac{B}{2} - 1$$
where $I$ is the number of integer points in the interior and $B$ is the number of integer points on the boundary.

This specific theorem shows that the formula holds even in the degenerate case where the "triangle" is actually a line segment. The proof confirms that both sides of the equation equal zero, as expected since a line segment has zero area.

### Dependencies
- **Theorems**:
  - `MEASURE_EQ_0`: States that if a set is negligible, then its measure is 0
  - `COLLINEAR_IMP_NEGLIGIBLE`: States that any collinear set in $\mathbb{R}^2$ is negligible
  - `FINITE_BOUNDED_INTEGER_POINTS`: States that for any bounded set in $\mathbb{R}^N$, the set of integral vectors in that set is finite

- **Definitions**:
  - `measure`: Defines the measure (area) of a set
  - `integral_vector`: Defines a vector with integer components

### Porting notes
When porting this theorem:
1. Ensure that the target system has appropriate handling for degenerate cases in geometric theorems
2. The notion of "measure" should be properly defined for 2D sets
3. The concept of "integral vector" (vector with integer components) should be defined
4. The proof relies heavily on set manipulation and cardinality properties, so ensure that these basic set operations are available in the target system

---

## PICK_TRIANGLE_ALT

### PICK_TRIANGLE_ALT
- PICK_TRIANGLE_ALT

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PICK_TRIANGLE_ALT = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`,
  let tac a bc =
    MATCH_MP_TAC CARD_PSUBSET THEN
    REWRITE_TAC[FINITE_TRIANGLE_INTEGER_POINTS] THEN
    REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}`) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; HULL_INC];
      DISCH_TAC] THEN
    SUBGOAL_THEN(subst[bc,`bc:real^2->bool`]
        `convex hull {a:real^2,b,c} = convex hull bc`)
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONVEX_HULLS_EQ THEN
      ASM_SIMP_TAC[HULL_INC; IN_INSERT; INSERT_SUBSET; EMPTY_SUBSET] THEN
      SUBGOAL_THEN(subst [a,`x:real^2`] `x IN convex hull {a:real^2,b,c}`)
      MP_TAC THENL
       [SIMP_TAC[HULL_INC; IN_INSERT]; ASM SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`{a:real^2,b,c}`; a]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] in
  REPEAT GEN_TAC THEN
  WF_INDUCT_TAC `CARD {x:real^2 | x IN convex hull {a,b,c} /\
                                  integral_vector x}` THEN
  ASM_CASES_TAC `collinear{a:real^2,b,c}` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_BETWEEN_CASES]) THEN
    REWRITE_TAC[BETWEEN_IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `a:real^2`] PICK_TRIANGLE_FLAT);
      MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `b:real^2`] PICK_TRIANGLE_FLAT);
      MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`]
       PICK_TRIANGLE_FLAT)] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
     REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
     REWRITE_TAC[INSERT_AC; REAL_ADD_AC]);
    ALL_TAC] THEN
  UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
  MAP_EVERY
   (fun t -> ASM_CASES_TAC t THENL
     [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC])
   [`a:real^2 = b`; `a:real^2 = c`; `b:real^2 = c`] THEN
  DISCH_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `{x:real^2 | x IN convex hull {a, b, c} /\ integral_vector x} =
    {a,b,c}`
  THENL
   [ASM_SIMP_TAC[PICK_ELEMENTARY_TRIANGLE] THEN
    SUBGOAL_THEN
     `{x | x IN convex hull {b,c} /\ integral_vector x} = {b,c} /\
      {x | x IN convex hull {a,c} /\ integral_vector x} = {a,c} /\
      {x | x IN convex hull {a,b} /\ integral_vector x} = {a:real^2,b}`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [REPEAT CONJ_TAC THEN
      (FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `{x | x IN cs /\ P x} = s
         ==> t SUBSET s /\ t SUBSET ct /\ ct SUBSET cs /\
                (s DIFF t) INTER ct = {}
             ==> {x | x IN ct /\ P x} = t`)) THEN
       REPEAT CONJ_TAC THENL
        [SET_TAC[];
         MATCH_ACCEPT_TAC HULL_SUBSET;
         MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
         ASM_REWRITE_TAC[INSERT_DIFF; IN_INSERT; NOT_IN_EMPTY; EMPTY_DIFF] THEN
         MATCH_MP_TAC(SET_RULE `~(x IN s) ==> {x} INTER s = {}`) THEN
         REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; GSYM BETWEEN_IN_SEGMENT] THEN
         DISCH_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
         UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[INSERT_AC]]);
       SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
       ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
       CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^2. d IN convex hull {a, b, c} /\ integral_vector d /\
               ~(d = a) /\ ~(d = b) /\ ~(d = c)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `~(s = t) ==> t SUBSET s ==> ?d. d IN s /\ ~(d IN t)`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_INSERT; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM; GSYM CONJ_ASSOC] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [COLLINEAR_3_EQ_AFFINE_DEPENDENT]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`measure:(real^2->bool)->real`;
    `a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
   TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
  SIMP_TAC[MEASURE_UNION; MEASURABLE_COMPACT] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[MEASURE_CONVEX_HULL_2_TRIVIAL; REAL_ADD_RID; REAL_SUB_RZERO] THEN
  MP_TAC(ISPECL
   [`\s. &(CARD {x:real^2 | x IN s /\ integral_vector x})`;
    `a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
   TRIANGLE_ADDITIVE_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[SET_RULE `{x | x IN (s UNION t) /\ P x} =
                          {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`;
                SET_RULE `{x | x IN (s INTER t) /\ P x} =
                          {x | x IN s /\ P x} INTER {x | x IN t /\ P x}`] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `x:real = y + z - w <=> x + w = y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x:num = (y + z) - w /\ w <= z ==> x + w = y + z`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_UNION_GEN;
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[INTER_SUBSET]] THEN
    ASM_SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS; COMPACT_IMP_BOUNDED];
    DISCH_THEN SUBST1_TAC] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`] th) THEN
   MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `d:real^2`] th) THEN
   MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `d:real^2`] th)) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [tac `a:real^2` `{b:real^2,c,d}`; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [tac `b:real^2` `{a:real^2,c,d}`; DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [tac `c:real^2` `{a:real^2,b,d}`; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `{x:real^2 | x IN convex hull {d} /\ integral_vector x} = {d}`
  SUBST1_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_SING] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
  REWRITE_TAC[INSERT_AC] THEN REAL_ARITH_TAC);;
```

### Informal statement
This theorem is a statement of Pick's formula for the area of a triangle in the plane whose vertices have integer coordinates. Specifically, for a triangle in $\mathbb{R}^2$ with vertices $a$, $b$, and $c$ that have integer coordinates, the area of the triangle (denoted by the measure of its convex hull) is given by:

$$\text{measure}(\text{conv}(\{a,b,c\})) = I - \frac{B}{2} + \frac{1}{2}$$

where:
- $I = \text{CARD}\{x \in \text{conv}(\{a,b,c\}) \mid x \text{ has integer coordinates}\}$ is the number of integer points in the triangle (including its interior and boundary)
- $B = \text{CARD}\{x \in \text{conv}(\{b,c\}) \mid x \text{ has integer coordinates}\} + \text{CARD}\{x \in \text{conv}(\{a,c\}) \mid x \text{ has integer coordinates}\} + \text{CARD}\{x \in \text{conv}(\{a,b\}) \mid x \text{ has integer coordinates}\}$ is the sum of integer points on all three sides of the triangle

### Informal proof
This proof uses induction on the number of integer points in the triangle. Let's summarize the key steps:

* The proof uses well-founded induction on the number of integer points in the triangle.

* **Base case**: When the triangle has only its three vertices as integer points (i.e., $\{x \in \text{conv}(\{a,b,c\}) \mid x \text{ has integer coordinates}\} = \{a,b,c\}$):
  - If the points are collinear, the area is 0.
  - If the points are not collinear, the area is $\frac{1}{2}$.
  - In both cases, the formula holds.

* **Collinear case**: If the points $a$, $b$, and $c$ are collinear, then one point lies on the line segment between the other two. The proof applies `PICK_TRIANGLE_FLAT` which handles this degenerate case.

* **Inductive case**: If the triangle contains an integer point $d$ that is not one of the vertices:
  1. The triangle is decomposed into three smaller triangles: $\{a,b,d\}$, $\{a,c,d\}$, and $\{b,c,d\}$.
  2. By induction, Pick's formula holds for each of these smaller triangles.
  3. The proof uses `TRIANGLE_ADDITIVE_DECOMPOSITION` to relate the area of the original triangle to the areas of the smaller triangles.
  4. It also relates the count of integer points in the original triangle to the counts in the smaller triangles.
  5. By combining these relationships and using the inductive hypotheses, the proof establishes that Pick's formula holds for the original triangle.

The theorem uses careful manipulation of set operations and cardinalities to handle the counting of integer points, particularly when triangles share boundaries.

### Mathematical insight
Pick's theorem provides a remarkably simple formula to calculate the area of a polygon with integer vertices in terms of the number of integer points it contains. The version proven here specifically addresses triangles, which are the fundamental building blocks for more complex polygons.

The theorem is significant because:
1. It connects discrete geometry (counting integer points) with continuous geometry (area).
2. It provides an efficient method to compute areas of integer polygons.
3. It has applications in computer graphics, computational geometry, and number theory.

The formula expresses the area as $I - \frac{B}{2} + \frac{1}{2}$, where $I$ is the number of integer points inside or on the boundary, and $B$ is the number of integer points on the boundary. For a triangle, the boundary points are enumerated by counting points on each side.

### Dependencies
- Geometric theorems:
  - `MEASURE_UNION`: Measure of union of sets
  - `MEASURABLE_COMPACT`: All compact sets are measurable
  - `EXTREME_POINT_OF_CONVEX_HULL`: Extreme points of a convex hull
  - `EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT`: Characterization of extreme points
  - `MEASURE_CONVEX_HULL_2_TRIVIAL`: Measure of convex hulls of 1-2 points is zero
  - `TRIANGLE_ADDITIVE_DECOMPOSITION`: Decomposition formula for triangles
  - `FINITE_BOUNDED_INTEGER_POINTS`: Finiteness of integer points in bounded sets
  - `FINITE_TRIANGLE_INTEGER_POINTS`: Finiteness of integer points in a triangle
  - `PICK_ELEMENTARY_TRIANGLE`: Special case for triangles with exactly three integer points
  - `PICK_TRIANGLE_FLAT`: Pick's formula for collinear (flat) triangles

- Definitions:
  - `measure`: Measure of a set
  - `integral_vector`: Vector with integer coordinates

### Porting notes
When porting this theorem:
1. Ensure your system has a well-defined notion of convex hull and measure.
2. The proof relies heavily on set operations and cardinality of sets - make sure these are well-supported.
3. The induction principle used here is well-founded induction on the number of integer points. Many systems have different ways of expressing this.
4. The decomposition of a triangle into smaller triangles is crucial - understand how this works in your system.
5. You'll need to handle special cases (collinear points, triangles with only vertex points) separately.

---

## PICK_TRIANGLE

### PICK_TRIANGLE
- pick_triangle

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PICK_TRIANGLE = prove
 (`!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
                if collinear {a,b,c} then &0
                else &(CARD {x | x IN interior(convex hull {a,b,c}) /\
                                 integral_vector x}) +
                     &(CARD {x | x IN frontier(convex hull {a,b,c}) /\
                                 integral_vector x}) / &2 - &1`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; COLLINEAR_IMP_NEGLIGIBLE;
               COLLINEAR_CONVEX_HULL_COLLINEAR] THEN
  ASM_SIMP_TAC[PICK_TRIANGLE_ALT] THEN
  REWRITE_TAC[INTERIOR_OF_TRIANGLE; FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN (s DIFF t) /\ P x} =
    {x | x IN s /\ P x} DIFF {x | x IN t /\ P x}`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i + c = s /\ ccc = c + &3
    ==> s - ccc / &2 + &1 / &2 = i + c / &2 - &1`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE `y:num <= x /\ x - y = z ==> z + y = x`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET; MATCH_MP_TAC(GSYM CARD_DIFF)] THEN
    ASM_SIMP_TAC[FINITE_BOUNDED_INTEGER_POINTS;
      FINITE_IMP_BOUNDED_CONVEX_HULL; FINITE_INSERT; FINITE_EMPTY] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t ==> {x | x IN s /\ P x} SUBSET {x | x IN t /\ P x}`) THEN
    REWRITE_TAC[UNION_SUBSET; SEGMENT_CONVEX_HULL] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    REWRITE_TAC[SET_RULE
     `{x | x IN (s UNION t) /\ P x} =
      {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
    SIMP_TAC[CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS;
      FINITE_INTER; FINITE_UNION; BOUNDED_SEGMENT; UNION_OVER_INTER] THEN
    REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
      {x | x IN (s INTER t) /\ P x}`] THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment [c,a] = {c} /\
      segment[a,b] INTER segment [b,c] = {b} /\
      segment[a,b] INTER segment [c,a] = {a}`
    (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[INTER_SEGMENT; SEGMENT_SYM; INSERT_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `P a ==> {x | x IN {a} /\ P x} = {a}`] THEN
    ASM_CASES_TAC `b:real^2 = a` THENL
     [ASM_MESON_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `~(a = b) ==> {b} INTER {a} = {}`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; SUB_0] THEN
    MATCH_MP_TAC(ARITH_RULE
     `c:num <= ca /\ a <= ab /\ b <= bc /\
      bc' + ac' + ab' + a + b + c = ab + bc + ca + 3
      ==> bc' + ac' + ab' = (ab + (bc + ca) - c) - (b + a) + 3`) THEN
    ASM_SIMP_TAC[CARD_SUBSET; SING_SUBSET; IN_ELIM_THM; ENDS_IN_SEGMENT;
                 FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT] THEN
    SIMP_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; FINITE_INSERT;
             FINITE_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER P`] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; INSERT_AC] THEN ARITH_TAC]);;
```

### Informal statement
For any points $a$, $b$, and $c$ in $\mathbb{R}^2$ with integer coordinates (i.e., $a$, $b$, and $c$ are integral vectors), the measure (area) of the convex hull of the set $\{a, b, c\}$ is given by:

$$\text{measure}(\text{convex hull } \{a,b,c\}) = \begin{cases} 
0, & \text{if } \{a,b,c\} \text{ are collinear} \\
|I| + \frac{|B|}{2} - 1, & \text{otherwise}
\end{cases}$$

where:
- $I = \{x \in \text{interior}(\text{convex hull } \{a,b,c\}) \mid x \text{ is an integral vector}\}$ is the set of interior lattice points
- $B = \{x \in \text{frontier}(\text{convex hull } \{a,b,c\}) \mid x \text{ is an integral vector}\}$ is the set of boundary lattice points

### Informal proof
This theorem is a specific case of Pick's theorem for triangles, which relates the area of a lattice polygon to the number of interior and boundary lattice points.

The proof proceeds in two cases:

- **Case 1: When the points $\{a, b, c\}$ are collinear**
  
  If the points are collinear, then the convex hull is a line segment, which has zero area. This follows directly from the fact that collinear sets are negligible (have zero measure).

- **Case 2: When the points $\{a, b, c\}$ are not collinear**

  We apply the alternative form of Pick's theorem for triangles (from `PICK_TRIANGLE_ALT`) which states that:
  
  $$\text{measure}(\text{convex hull } \{a,b,c\}) = |T| - \frac{|E_1| + |E_2| + |E_3|}{2} + \frac{1}{2}$$
  
  where:
  - $T = \{x \in \text{convex hull } \{a,b,c\} \mid x \text{ is an integral vector}\}$ is the set of all lattice points in the triangle
  - $E_1, E_2, E_3$ are the sets of lattice points on each edge of the triangle
  
  We then use the fact that:
  - The interior of the triangle equals the triangle minus its frontier (boundary)
  - The frontier of the triangle is the union of its three edges
  
  By set theory manipulations and counting arguments:
  - We establish that $|T| = |I| + |B|$ where $I$ and $B$ are interior and boundary points
  - The boundary points $|B|$ can be expressed in terms of the points on the three edges
  - Accounting for double-counting at vertices, we arrive at the formula $|I| + \frac{|B|}{2} - 1$

The proof involves careful tracking of the cardinalities of various sets of lattice points and applying several properties of convex hulls and segments in $\mathbb{R}^2$.

### Mathematical insight
This theorem is a special case of Pick's theorem, a fundamental result in discrete geometry that provides a formula for calculating the area of a simple polygon with vertices on a lattice grid.

Pick's theorem states that for a simple polygon with lattice points as vertices, the area equals $i + \frac{b}{2} - 1$, where $i$ is the number of interior lattice points and $b$ is the number of lattice points on the boundary.

The result is important because:
1. It establishes a beautiful connection between continuous geometric measure (area) and discrete counting (lattice points)
2. It provides an efficient way to calculate areas of lattice polygons
3. It serves as a foundation for more general results in algebraic geometry and number theory

The theorem illustrates how geometric quantities can be computed through combinatorial means, bridging continuous and discrete mathematics.

### Dependencies
#### Theorems
- `MEASURE_EQ_0`: If a set is negligible, then its measure is 0
- `COLLINEAR_IMP_NEGLIGIBLE`: Collinear sets in $\mathbb{R}^2$ are negligible
- `COLLINEAR_CONVEX_HULL_COLLINEAR`: If a set is collinear, then its convex hull is also collinear
- `PICK_TRIANGLE_ALT`: The alternative form of Pick's theorem for triangles
- `INTERIOR_OF_TRIANGLE`: Characterization of the interior of a triangle
- `FRONTIER_OF_TRIANGLE`: Characterization of the frontier of a triangle
- `FINITE_BOUNDED_INTEGER_POINTS`: A bounded set contains only finitely many integral vectors

#### Definitions
- `measure`: The measure (area) of a set
- `integral_vector`: A vector whose components are all integers

### Porting notes
When porting this theorem:
1. Ensure that the convex hull, interior, and frontier operations work the same way in the target system
2. Pay attention to how the target system handles cardinality of sets
3. The theorem relies on measure theory results, so ensure that the measure is properly defined
4. The proof uses many set-theoretic manipulations, so the target system should have good support for set operations
5. Be aware that the theorem is specifically for 2D, so dimension-specific theorems may be needed

---

## PARITY_LEMMA

### Name of formal statement
PARITY_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PARITY_LEMMA = prove
 (`!a b c d p x:real^2.
        simple_path(p ++ linepath(a,b)) /\
        pathstart p = b /\ pathfinish p = a /\
        segment(a,b) INTER segment(c,d) = {x} /\
        segment[c,d] INTER path_image p = {}
        ==> (c IN inside(path_image(p ++ linepath(a,b))) <=>
             d IN outside(path_image(p ++ linepath(a,b))))`,
  let lemma = prove
   (`!a b x y:real^N.
          collinear{y,a,b} /\ between x (a,b) /\
          dist(y,x) < dist(x,b) /\ dist(y,x) < dist(x,a)
          ==> y IN segment(a,b)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COLLINEAR_DIST_IN_OPEN_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[between; DIST_SYM] THEN
    NORM_ARITH_TAC)
  and symlemma = prove
   (`(!n. P(--n) <=> P (n)) /\ (!n. &0 < n dot x ==> P n)
     ==> !n:real^N. ~(n dot x = &0) ==> P n`,
    STRIP_TAC THEN GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `~(x = &0) <=> &0 < x \/ &0 < --x`] THEN
    REWRITE_TAC[GSYM DOT_LNEG] THEN ASM_MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real^1->real^2`; `linepath(a:real^2,b)`]
        SIMPLE_PATH_JOIN_LOOP_EQ) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLE_PATH_IMP_PATH) THEN
  ASM_SIMP_TAC[PATH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(a:real^2) INSERT b INSERT c INSERT d INSERT path_image p`;
                 `x:real^2`]
        DISTANCE_ATTAINS_INF) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN
  ONCE_REWRITE_TAC[SET_RULE `a INSERT b INSERT c INSERT d INSERT s =
                             {a,b,c,d} UNION s`] THEN
  ASM_SIMP_TAC[CLOSED_UNION; FINITE_IMP_CLOSED; CLOSED_PATH_IMAGE;
               FINITE_INSERT; FINITE_EMPTY] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cp:real^2` MP_TAC) THEN
  DISJ_CASES_TAC(NORM_ARITH `cp = x \/ &0 < dist(x:real^2,cp)`) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `~a ==> a /\ b ==> c`) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE `a = {x} ==> x IN a`)) THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_UNION; IN_INSERT; NOT_IN_EMPTY;
                IN_INTER; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `p INTER s SUBSET u ==> x IN (s DIFF u) ==> ~(x IN p)`)) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; PATH_IMAGE_LINEPATH];
    ALL_TAC] THEN
  ABBREV_TAC `e = dist(x:real^2,cp)` THEN FIRST_X_ASSUM(K ALL_TAC o SYM) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARC_LINEPATH_EQ]) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`; `d:real^2`]
        FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`; `c:real^2`]
        FINITE_INTER_COLLINEAR_OPEN_SEGMENTS) THEN
  SUBST1_TAC(MESON[SEGMENT_SYM] `segment(d:real^2,c) = segment(c,d)`) THEN
  ASM_REWRITE_TAC[FINITE_SING; NOT_INSERT_EMPTY] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~(a IN segment[c:real^2,d]) /\ ~(b IN segment[c,d])`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE;
                  IN_INTER; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c:real^2 = a) /\ ~(c = b) /\ ~(d = a) /\ ~(d = b)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `x IN segment(a:real^2,b) /\ x IN segment(c,d)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_OPEN_SEGMENT_ALT] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{c,d} INTER path_image(p ++ linepath(a:real^2,b)) = {}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_LINEPATH; PATHSTART_LINEPATH] THEN
    REWRITE_TAC[SET_RULE
     `{c,d} INTER (s UNION t) = {} <=>
      (~(c IN s) /\ ~(d IN s)) /\ ~(c IN t) /\ ~(d IN t)`] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT; IN_INTER; NOT_IN_EMPTY];
      REWRITE_TAC[PATH_IMAGE_LINEPATH; GSYM BETWEEN_IN_SEGMENT] THEN
      CONJ_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `b - x:real^2` ORTHOGONAL_TO_VECTOR_EXISTS) THEN
  REWRITE_TAC[DIMINDEX_2; LE_REFL; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^2) IN segment(a,b) /\ x IN segment(c,d)` MP_TAC THENL
   [ASM SET_TAC[];
    SIMP_TAC[IN_OPEN_SEGMENT_ALT; GSYM BETWEEN_IN_SEGMENT] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^2, b, c, d}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COLLINEAR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n dot (d - x:real^2) = &0)` MP_TAC THENL
   [REWRITE_TAC[GSYM orthogonal] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:real^2`; `d - x:real^2`; `b - x:real^2`]
      ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM COLLINEAR_3] THEN DISCH_TAC THEN
    UNDISCH_TAC `~collinear{a:real^2, b, c, d}` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b,c,d} = {b,d,a,c}`] THEN
    ASM_SIMP_TAC[COLLINEAR_4_3] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `{b:real^2,x,a,d}` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[COLLINEAR_4_3]; SET_TAC[]] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,b,a}`] THEN
      ASM_SIMP_TAC[BETWEEN_IMP_COLLINEAR];
      MATCH_MP_TAC COLLINEAR_SUBSET THEN EXISTS_TAC `{d:real^2,x,b,c}` THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[COLLINEAR_4_3]; SET_TAC[]] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {c,b,a}`] THEN
      ASM_SIMP_TAC[BETWEEN_IMP_COLLINEAR]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
                       MP_TAC th) THEN
  SPEC_TAC(`n:real^2`,`n:real^2`) THEN
  MATCH_MP_TAC symlemma THEN CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_RNEG; VECTOR_NEG_EQ_0]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `n dot (c - x:real^2) < &0` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < n dot (d - x:real^2)` THEN
    SUBGOAL_THEN `(x:real^2) IN segment(c,d)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH
      `d - ((&1 - u) % c + u % d):real^N = (&1 - u) % (d - c) /\
       c - ((&1 - u) % c + u % d) = --u % (d - c)`] THEN
    REWRITE_TAC[DOT_RMUL; REAL_MUL_LNEG; REAL_ARITH `--x < &0 <=> &0 < x`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_SUB_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(x:real^2,e)
        ==> y IN segment(a,b) \/
            &0 < n dot (y - x) \/
            n dot (y - x) < &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~c /\ ~b ==> a) ==> a \/ b \/ c`) THEN
    REWRITE_TAC[REAL_ARITH `~(x < &0) /\ ~(&0 < x) <=> x = &0`] THEN
    REWRITE_TAC[GSYM orthogonal] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:real^2`; `y - x:real^2`; `b - x:real^2`]
      ORTHOGONAL_TO_ORTHOGONAL_2D) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[ORTHOGONAL_SYM]; ALL_TAC] THEN
    REWRITE_TAC[GSYM COLLINEAR_3] THEN DISCH_TAC THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[REAL_LTE_TRANS; DIST_SYM]] THEN
    ONCE_REWRITE_TAC[SET_RULE `{y,a,b} = {a,b,y}`] THEN
    MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `collinear{y:real^2, x, b}` THEN
    MP_TAC(MATCH_MP BETWEEN_IMP_COLLINEAR (ASSUME
     `between (x:real^2) (a,b)`)) THEN
    SIMP_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(SPEC `p ++ linepath(a:real^2,b)` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `~(connected_component((:real^2) DIFF path_image(p ++ linepath (a,b))) c d)`
  MP_TAC THENL
   [DISCH_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `path_image(p ++ linepath(a:real^2,b))` o
      MATCH_MP (SET_RULE
     `~(x IN s <=> y IN t)
      ==> !p. s UNION t = (:real^2) DIFF p /\ {x,y} INTER p = {}
              ==> x IN s /\ y IN s \/ x IN t /\ y IN t`)) THEN
    ASM_REWRITE_TAC[connected_component] THEN
    ASM_REWRITE_TAC[SET_RULE `t SUBSET UNIV DIFF s <=> t INTER s = {}`] THEN
    ASM_MESON_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP]] THEN
  MP_TAC(SPEC `p ++ linepath(a:real^2,b)` JORDAN_DISCONNECTED) THEN
  ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  SUBGOAL_THEN
   `!u v. u IN inside(path_image(p ++ linepath(a,b))) /\
          v IN outside(path_image(p ++ linepath(a,b)))
          ==> connected_component
              ((:real^2) DIFF path_image (p ++ linepath (a,b))) u v`
  ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [SYM(ASSUME `inside (path_image (p ++ linepath (a,b))) UNION
                  outside (path_image (p ++ linepath (a,b))) =
                  (:real^2) DIFF path_image (p ++ linepath (a,b))`)] THEN
    REWRITE_TAC[IN_UNION; CONNECTED_IFF_CONNECTED_COMPONENT] THEN
    STRIP_TAC THENL
     [REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `inside(path_image(p ++ linepath(a:real^2,b)))`;
      ASM_MESON_TAC[];
      ASM_MESON_TAC[CONNECTED_COMPONENT_SYM];
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `outside(path_image(p ++ linepath(a:real^2,b)))`] THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[OUTSIDE_NO_OVERLAP; INSIDE_NO_OVERLAP]] THEN
  SUBGOAL_THEN `(x:real^2) IN path_image(p ++ linepath(a,b))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
    REWRITE_TAC[IN_UNION; PATH_IMAGE_LINEPATH] THEN DISJ2_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[open_segment]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `frontier(inside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))` THEN
  REWRITE_TAC[EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[frontier] THEN
  REWRITE_TAC[IN_DIFF; CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `w:real^2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `inside(path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  UNDISCH_TAC
   `frontier(outside(path_image(p ++ linepath(a:real^2,b)))) =
    path_image(p ++ linepath(a,b))` THEN
  REWRITE_TAC[EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[frontier] THEN
  REWRITE_TAC[IN_DIFF; CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `z:real^2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `outside(path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF t <=> s INTER t = {}`] THEN
    REWRITE_TAC[OUTSIDE_NO_OVERLAP]] THEN
  SUBGOAL_THEN
   `!y. dist(y,x) < e /\ ~(y IN path_image(p ++ linepath (a,b)))
        ==> connected_component
             ((:real^2) DIFF path_image(p ++ linepath(a,b))) c y`
  ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `c:real^2` THEN
    CONJ_TAC THENL [MATCH_MP_TAC CONNECTED_COMPONENT_SYM; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP; IN_INTER;
                  NOT_IN_EMPTY]] THEN
  X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[c,d] INTER path_image(p ++ linepath(a,b)) = {x:real^2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `{c,d} INTER p = {} /\ (segment[c,d] DIFF {c,d}) INTER p = {x}
      ==> segment[c,d] INTER p = {x}`) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATH_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `cd INTER p = {} /\ l INTER (cd DIFF {c,d}) = {x}
      ==> (cd DIFF {c,d}) INTER (p UNION l) = {x}`) THEN
    ASM_REWRITE_TAC[GSYM open_segment; PATH_IMAGE_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `~(a IN segment[c,d]) /\ ~(b IN segment[c,d]) /\
      segment(a,b) INTER segment(c,d) = {x} /\
      segment(a,b) = segment[a,b] DIFF {a,b} /\
      segment(c,d) = segment[c,d] DIFF {c,d}
      ==> segment[a,b] INTER segment(c,d) = {x}`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[open_segment];
    ALL_TAC] THEN
  UNDISCH_THEN
    `!y. y IN ball(x:real^2,e)
          ==> y IN segment(a,b) \/ &0 < n dot (y - x) \/ n dot (y - x) < &0`
    (MP_TAC o SPEC `y:real^2`) THEN
  REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THENL
   [MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    UNDISCH_TAC `~(y IN path_image(p ++ linepath(a:real^2,b)))` THEN
    ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
    SIMP_TAC[CONTRAPOS_THM; open_segment; IN_DIFF; IN_UNION;
             PATH_IMAGE_LINEPATH];
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `x + min (&1 / &2) (e / &2 / norm(d - x)) % (d - x):real^2` THEN
    REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC `segment[x:real^2,d] DELETE x` THEN
      SIMP_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_CONNECTED] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)`)) THEN
        REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
        UNDISCH_TAC `segment (a,b) INTER segment (c,d) = {x:real^2}` THEN
        REWRITE_TAC[open_segment] THEN SET_TAC[];
        REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
         `x + a % (y - x):real^N = (&1 - a) % x + a % y`] THEN
        EXISTS_TAC `min (&1 / &2) (e / &2 / norm(d - x:real^2))` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ;
                        VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min (&1 / &2) x = &0)`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]];
      EXISTS_TAC `ball(x,e) INTER {w:real^2 | &0 < n dot (w - x)}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL; DOT_RSUB; REAL_SUB_LT] THEN
        REWRITE_TAC[GSYM real_gt; CONVEX_HALFSPACE_GT];
        ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
        MATCH_MP_TAC(SET_RULE
         `p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))`) THEN
        ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL; REAL_NOT_LT] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}`) THEN
        EXISTS_TAC `affine hull {x:real^2,b}` THEN CONJ_TAC THENL
         [REWRITE_TAC[AFFINE_HULL_2; FORALL_IN_GSPEC; SET_RULE
           `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          SIMP_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
          REWRITE_TAC[DOT_RMUL; VECTOR_ARITH
           `((&1 - v) % x + v % b) - x:real^N = v % (b - x)`] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[orthogonal]) THEN
          ONCE_REWRITE_TAC[DOT_SYM] THEN
          ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
          REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
          SIMP_TAC[SUBSET_HULL; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          SIMP_TAC[HULL_INC; IN_INSERT] THEN
          ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL] THEN
          ONCE_REWRITE_TAC[SET_RULE `{x,b,a} = {a,x,b}`] THEN
          MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM; dist] THEN
        REWRITE_TAC[NORM_ARITH `norm(x - (x + a):real^N) = norm a`] THEN
        REWRITE_TAC[VECTOR_ARITH `(x + a) - x:real^N = a`] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT;
                       VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ x < e ==> abs(min (&1 / &2) x) < e`) THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[DOT_RMUL] THEN MATCH_MP_TAC REAL_LT_MUL THEN
          ASM_REWRITE_TAC[REAL_LT_MIN] THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_01]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]];
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN
    EXISTS_TAC `x + min (&1 / &2) (e / &2 / norm(c - x)) % (c - x):real^2` THEN
    REWRITE_TAC[connected_component] THEN CONJ_TAC THENL
     [EXISTS_TAC `segment[x:real^2,c] DELETE x` THEN
      SIMP_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_CONNECTED] THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `cd INTER p = {x}
          ==> xd SUBSET cd
              ==> (xd DELETE x) SUBSET (UNIV DIFF p)`)) THEN
        REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
        UNDISCH_TAC `segment (a,b) INTER segment (c,d) = {x:real^2}` THEN
        REWRITE_TAC[open_segment] THEN SET_TAC[];
        REWRITE_TAC[IN_SEGMENT; VECTOR_ARITH
         `x + a % (y - x):real^N = (&1 - a) % x + a % y`] THEN
        EXISTS_TAC `min (&1 / &2) (e / &2 / norm(c - x:real^2))` THEN
        REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LE_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE];
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ;
                        VECTOR_ARITH `x + a:real^N = x <=> a = vec 0`] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(min (&1 / &2) x = &0)`) THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]];
      EXISTS_TAC `ball(x,e) INTER {w:real^2 | n dot (w - x) < &0}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
        REWRITE_TAC[CONVEX_BALL; DOT_RSUB; REAL_ARITH `a - b < &0 <=> a < b`;
                    CONVEX_HALFSPACE_LT];
        ASM_SIMP_TAC[PATHSTART_LINEPATH; PATH_IMAGE_JOIN; PATH_LINEPATH] THEN
        MATCH_MP_TAC(SET_RULE
         `p SUBSET (UNIV DIFF b) /\ l INTER w = {}
          ==> (b INTER w) SUBSET (UNIV DIFF (p UNION l))`) THEN
        ASM_REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_BALL; REAL_NOT_LT] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. t INTER u = {} /\ s SUBSET t ==> s INTER u = {}`) THEN
        EXISTS_TAC `affine hull {x:real^2,b}` THEN CONJ_TAC THENL
         [REWRITE_TAC[AFFINE_HULL_2; FORALL_IN_GSPEC; SET_RULE
           `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
          SIMP_TAC[REAL_ARITH `u + v = &1 <=> u = &1 - v`] THEN
          REWRITE_TAC[DOT_RMUL; VECTOR_ARITH
           `((&1 - v) % x + v % b) - x:real^N = v % (b - x)`] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[orthogonal]) THEN
          ONCE_REWRITE_TAC[DOT_SYM] THEN
          ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
          REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL] THEN
          SIMP_TAC[SUBSET_HULL; AFFINE_IMP_CONVEX; AFFINE_AFFINE_HULL] THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          SIMP_TAC[HULL_INC; IN_INSERT] THEN
          ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL] THEN
          ONCE_REWRITE_TAC[SET_RULE `{x,b,a} = {a,x,b}`] THEN
          MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM; dist] THEN
        REWRITE_TAC[NORM_ARITH `norm(x - (x + a):real^N) = norm a`] THEN
        REWRITE_TAC[VECTOR_ARITH `(x + a) - x:real^N = a`] THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LT_RDIV_EQ; NORM_POS_LT;
                       VECTOR_SUB_EQ] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ x < e ==> abs(min (&1 / &2) x) < e`) THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_DIV2_EQ] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[DOT_RMUL; REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
          ASM_REWRITE_TAC[REAL_ARITH `&0 < --x <=> x < &0`] THEN
          ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ;
                       REAL_LT_01]];
        REWRITE_TAC[IN_BALL; IN_INTER; IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]]]);;
```

### Informal statement
For any points $a, b, c, d$ and $x$ in $\mathbb{R}^2$, and any simple path $p$, if:
- $p \oplus \text{linepath}(a,b)$ is a simple path
- $p$ starts at $b$ and ends at $a$
- The segments $(a,b)$ and $(c,d)$ intersect at exactly one point $x$
- The segment $[c,d]$ does not intersect the image of path $p$

Then $c$ is inside the closed curve formed by $p \oplus \text{linepath}(a,b)$ if and only if $d$ is outside this curve.

### Informal proof
This proof establishes a "parity lemma" that characterizes when a line segment crosses a simple closed curve.

First, we establish two auxiliary lemmas:
1. A geometric lemma showing that if a point $y$ is collinear with points $a$ and $b$, between $a$ and $b$, and close enough to a point $x$, then $y$ lies on the segment $(a,b)$.
2. A symmetry lemma about predicates on vectors.

For the main proof:

- We apply the Jordan curve theorem to our path $p \oplus \text{linepath}(a,b)$, which gives us that the curve divides the plane into two regions: inside and outside.

- We need to show that points $c$ and $d$ are on opposite sides of the curve. We prove this by contradiction, assuming they are in the same connected component of $\mathbb{R}^2 \setminus \text{path_image}(p \oplus \text{linepath}(a,b))$.

- Since the segment $(a,b)$ and $(c,d)$ intersect at exactly one point $x$, and $x$ is on the curve, we can show that there exists a vector $n$ orthogonal to $b-x$ such that $n \cdot (d-x) \neq 0$.

- Using this vector, we can establish that $n \cdot (c-x) < 0$ when $n \cdot (d-x) > 0$, which means $c$ and $d$ lie on opposite sides of the line through $x$ orthogonal to $b-x$.

- We then show that any point $y$ in a small ball around $x$ either:
  1. Lies on segment $(a,b)$, or
  2. Has $n \cdot (y-x) > 0$, or
  3. Has $n \cdot (y-x) < 0$

- Using the Jordan curve theorem and properties of frontier points, we can find points $w$ and $z$ very close to $x$ such that $w$ is inside the curve and $z$ is outside. We show these are connected to $c$ and $d$ respectively, within their respective regions.

- This contradicts our assumption that $c$ and $d$ share the same connected component, proving they must be on opposite sides of the curve.

### Mathematical insight
This theorem establishes a fundamental "parity principle" for how a line segment intersects a simple closed curve. If a line segment crosses a simple closed curve exactly once, its endpoints must lie on opposite sides of the curve. This result is intuitively clear from topology but requires careful analysis to prove formally.

The proof uses the Jordan Curve Theorem in an essential way, along with techniques from linear algebra (orthogonal vectors) to characterize the local geometry near the intersection point. This result is crucial for algorithms in computational geometry, particularly for determining whether a point is inside or outside a polygon.

### Dependencies
- `SIMPLE_PATH_JOIN_LOOP_EQ`: Characterizes when joining paths forms a loop
- `DISTANCE_ATTAINS_INF`: Result about distance infimum
- `COLLINEAR_DIST_IN_OPEN_SEGMENT`: Characterizes when a point is in an open segment
- `ORTHOGONAL_TO_VECTOR_EXISTS`: Existence of orthogonal vectors
- `ORTHOGONAL_TO_ORTHOGONAL_2D`: Properties of orthogonal vectors in 2D
- `COLLINEAR_3_TRANS`: Transitivity of collinearity
- `JORDAN_INSIDE_OUTSIDE`: Jordan curve theorem about inside vs outside
- `JORDAN_DISCONNECTED`: Disconnectedness result from Jordan curve theorem
- `FINITE_INTER_COLLINEAR_OPEN_SEGMENTS`: Result about intersection of collinear open segments
- `BETWEEN_IMP_COLLINEAR`: A point between two others implies collinearity
- Various path properties: `PATHSTART_LINEPATH`, `PATH_IMAGE_JOIN`, etc.

### Porting notes
When porting this theorem:
1. Ensure your target system has a well-established Jordan Curve Theorem
2. Pay attention to how paths and path concatenation are represented
3. The proof relies on several geometric lemmas about orthogonal vectors and collinearity in 2D that may need separate porting
4. The proof uses connected components and frontiers of sets, which may be represented differently in other systems
5. The HOL Light vector notation `n dot (d - x)` corresponds to the dot product $n \cdot (d - x)$ which might use different syntax in other systems

---

## polygonal_path

### polygonal_path

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let polygonal_path = define
 `polygonal_path[] = linepath(vec 0,vec 0) /\
  polygonal_path[a] = linepath(a,a) /\
  polygonal_path [a;b] = linepath(a,b) /\
  polygonal_path (CONS a (CONS b (CONS c l))) =
       linepath(a,b) ++ polygonal_path(CONS b (CONS c l))`;;
```

### Informal statement
The `polygonal_path` function defines a path formed by connecting consecutive points with straight line segments. Given a list of points, it is defined recursively as follows:

- $\text{polygonal\_path}[\,] = \text{linepath}(\vec{0},\vec{0})$
- $\text{polygonal\_path}[a] = \text{linepath}(a,a)$
- $\text{polygonal\_path}[a,b] = \text{linepath}(a,b)$
- $\text{polygonal\_path}(a :: b :: c :: l) = \text{linepath}(a,b) \oplus \text{polygonal\_path}(b :: c :: l)$

where $\vec{0}$ is the zero vector, $\text{linepath}(a,b)$ represents the straight line path from point $a$ to point $b$, and $\oplus$ denotes path concatenation.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The `polygonal_path` function creates a continuous path by connecting a sequence of points with straight lines. This is a fundamental construction in computational geometry and topology.

Some notable aspects:
- For the empty list, a degenerate path at the origin is defined for convenience and linear invariance.
- For a single point, the path stays at that point.
- For two points, the path is simply a line between them.
- For three or more points, the path is constructed recursively by concatenating the line from the first point to the second with the polygonal path formed by the remaining points.

This construction allows defining arbitrary piecewise linear paths that can be used to approximate more complex curves or to define polygonal boundaries.

### Dependencies
#### Definitions:
- `linepath`: Defines a straight line path between two points
- `++`: Path concatenation operator

### Porting notes
When porting this definition:
- Ensure the target system has an equivalent concept of path concatenation and linear paths
- The use of the zero vector for the empty list case is arbitrary but ensures the path is well-defined in all cases
- Be mindful of how the target system handles recursive definitions over different list patterns

---

## POLYGONAL_PATH_CONS_CONS

### POLYGONAL_PATH_CONS_CONS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let POLYGONAL_PATH_CONS_CONS = prove
 (`!a b p. ~(p = [])
           ==> polygonal_path(CONS a (CONS b p)) =
               linepath(a,b) ++ polygonal_path(CONS b p)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[polygonal_path]);;
```

### Informal statement
For all points $a$, $b$, and any non-empty list of points $p$, the polygonal path formed by $a$, $b$, followed by the points in $p$ is equal to the line segment from $a$ to $b$ joined with the polygonal path starting at $b$ followed by the points in $p$:

$$\forall a, b, p. p \neq [] \Rightarrow \text{polygonal\_path}(a::b::p) = \text{linepath}(a,b) \oplus \text{polygonal\_path}(b::p)$$

where $\oplus$ denotes path concatenation.

### Informal proof
We prove this by induction on the list $p$.

* **Base case**: When $p = [c]$ for some point $c$ (since $p$ is non-empty)
  - By definition of `polygonal_path`, we have:
    - $\text{polygonal\_path}(a::b::[c]) = \text{polygonal\_path}([a,b,c]) = \text{linepath}(a,b) \oplus \text{polygonal\_path}([b,c])$

* **Inductive case**: When $p = c::l$ for some point $c$ and list $l$
  - By definition of `polygonal_path`, for a list with three or more elements, we have:
    - $\text{polygonal\_path}(a::b::c::l) = \text{linepath}(a,b) \oplus \text{polygonal\_path}(b::c::l)$

In both cases, the result follows directly from applying the definition of `polygonal_path`.

### Mathematical insight
This theorem provides a key compositional property of polygonal paths: they can be broken down into individual line segments. The result is crucial for understanding how polygonal paths are constructed and manipulated in geometric reasoning.

The theorem effectively gives an alternative recursive formulation for polygonal paths, showing that we can construct a polygonal path incrementally by adding one vertex at a time and joining with a line segment.

This decomposition is useful for proofs about polygonal paths, as it allows reasoning about the path properties one segment at a time.

### Dependencies
- **Definitions**:
  - `polygonal_path`: Defines a path through a sequence of points as a concatenation of line segments

### Porting notes
When porting this theorem, ensure that:
1. The definition of polygonal paths in your target system follows the same recursive structure
2. The path concatenation operation (represented by `++` in HOL Light) is appropriately defined
3. Your system's list operations properly handle the cons operations and empty list checks

---

## POLYGONAL_PATH_TRANSLATION

### Name of formal statement
POLYGONAL_PATH_TRANSLATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYGONAL_PATH_TRANSLATION = prove
 (`!a b p. polygonal_path (MAP (\x. a + x) (CONS b p)) =
         (\x. a + x) o (polygonal_path (CONS b p))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[MAP; polygonal_path; LINEPATH_TRANSLATION] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN
  ASM_SIMP_TAC[MAP; polygonal_path; LINEPATH_TRANSLATION] THEN
  REWRITE_TAC[JOINPATHS_TRANSLATION]);;
```

### Informal statement
For any vectors $a$, $b$ and list of vectors $p$, a translation of a polygonal path by vector $a$ is equivalent to composition with the translation function:

$$\text{polygonal\_path}(\text{MAP}(\lambda x. a + x)(\text{CONS}(b, p))) = (\lambda x. a + x) \circ \text{polygonal\_path}(\text{CONS}(b, p))$$

where:
- $\text{polygonal\_path}$ constructs a path from a list of points
- $\text{MAP}$ applies the function $\lambda x. a + x$ to each element in the list
- $\text{CONS}(b, p)$ is the list with $b$ as first element followed by elements of $p$
- $\circ$ denotes function composition

### Informal proof
We prove that translating each point in a polygonal path by vector $a$ is equivalent to translating the entire path by $a$. The proof proceeds by induction on the list structure:

1. We use induction on the list $p$, with $b$ fixed.
   
2. Base case: When $p$ is empty, we have:
   $$\text{polygonal\_path}(\text{MAP}(\lambda x. a + x)[\text{CONS}(b)]) = \text{polygonal\_path}([a+b])$$
   
   By the definition of `polygonal_path` for a single-element list and `LINEPATH_TRANSLATION`, this equals $(\lambda x. a + x) \circ \text{polygonal\_path}([b])$.

3. Inductive step: We perform another induction on the next element of the list.
   - For the base case of this nested induction, we use `LINEPATH_TRANSLATION`
   - For the inductive step, we use both the inductive hypothesis and `JOINPATHS_TRANSLATION`

4. The theorem follows from the principle of double induction on the list structure, combined with previously established results about translations of line paths and joined paths.

### Mathematical insight
This theorem establishes an important property for geometric transformations: translating each point of a polygonal path by a vector is equivalent to translating the entire path as a function. This is a fundamental result for computer graphics and computational geometry, showing that translations behave well with respect to paths constructed from multiple line segments.

The result generalizes the property of linear paths under translation to the more complex case of polygonal paths (which are essentially concatenations of linear paths). This compositionality principle allows for efficient geometric algorithms when working with transformed shapes.

### Dependencies
#### Definitions
- `polygonal_path`: Recursively defines a path from a list of points, where consecutive points are connected by line segments

#### Theorems
- `LINEPATH_TRANSLATION`: States that translating a linear path is equivalent to composing with a translation function
- `JOINPATHS_TRANSLATION`: States that translation distributes over path joining

### Porting notes
When implementing this in another proof assistant:
- Ensure the definition of `polygonal_path` matches, particularly its handling of empty, singleton, and two-element lists as special cases
- The theorem relies on a double induction on list structure, which might require different tactics in other systems
- The handling of function composition may differ in syntax across systems

---

## POLYGONAL_PATH_LINEAR_IMAGE

### POLYGONAL_PATH_LINEAR_IMAGE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let POLYGONAL_PATH_LINEAR_IMAGE = prove
 (`!f p. linear f ==> polygonal_path (MAP f p) = f o polygonal_path p`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; MAP] THEN CONJ_TAC THENL
   [REWRITE_TAC[LINEPATH_REFL; o_DEF; FUN_EQ_THM] THEN ASM_MESON_TAC[LINEAR_0];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[polygonal_path; MAP] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[LINEPATH_LINEAR_IMAGE];
    ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[polygonal_path; MAP] THEN
  ASM_SIMP_TAC[GSYM JOINPATHS_LINEAR_IMAGE; GSYM LINEPATH_LINEAR_IMAGE]);;
```

### Informal statement
For any linear function $f$ and path $p$, the polygonal path through the points mapped by $f$ is equal to the composition of $f$ with the polygonal path through the original points. Formally:

$$\forall f, p. \text{ linear } f \implies \text{polygonal\_path}(\text{MAP } f \, p) = f \circ \text{polygonal\_path } p$$

This means that applying a linear transformation to the vertices of a polygonal path and then constructing the path is equivalent to first constructing the path and then applying the linear transformation to every point on the path.

### Informal proof
The theorem is proved by induction on the list structure of the path $p$.

- **Base case** ($p = []$): 
  When $p$ is empty, we have:
  $$\text{polygonal\_path}(\text{MAP } f \, []) = \text{polygonal\_path}([]) = \text{linepath}(\vec{0},\vec{0})$$
  
  And on the right side:
  $$f \circ \text{polygonal\_path}([]) = f \circ \text{linepath}(\vec{0},\vec{0})$$
  
  These are equal because $f$ is linear and $f(\vec{0}) = \vec{0}$.

- **Case** ($p = [a]$): 
  When $p$ has one element, we use the fact that the linear image of a single point path is the path through the image of that point.

- **Case** ($p = [a, b]$):
  For a two-point path, we apply the fact that the linear image of a line path is the line path through the images of the endpoints, which follows from `LINEPATH_LINEAR_IMAGE`.

- **Inductive case** ($p = a::b::c::l$): 
  For longer paths, we use the recursive definition of `polygonal_path`:
  $$\text{polygonal\_path}(a::b::c::l) = \text{linepath}(a,b) ++ \text{polygonal\_path}(b::c::l)$$
  
  We can apply the linear function $f$ to both sides, and by induction hypothesis and the properties of linear functions on paths (specifically using `JOINPATHS_LINEAR_IMAGE` and `LINEPATH_LINEAR_IMAGE`), we establish the equality.

### Mathematical insight
This theorem states that linear transformations preserve polygonal paths in the sense that transforming the vertices and then constructing the path is equivalent to transforming the entire path. This is a natural property we would expect from linear transformations and is important for manipulation and transformation of geometric objects in vector spaces.

The result is part of a broader family of theorems showing how geometric constructions behave under linear maps, which is fundamental in linear algebra and its applications to geometry.

### Dependencies
- Definitions:
  - `polygonal_path`: Defines a path through a sequence of points, connecting consecutive points with line segments
- Theorems:
  - `LINEPATH_REFL`
  - `LINEAR_0`
  - `LINEPATH_LINEAR_IMAGE`
  - `JOINPATHS_LINEAR_IMAGE`

### Porting notes
When porting this theorem, ensure that:
1. The definition of `polygonal_path` matches the HOL Light definition, including special cases for empty, singleton, and two-element lists
2. The notation for function composition (`o`) is properly handled
3. The system has equivalent theorems for how linear functions interact with line paths and path joining

---

## PATHSTART_POLYGONAL_PATH

### PATHSTART_POLYGONAL_PATH
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATHSTART_POLYGONAL_PATH = prove
 (`!p. pathstart(polygonal_path p) = if p = [] then vec 0 else HD p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; NOT_CONS_NIL; HD] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; HD; PATHSTART_JOIN]);;
```

### Informal statement
The theorem states that for any list of points `p`, the starting point of the polygonal path defined by `p` is:
- The zero vector if `p` is empty
- The first element of `p` otherwise

Formally: 
$$\forall p. \text{pathstart}(\text{polygonal\_path}(p)) = \begin{cases}
\vec{0} & \text{if } p = [] \\
\text{HD}(p) & \text{otherwise}
\end{cases}$$

where `pathstart` gives the starting point of a path, `polygonal_path` constructs a path from a list of points, and `HD` returns the first element of a list.

### Informal proof

The proof proceeds by structural induction on the list `p`:

1. **Base case** (`p = []`):
   - From the definition of `polygonal_path`, we have `polygonal_path [] = linepath(vec 0, vec 0)`
   - Using `PATHSTART_LINEPATH`, we know that `pathstart(linepath(vec 0, vec 0)) = vec 0`
   - This matches the desired result when `p = []`

2. **Inductive cases**:
   - For a singleton list `p = [a]`:
     - By definition, `polygonal_path [a] = linepath(a, a)`
     - By `PATHSTART_LINEPATH`, `pathstart(linepath(a, a)) = a = HD [a]`
     
   - For a two-element list `p = [a, b]`:
     - By definition, `polygonal_path [a; b] = linepath(a, b)`
     - By `PATHSTART_LINEPATH`, `pathstart(linepath(a, b)) = a = HD [a; b]`
     
   - For a list with three or more elements `p = a::b::c::l`:
     - By definition, `polygonal_path (a::b::c::l) = linepath(a, b) ++ polygonal_path(b::c::l)`
     - Using `PATHSTART_JOIN`, we know that the starting point of a joined path equals the starting point of the first path
     - Therefore, `pathstart(polygonal_path(a::b::c::l)) = pathstart(linepath(a, b)) = a = HD (a::b::c::l)`

Thus, for any non-empty list `p`, we have `pathstart(polygonal_path p) = HD p`.

### Mathematical insight
This theorem establishes a fundamental property of polygonal paths: the starting point of a polygonal path is either the zero vector (for an empty list) or the first point in the list. This result is intuitively clear from the construction of polygonal paths, which connect consecutive points in the given list.

The result is important for reasoning about paths in geometric contexts, particularly when working with path properties or transformations. It provides a simple way to identify the starting point of a polygonal path without having to unfold its definition.

### Dependencies
- Definitions:
  - `polygonal_path`: Defines how to construct a path from a list of points
- Theorems (implicit):
  - `PATHSTART_LINEPATH`: Specifies the starting point of a line path
  - `PATHSTART_JOIN`: Specifies the starting point of a joined path

### Porting notes
When porting to other systems:
- Ensure that the underlying path definitions (`linepath`, path joining `++`) are consistent with HOL Light's implementation
- The case analysis on list structure may need to be handled differently depending on how the target system represents lists and pattern matching
- The proof relies on structural induction on lists, which should be available in most proof assistants but might use different syntax

---

## PATHFINISH_POLYGONAL_PATH

### Name of formal statement
PATHFINISH_POLYGONAL_PATH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PATHFINISH_POLYGONAL_PATH = prove
 (`!p. pathfinish(polygonal_path p) = if p = [] then vec 0 else LAST p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH; NOT_CONS_NIL; LAST] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATHFINISH_LINEPATH; PATHFINISH_JOIN]);;
```

### Informal statement
For any list of vectors $p$, the endpoint of the polygonal path determined by $p$ is:
- If $p$ is empty, then the zero vector $\vec{0}$
- Otherwise, the last element of $p$ (denoted by $\text{LAST } p$)

Formally:
$$\forall p. \text{pathfinish}(\text{polygonal\_path } p) = 
\begin{cases}
\vec{0} & \text{if } p = [] \\
\text{LAST } p & \text{otherwise}
\end{cases}$$

### Informal proof
The proof proceeds by induction on the list structure:

1. **Base case**: When $p = []$ (empty list)
   - By definition of `polygonal_path`, we have `polygonal_path [] = linepath(vec 0, vec 0)`
   - The endpoint of a line path is its second parameter, so `pathfinish(linepath(vec 0, vec 0)) = vec 0`

2. **Inductive cases**:
   - For a singleton list $p = [a]$:
     - By definition, `polygonal_path [a] = linepath(a, a)`
     - Thus `pathfinish(polygonal_path [a]) = a = LAST [a]`
   
   - For a list with two elements $p = [a, b]$:
     - By definition, `polygonal_path [a, b] = linepath(a, b)`
     - Thus `pathfinish(polygonal_path [a, b]) = b = LAST [a, b]`
   
   - For a list with three or more elements $p = a:b:c:l$ (using cons notation):
     - By definition, `polygonal_path (a::b::c::l) = linepath(a, b) ++ polygonal_path(b::c::l)`
     - Using the property that the endpoint of a joined path equals the endpoint of the second path:
       `pathfinish(linepath(a, b) ++ polygonal_path(b::c::l)) = pathfinish(polygonal_path(b::c::l))`
     - By the induction hypothesis, this equals `LAST (b::c::l)` which equals `LAST (a::b::c::l)`

Thus, for any non-empty list $p$, the endpoint of the polygonal path is the last element of $p$.

### Mathematical insight
This theorem establishes a fundamental property of polygonal paths: the endpoint of a path constructed from a list of points is simply the last point in that list (or the origin if the list is empty). This result is useful for path manipulation and geometric calculations, as it gives a direct way to determine where a polygonal path ends without having to traverse the entire path.

The theorem shows how the recursive definition of polygonal paths yields a straightforward result for the endpoint, which is important for reasoning about paths in topological or geometric contexts.

### Dependencies
- **Definitions**: 
  - `polygonal_path`: Recursively defines a polygonal path from a list of points
  
- **Theorems**: 
  - `PATHFINISH_LINEPATH`: Provides the endpoint of a linear path
  - `PATHFINISH_JOIN`: Gives the endpoint of a joined path
  - `list_INDUCT`: Induction principle for lists
  
- **HOL Light built-ins**:
  - `LAST`: Function that returns the last element of a list
  - List operations and conditionals

### Porting notes
When porting this theorem to other systems:
- Ensure the definition of `polygonal_path` is correctly implemented with the same recursion pattern
- The proof relies on list induction, which should be available in most systems, but the exact tactic might differ
- Pay attention to how path joining (`++`) is defined in the target system, as this is crucial for the recursive case

---

## VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH

### VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH = prove
 (`!p:(real^N)list. set_of_list p SUBSET path_image (polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[set_of_list; EMPTY_SUBSET] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[set_of_list; polygonal_path; PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[SEGMENT_REFL; INSERT_AC; SUBSET_REFL] THEN
   GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[set_of_list; polygonal_path] THEN CONJ_TAC THENL
   [REWRITE_TAC[PATH_IMAGE_LINEPATH; INSERT_SUBSET; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[EMPTY_SUBSET];
    REPEAT GEN_TAC THEN REPLICATE_TAC 3 DISCH_TAC THEN
    ONCE_REWRITE_TAC[INSERT_SUBSET] THEN
    SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
        HD; NOT_CONS_NIL; IN_UNION; ENDS_IN_SEGMENT; PATH_IMAGE_LINEPATH] THEN
    ASM SET_TAC[]]);;
```

### Informal statement
For any list of points $p$ in $\mathbb{R}^N$, the set of all vertices in the list $p$ is a subset of the path image of the polygonal path defined by $p$. 

Formally, for any $p : (\mathbb{R}^N)$ list:
$$\text{set\_of\_list}(p) \subseteq \text{path\_image}(\text{polygonal\_path}(p))$$

### Informal proof
The proof proceeds by induction on the list $p$.

* **Base case**: When $p = []$ (empty list)
  - $\text{set\_of\_list}([]) = \emptyset$
  - Since the empty set is a subset of any set, the theorem holds.

* **Inductive cases**: For a non-empty list, we perform another induction on the tail
  
  - **Case $p = [h]$** (singleton list):
    - $\text{set\_of\_list}([h]) = \{h\}$
    - $\text{polygonal\_path}([h]) = \text{linepath}(h, h)$
    - $\text{path\_image}(\text{linepath}(h, h)) = \{h\}$ (segment reduces to a point)
    - Thus $\{h\} \subseteq \{h\}$, which is true.
  
  - **Case $p = [h_1, h_2]$** (list with two elements):
    - $\text{set\_of\_list}([h_1, h_2]) = \{h_1, h_2\}$
    - $\text{polygonal\_path}([h_1, h_2]) = \text{linepath}(h_1, h_2)$
    - $\text{path\_image}(\text{linepath}(h_1, h_2))$ contains both endpoints $h_1$ and $h_2$
    - Therefore $\{h_1, h_2\} \subseteq \text{path\_image}(\text{linepath}(h_1, h_2))$
  
  - **Case $p = h_1 :: h_2 :: h_3 :: t$** (list with at least three elements):
    - By definition, $\text{polygonal\_path}(h_1 :: h_2 :: h_3 :: t) = \text{linepath}(h_1, h_2) \mathbin{++} \text{polygonal\_path}(h_2 :: h_3 :: t)$
    - We need to show that $\{h_1\} \cup \text{set\_of\_list}(h_2 :: h_3 :: t) \subseteq \text{path\_image}(\text{linepath}(h_1, h_2) \mathbin{++} \text{polygonal\_path}(h_2 :: h_3 :: t))$
    - By induction hypothesis, $\text{set\_of\_list}(h_2 :: h_3 :: t) \subseteq \text{path\_image}(\text{polygonal\_path}(h_2 :: h_3 :: t))$
    - The path image of a joined path is the union of the path images
    - $h_1$ is in the path image of $\text{linepath}(h_1, h_2)$
    - $h_2$ is both the end of $\text{linepath}(h_1, h_2)$ and the start of $\text{polygonal\_path}(h_2 :: h_3 :: t)$
    - Using these facts and set theory, the result follows.

### Mathematical insight
This theorem establishes that a polygonal path contains all the vertices used to define it, which is an essential property for many geometric applications. While intuitively obvious, formally proving this is important for building more complex theorems about polygonal paths.

The result confirms that when constructing a polygonal path from a list of points, every point in that list becomes a vertex of the resulting path. This is useful when working with path connectivity, path homotopy, and algorithms involving polygonal approximations of continuous curves.

### Dependencies
- **Theorems**:
  - `PATHSTART_POLYGONAL_PATH`: Defines the starting point of a polygonal path.
- **Definitions**:
  - `polygonal_path`: Recursively defines a polygonal path from a list of points.

### Porting notes
When porting this theorem:
1. Ensure that the definition of `polygonal_path` is correctly implemented first.
2. The proof relies heavily on structural induction over lists, which should be available in most proof assistants.
3. In systems with different path representations, you may need to adjust the definition to match the local conventions for path images and path joining.

---

## ARC_POLYGONAL_PATH_IMP_DISTINCT

### Name of formal statement
ARC_POLYGONAL_PATH_IMP_DISTINCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ARC_POLYGONAL_PATH_IMP_DISTINCT = prove
 (`!p:(real^N)list. arc(polygonal_path p) ==> PAIRWISE (\x y. ~(x = y)) p`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN
  X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; ARC_LINEPATH_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[PAIRWISE; ALL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN
  SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           HD; NOT_CONS_NIL; ARC_LINEPATH_EQ] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[PAIRWISE] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[ALL] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
  ASM_REWRITE_TAC[IN_INTER; IN_SING; ENDS_IN_SEGMENT; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
    (REWRITE_RULE[SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH))) THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM; DE_MORGAN_THM; GSYM ALL_MEM] THEN
  MESON_TAC[]);;
```

### Informal statement
For any list $p$ of points in $\mathbb{R}^N$, if the polygonal path formed by $p$ is an arc, then all points in $p$ are pairwise distinct.

Formally, for all $p: (\mathbb{R}^N)$ list:
$$\text{arc}(\text{polygonal\_path}(p)) \Rightarrow \text{PAIRWISE}(\lambda x\,y. x \neq y)(p)$$

Where:
- $\text{polygonal\_path}(p)$ represents a path constructed by connecting consecutive points in the list $p$ with straight line segments
- $\text{arc}(path)$ means the path is simple (non-self-intersecting) and not a loop
- $\text{PAIRWISE}(\lambda x\,y. x \neq y)(p)$ means all elements in $p$ are pairwise distinct

### Informal proof
We prove this by induction on the list $p$.

* Base case: For the empty list, the polygonal path is just a point (a degenerate line segment from the zero vector to itself), which is not an arc. The implication holds vacuously.

* For a singleton list $[a]$, the polygonal path is just a point, which again is not an arc. The implication holds vacuously.

* For a two-element list $[a, b]$, the polygonal path is simply a line segment from $a$ to $b$. By `ARC_LINEPATH_EQ`, this is an arc if and only if $a \neq b$, which is precisely what we need to prove: that the points are distinct.

* For a list with at least three elements $[a, b, c, \ldots]$, we proceed as follows:
  - The polygonal path can be decomposed as the join of the line segment from $a$ to $b$ and the polygonal path starting from $b$ through the remaining points.
  - For this to be an arc, several conditions must be met (by `ARC_JOIN_EQ`):
    1. The line segment from $a$ to $b$ must be an arc, which means $a \neq b$.
    2. The remaining polygonal path must be an arc.
    3. The point $a$ cannot lie on the polygonal path starting from $b$.

  - By the induction hypothesis, all points in the remaining list $[b, c, \ldots]$ are pairwise distinct.
  - Using `VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH`, we know all vertices in a list are in the path image of the corresponding polygonal path.
  - The fact that $a$ cannot lie on the polygonal path starting from $b$ implies that $a$ is distinct from all points in the list $[b, c, \ldots]$.
  - Combining these results, we establish that all points in the original list $[a, b, c, \ldots]$ are pairwise distinct.

### Mathematical insight
This theorem establishes a fundamental property of polygonal paths: for a polygonal path to be an arc (a simple, non-self-intersecting path), it must not revisit any vertex. In geometric terms, if we want to draw a polygonal path without self-intersections, we must use distinct points.

This result is crucial for many algorithms and proofs in computational geometry and topological graph theory. It confirms the intuitive notion that repeating a point in a vertex list would create either a loop (which isn't an arc) or force self-intersection (which also violates the arc property).

### Dependencies
#### Theorems
- `PATHSTART_POLYGONAL_PATH`: Defines the starting point of a polygonal path
- `VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH`: Shows that all vertices in the list are contained in the path image

#### Definitions
- `polygonal_path`: Recursively defines a polygonal path from a list of points

### Porting notes
When porting this theorem:
1. Ensure your target system has compatible definitions for polygonal paths and arcs
2. The proof relies on induction over lists and set-theoretic operations, which most proof assistants support
3. Be cautious about how path joins and path images are defined in your target system, as these concepts may have slightly different formalizations

---

## PATH_POLYGONAL_PATH

### PATH_POLYGONAL_PATH
- `PATH_POLYGONAL_PATH`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATH_POLYGONAL_PATH = prove
 (`!p:(real^N)list. path(polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; PATH_LINEPATH] THEN
  SIMP_TAC[PATH_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           NOT_CONS_NIL; HD; PATH_LINEPATH]);;
```

### Informal statement
For any list $p$ of vectors in $\mathbb{R}^N$, the function $\text{polygonal\_path}(p)$ is a path.

### Informal proof
The proof proceeds by induction on the structure of the list $p$.

* **Base case**: When $p = []$ (empty list), we have $\text{polygonal\_path}([]) = \text{linepath}(\vec{0}, \vec{0})$. Since `linepath` always defines a path (as per `PATH_LINEPATH`), the result holds.

* **Inductive cases**: 
  - When $p = [a]$ (single element), $\text{polygonal\_path}([a]) = \text{linepath}(a, a)$, which is a path.
  - When $p = [a, b]$ (two elements), $\text{polygonal\_path}([a, b]) = \text{linepath}(a, b)$, which is a path.
  - When $p = a::b::c::l$ (list with at least three elements), we have:
    $\text{polygonal\_path}(a::b::c::l) = \text{linepath}(a, b) \; ++ \; \text{polygonal\_path}(b::c::l)$
    
    By the induction hypothesis, $\text{polygonal\_path}(b::c::l)$ is a path. 
    We know $\text{linepath}(a, b)$ is a path from `PATH_LINEPATH`.
    
    For the join of two paths to be a path, the end point of the first path must equal the start point of the second path.
    Here, $\text{pathfinish}(\text{linepath}(a, b)) = b$ and $\text{pathstart}(\text{polygonal\_path}(b::c::l)) = b$ (from `PATHSTART_POLYGONAL_PATH`).
    
    Therefore, using `PATH_JOIN`, we conclude that $\text{polygonal\_path}(a::b::c::l)$ is a path.

In all cases, $\text{polygonal\_path}(p)$ forms a path, completing the proof.

### Mathematical insight
The theorem establishes that a polygonal path formed by connecting a sequence of points with straight line segments is a valid path in the topological sense. This is a fundamental result for many applications in topology and geometry, as polygonal paths are often used to approximate more complex paths or to define piecewise linear functions.

The result is intuitive: a polygonal path connects consecutive points in the list with line segments, and since line segments are continuous paths, their concatenation (when properly joined) is also a continuous path.

### Dependencies
- **Theorems**:
  - `PATH_LINEPATH`: Establishes that a line path between two points is a valid path
  - `PATH_JOIN`: Shows that joining two paths (where the end of the first equals the start of the second) results in a valid path
  - `PATHFINISH_LINEPATH`: Gives the end point of a line path
  - `PATHSTART_POLYGONAL_PATH`: Determines the starting point of a polygonal path

- **Definitions**:
  - `polygonal_path`: Defines a path formed by connecting points in a list with straight line segments

### Porting notes
When porting this theorem:
1. Ensure that the definition of `polygonal_path` is properly handled for the edge cases (empty list, singleton, etc.)
2. The theorem relies on path concatenation (the `++` operator), which should be properly defined in the target system
3. Consider how lists are handled in the target system, especially the pattern matching on list structures

---

## PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL

### PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL = prove
 (`!p. ~(p = [])
       ==> path_image(polygonal_path p) SUBSET convex hull (set_of_list p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[] THEN GEN_TAC THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL] THEN CONJ_TAC THENL
   [REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; set_of_list] THEN
    REWRITE_TAC[SEGMENT_REFL; CONVEX_HULL_SING] THEN SET_TAC[];
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path] THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH; set_of_list] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL; SUBSET_REFL];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_PATH_IMAGE_JOIN THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_CONVEX_HULL; set_of_list] THEN
      SIMP_TAC[HULL_MONO; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[set_of_list] THEN
      SET_TAC[]]]);;
```

### Informal statement
For any non-empty list of vectors $p$, the path image of the polygonal path formed by $p$ is a subset of the convex hull of the set of elements in $p$. In mathematical notation:

$$\forall p. p \neq [] \implies \text{path\_image}(\text{polygonal\_path}(p)) \subseteq \text{convex hull}(\text{set\_of\_list}(p))$$

where:
- $\text{path\_image}(P)$ is the set of all points on the path $P$
- $\text{polygonal\_path}(p)$ constructs a path connecting consecutive points in list $p$
- $\text{set\_of\_list}(p)$ converts list $p$ to a set
- $\text{convex hull}(S)$ is the smallest convex set containing $S$

### Informal proof
We prove this by induction on the structure of the list $p$.

**Base cases**:
- For $p = [a]$: 
  - The polygonal path is $\text{linepath}(a,a)$ which is just the point $a$ itself.
  - The path image is $\{a\}$.
  - The convex hull of $\{a\}$ is also $\{a\}$.
  - Therefore, $\text{path\_image}(\text{polygonal\_path}([a])) \subseteq \text{convex hull}(\{a\})$.

- For $p = [a,b]$:
  - The polygonal path is $\text{linepath}(a,b)$, which is the line segment from $a$ to $b$.
  - The path image is $\overline{ab}$ (the line segment between $a$ and $b$).
  - The convex hull of $\{a,b\}$ is exactly $\overline{ab}$.
  - Therefore, $\text{path\_image}(\text{polygonal\_path}([a,b])) \subseteq \text{convex hull}(\{a,b\})$.

**Inductive case**:
For $p = [a,b,c,...,l]$, where $l$ represents the rest of the list:
- By definition, $\text{polygonal\_path}([a,b,c,...,l]) = \text{linepath}(a,b) \cup \text{polygonal\_path}([b,c,...,l])$.
- The path image of this union is the union of the path images.
- The line segment from $a$ to $b$ is contained in the convex hull of $\{a,b\}$, which is contained in the convex hull of $\{a,b,c,...,l\}$.
- By the inductive hypothesis, $\text{path\_image}(\text{polygonal\_path}([b,c,...,l])) \subseteq \text{convex hull}(\{b,c,...,l\})$.
- Since $\{b,c,...,l\} \subseteq \{a,b,c,...,l\}$, and the convex hull operation is monotone, $\text{convex hull}(\{b,c,...,l\}) \subseteq \text{convex hull}(\{a,b,c,...,l\})$.
- Therefore, $\text{path\_image}(\text{polygonal\_path}([a,b,c,...,l])) \subseteq \text{convex hull}(\{a,b,c,...,l\})$.

### Mathematical insight
This theorem establishes a fundamental topological property of polygonal paths: they remain within the convex hull of their vertices. This is geometrically intuitive, as a polygonal path is made up of straight line segments between consecutive points, and each such segment must lie within the convex hull of its endpoints (which is itself contained in the convex hull of all points).

This result is useful for analyzing and constraining the behavior of polygonal paths in computational geometry, path planning algorithms, and when working with piecewise linear approximations of curves. It also serves as a foundational result for more complex theorems about polygonal paths and their properties.

### Dependencies
- Definitions:
  - `polygonal_path`: Recursively defines a path connecting consecutive points in a list
  - `path_image`: The set of all points on a path
  - `convex hull`: The smallest convex set containing a given set
  - `set_of_list`: Converts a list to a set
  - `linepath`: Creates a straight line path between two points

### Porting notes
When porting this theorem:
- Ensure that the definition of polygonal paths is consistent with the HOL Light definition, which uses path concatenation (`++`) to join consecutive line segments.
- The proof relies heavily on set-theoretic manipulations, which might require different tactics in other proof assistants.
- The handling of base cases (empty list, singleton list, two-element list) is explicit in HOL Light but might be handled differently in systems with more pattern matching capabilities.

---

## PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS

### Name of formal statement
PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS = prove
 (`!p x:real^N.
        arc(polygonal_path p) /\ 3 <= LENGTH p /\
        x IN path_image(polygonal_path p)
        ==> ?a b. MEM a p /\ MEM b p /\ x IN segment[a,b] /\
                  segment[a,b] SUBSET path_image(polygonal_path p) /\
                  ~(pathstart(polygonal_path p) IN segment[a,b] /\
                    pathfinish(polygonal_path p) IN segment[a,b])`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `c:real^N` THEN X_GEN_TAC `p:(real^N)list` THEN
  REPEAT DISCH_TAC THEN REWRITE_TAC[polygonal_path] THEN
  X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           ARC_JOIN_EQ; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH; ARC_LINEPATH] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNION] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[MEM; SUBSET_UNION; ENDS_IN_SEGMENT] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL] THEN
    DISCH_TAC THEN REWRITE_TAC[ARC_LINEPATH_EQ] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!p b. (s INTER p) SUBSET {b} /\
      x IN p /\ b IN s /\ ~(x = b)
      ==> ~(x IN s)`) THEN
    MAP_EVERY EXISTS_TAC
     [`path_image(polygonal_path (CONS (b:real^N) (CONS c p)))`;
      `b:real^N`] THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; PATHFINISH_IN_PATH_IMAGE];
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[ARITH_RULE `3 <= SUC(SUC p) <=> ~(p = 0)`] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN ASM_CASES_TAC `p:(real^N)list = []` THENL
     [ASM_REWRITE_TAC[LENGTH; polygonal_path] THEN
      REWRITE_TAC[PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      UNDISCH_TAC
       `x IN path_image(polygonal_path (CONS (b:real^N) (CONS c p)))` THEN
      ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH] THEN
      DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`b:real^N`; `c:real^N`] THEN
      ASM_REWRITE_TAC[MEM; SUBSET_UNION; ENDS_IN_SEGMENT] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[polygonal_path; PATH_IMAGE_LINEPATH] THEN
      REWRITE_TAC[ARC_LINEPATH_EQ] THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN SET_TAC[];
      ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^N` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N` THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[MEM];
        ASM_MESON_TAC[MEM];
        ASM_REWRITE_TAC[];
        ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `(sab INTER p) SUBSET {b}
          ==> !sde a. sde SUBSET p /\
              ~(b IN sde) /\ d IN sde /\ a IN sde /\ a IN sab
              ==> F`) o el 2 o CONJUNCTS) THEN
        MAP_EVERY EXISTS_TAC [`segment[d:real^N,e]`; `a:real^N`] THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]]]]);;
```

### Informal statement
For any list $p$ of points in $\mathbb{R}^N$ and any point $x \in \mathbb{R}^N$, if the polygonal path defined by $p$ forms an arc, the list has at least 3 elements, and $x$ is in the image of this polygonal path, then there exist points $a$ and $b$ in $p$ such that:
- $x$ lies on the line segment between $a$ and $b$
- The entire segment $[a,b]$ is contained in the path image of the polygonal path
- It is not the case that both the start point and end point of the polygonal path lie on the segment $[a,b]$

### Informal proof
The proof proceeds by induction on the list structure of $p$:

1. We use list induction three times to handle the base cases for lists with fewer than 3 elements, which are trivially true due to the assumption requiring $\text{LENGTH}(p) \geq 3$.

2. For the inductive case, we consider a list of the form $[a, b, c] \oplus p'$ where $\oplus$ denotes concatenation.
   
3. We rewrite the polygonal path as the join of the line segment from $a$ to $b$ and the polygonal path starting at $b$ through the rest of the points.

4. For a point $x$ in the path image, we have two cases based on whether $x$ is in the first line segment or the rest of the path:

   * **Case 1**: If $x$ is in the line segment $[a,b]$:
     - We set $a$ and $b$ as our witnesses.
     - This segment satisfies our requirements because:
       - Both $a$ and $b$ are members of the original list $p$.
       - The segment $[a,b]$ is part of the path image.
       - Using the arc property, we prove that the start and end points of the full path cannot both be in $[a,b]$.

   * **Case 2**: If $x$ is in the rest of the path:
     - We apply the induction hypothesis to the shorter list.
     - A special subcase is handled when $p$ is empty (so we have just $[a,b,c]$).
     - For non-empty $p$, we use the induction hypothesis to find points $d$ and $e$ with the desired properties and show that they work for the extended path as well.

5. The proof relies on properties of arcs, particularly that distinct points on the path cannot be connected directly by a line segment unless that segment is part of the original path.

### Mathematical insight
This theorem captures an important property of polygonal paths: any point on a polygonal path must lie on one of the line segments between consecutive vertices, and furthermore, we can find such a segment that doesn't contain both endpoints of the path.

This result is useful when analyzing the structure of polygonal paths and is particularly relevant for computational geometry and topology. The condition that the segment doesn't contain both endpoints ensures that the path doesn't "double back" on itself in certain ways, which is a characteristic of arcs (simple curves without self-intersections).

The requirement of at least 3 points is necessary as paths with only 1 or 2 points are degenerate cases where the entire path might be a single line segment containing both endpoints.

### Dependencies
- Theorems:
  - `PATHSTART_POLYGONAL_PATH`: Determines the starting point of a polygonal path
- Definitions:
  - `polygonal_path`: Defines a path composed of connected line segments

### Porting notes
When porting this theorem:
1. Be aware of how polygonal paths are defined in the target system - especially the handling of edge cases like empty or singleton lists.
2. Ensure the target system has corresponding definitions of arcs, path images, and line segments.
3. The proof uses set-theoretic reasoning extensively, so you'll need good set operation support in the target system.
4. The nested induction structure might need to be reformulated based on the induction capabilities of the target system.

---

## SET_OF_LIST_POLYGONAL_PATH_ROTATE

### Name of formal statement
SET_OF_LIST_POLYGONAL_PATH_ROTATE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SET_OF_LIST_POLYGONAL_PATH_ROTATE = prove
 (`!p. ~(p = []) ==> set_of_list(CONS (LAST p) (BUTLAST p)) = set_of_list p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
  REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN SET_TAC[]);;
```

### Informal statement
For any list `p`, if `p` is not empty, then the set of elements in the list formed by putting the last element of `p` at the front and removing the last element from the original list (i.e., `CONS (LAST p) (BUTLAST p)`) is equal to the set of elements in the original list `p`.

Formally:
$$\forall p. p \neq [] \Rightarrow \text{set\_of\_list}(\text{CONS}(\text{LAST}(p), \text{BUTLAST}(p))) = \text{set\_of\_list}(p)$$

### Informal proof
We need to show that rotating the list by moving the last element to the front preserves the set of elements.

* First, we apply the theorem `APPEND_BUTLAST_LAST` which states that for a non-empty list `p`, we have `p = APPEND (BUTLAST p) [LAST p]`.
* Using this, we rewrite the right side of our goal.
* Then we use the property `SET_OF_LIST_APPEND` which states that `set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)`.
* Finally, we apply basic set theory reasoning to show that the sets are equal, since we're just rearranging the same elements.

### Mathematical insight
This theorem demonstrates an important property about set representations of lists: the ordering of elements in a list doesn't affect the resulting set. Specifically, it shows that rotating a list by moving its last element to the front position (which can be useful in polygon traversals or cyclic structures) preserves the set of elements.

This result is particularly useful when working with polygonal paths or cycles where we may want to start from different vertices while maintaining the same set of vertices. The comment suggests this theorem is used for "rotating the starting point to move a preferred vertex forward," which is a common operation in geometric algorithms and computational geometry.

### Dependencies
- `APPEND_BUTLAST_LAST`: Theorem relating a non-empty list to appending its BUTLAST with its LAST element
- `SET_OF_LIST_APPEND`: Theorem about the set of elements in an appended list
- `set_of_list`: Definition converting a list to its corresponding set

### Porting notes
When porting this theorem:
- Ensure that the target system has equivalent functions for `LAST`, `BUTLAST`, `CONS`, and `APPEND`
- The `SET_TAC` tactic is used for basic set theory reasoning; you may need to replace this with appropriate set theory tactics in your target system
- The theorem relies on the definition of `set_of_list` which converts a list to a set; ensure this is properly defined in your target system

---

## PROPERTIES_POLYGONAL_PATH_SNOC

### PROPERTIES_POLYGONAL_PATH_SNOC
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PROPERTIES_POLYGONAL_PATH_SNOC = prove
 (`!p d:real^N.
        2 <= LENGTH p
        ==> path_image(polygonal_path(APPEND p [d])) =
            path_image(polygonal_path p ++ linepath(LAST p,d)) /\
            (arc(polygonal_path(APPEND p [d])) <=>
             arc(polygonal_path p ++ linepath(LAST p,d))) /\
            (simple_path(polygonal_path(APPEND p [d])) <=>
             simple_path(polygonal_path p ++ linepath(LAST p,d)))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; ARITH] THEN X_GEN_TAC `b:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[APPEND; polygonal_path; LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN REPEAT DISCH_TAC THEN
  X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN REWRITE_TAC[APPEND] THEN
  ONCE_REWRITE_TAC[LAST] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  ONCE_REWRITE_TAC[polygonal_path] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[APPEND; LENGTH; ARITH_RULE `2 <= SUC(SUC n)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SIMP_TAC[GSYM ARC_ASSOC; GSYM SIMPLE_PATH_ASSOC; PATHSTART_JOIN;
           PATHFINISH_JOIN; PATHSTART_POLYGONAL_PATH;
           PATHFINISH_POLYGONAL_PATH;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
           PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
           PATHSTART_LINEPATH; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD] THEN
    REWRITE_TAC[UNION_ACI];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = d` THENL
   [MATCH_MP_TAC(TAUT
     `(~p /\ ~p') /\ (q <=> q') ==> (p <=> p') /\ (q <=> q')`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARC_SIMPLE_PATH; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      ASM_REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; NOT_CONS_NIL; LAST;
                      APPEND_EQ_NIL; LAST_APPEND];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_JOIN_LOOP_EQ o
     lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; PATHSTART_LINEPATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_JOIN_LOOP_EQ o
     rhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                  PATHFINISH_POLYGONAL_PATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
    MATCH_MP_TAC(TAUT
     `((q <=> p) /\ (q' <=> p')) /\ (p <=> p')
      ==> (p <=> p') /\ (q <=> q')`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC SIMPLE_PATH_EQ_ARC THEN
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                  PATHFINISH_POLYGONAL_PATH] THEN
      ASM_REWRITE_TAC[NOT_CONS_NIL; HD; LAST; LAST_APPEND; APPEND_EQ_NIL];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) ARC_JOIN_EQ o lhs o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[NOT_CONS_NIL; HD];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) ARC_JOIN_EQ o rhs o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_LINEPATH; PATHSTART_JOIN;
               NOT_CONS_NIL; HD];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]]);;
```

### Informal statement
For any list of vectors $p$ in $\mathbb{R}^N$ with length at least 2, and any vector $d \in \mathbb{R}^N$, the following properties hold when appending $d$ to $p$:

1. The path image of the polygonal path formed by appending $d$ to $p$ equals the path image of the join of the polygonal path formed by $p$ and the line segment from the last point of $p$ to $d$:
   $$\text{path\_image}(\text{polygonal\_path}(p \cdot [d])) = \text{path\_image}(\text{polygonal\_path}(p) \frown \text{linepath}(\text{LAST}(p), d))$$

2. The polygonal path formed by appending $d$ to $p$ is an arc if and only if the join of the polygonal path formed by $p$ and the line segment from the last point of $p$ to $d$ is an arc:
   $$\text{arc}(\text{polygonal\_path}(p \cdot [d])) \iff \text{arc}(\text{polygonal\_path}(p) \frown \text{linepath}(\text{LAST}(p), d))$$

3. The polygonal path formed by appending $d$ to $p$ is a simple path if and only if the join of the polygonal path formed by $p$ and the line segment from the last point of $p$ to $d$ is a simple path:
   $$\text{simple\_path}(\text{polygonal\_path}(p \cdot [d])) \iff \text{simple\_path}(\text{polygonal\_path}(p) \frown \text{linepath}(\text{LAST}(p), d))$$

### Informal proof
We prove the theorem by induction on the list $p$.

* Base case: Since we require $p$ to have length at least 2, we consider cases where $p$ has the form $[a, b]$ for vectors $a$ and $b$. For these cases, we have:
  $$\text{polygonal\_path}([a, b] \cdot [d]) = \text{polygonal\_path}([a, b, d]) = \text{linepath}(a, b) \frown \text{linepath}(b, d)$$

* Inductive step: Assume the result holds for a list of the form $[b, c] \cdot p'$. We show it holds for $[a, b, c] \cdot p'$.
  
* For a list beginning with $a, b, c$ followed by $p$, we need to show the properties hold when appending $d$.
  
* We use the recursive definition of `polygonal_path` to rewrite the polygonal path of the extended list in terms of a join operation.

* For the path image equality, we apply the property that the path image of a joined path is the union of the path images of the component paths.

* For the arc and simple path properties, we consider two cases:
  
  1. If $a = d$ (creating a potential loop), both paths fail to be arcs because they form loops, but the simple path equivalence holds based on whether the original path is simple.
  
  2. If $a \neq d$, we use the fact that the arc property holds for a join of paths when certain conditions on endpoints are met, and similarly for the simple path property.

* We use properties of path start and finish points, particularly that:
  - $\text{pathstart}(\text{polygonal\_path}(p)) = \text{HD}(p)$ when $p$ is non-empty
  - $\text{pathfinish}(\text{polygonal\_path}(p)) = \text{LAST}(p)$ when $p$ is non-empty

* By applying these properties along with the inductive hypothesis, we establish all three claims.

### Mathematical insight
This theorem establishes the equivalence between two ways of extending a polygonal path: either by directly appending a new point to the list defining the path, or by joining the original polygonal path with a line segment to the new point. This is a fundamental property for manipulating polygonal paths in geometric calculations.

The result is particularly useful because it shows that key properties like being an arc (having no self-intersections and distinct endpoints) or being a simple path (having no self-intersections) are preserved between these two representations. This allows flexible manipulation of polygonal paths while preserving their topological properties.

The theorem helps simplify proofs about polygonal paths by allowing the use of the more convenient representation depending on the situation.

### Dependencies
- **Theorems**:
  - `PATHSTART_POLYGONAL_PATH`: Defines the starting point of a polygonal path
  - `PATHFINISH_POLYGONAL_PATH`: Defines the ending point of a polygonal path
  - Various implicit theorems about `ARC_JOIN_EQ`, `SIMPLE_PATH_JOIN_LOOP_EQ`, `PATH_IMAGE_JOIN`

- **Definitions**:
  - `polygonal_path`: Recursively defines a path formed by connecting a sequence of points with straight lines

### Porting notes
When porting this theorem:
1. Ensure the definition of `polygonal_path` is correctly implemented, especially its recursive nature
2. Watch for different handling of path joins (`++` in HOL Light) in other systems
3. The proof relies heavily on path start/finish behavior, so ensure these concepts are compatible in the target system
4. The case analysis on whether $a = d$ forms a loop is critical for correctly handling the arc and simple path properties

---

## PATH_IMAGE_POLYGONAL_PATH_ROTATE

### PATH_IMAGE_POLYGONAL_PATH_ROTATE
- path_image_polygonal_path_rotate

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PATH_IMAGE_POLYGONAL_PATH_ROTATE = prove
 (`!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> path_image(polygonal_path(APPEND (TL p) [HD(TL p)])) =
            path_image(polygonal_path p)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[HD; TL] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAST; APPEND; NOT_CONS_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[GSYM LAST] THEN
  DISCH_TAC THEN
  SIMP_TAC[PROPERTIES_POLYGONAL_PATH_SNOC; LENGTH;
           ARITH_RULE `2 <= SUC(SUC n)`] THEN
  ONCE_REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [polygonal_path] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST]) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
           PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
           LAST; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[UNION_ACI]);;
```

### Informal statement
For any list $p$ of vectors in $\mathbb{R}^N$ with length at least 2, if the last element equals the first element (i.e., $\text{LAST}(p) = \text{HD}(p)$), then the path image of the polygonal path formed by appending the second element to the tail of $p$ is equal to the path image of the polygonal path formed by $p$. 

That is, if $|p| \geq 2$ and $p[|p|-1] = p[0]$, then:
$$\text{path\_image}(\text{polygonal\_path}(\text{APPEND}(\text{TL}(p), [\text{HD}(\text{TL}(p))]))) = \text{path\_image}(\text{polygonal\_path}(p))$$

### Informal proof
We proceed by induction on lists.

First, we handle the case where the list has less than 2 elements:
- For the empty list, the length condition $2 \leq \text{LENGTH}(p)$ is false.
- For a singleton list $[a]$, the length condition is also false.

Next, we consider a list with exactly two elements $[a,b]$:
- If $\text{LAST}([a,b]) = \text{HD}([a,b])$, then $b = a$.
- The conclusion requires comparing $\text{path\_image}(\text{polygonal\_path}(\text{APPEND}([b], [b])))$ with $\text{path\_image}(\text{polygonal\_path}([a,b]))$.
- But this case is handled directly through the rewriting and simplification.

For the inductive case, consider a list $[a,b,c] \cdot p$ where $p$ is some remaining list:
- We need to show that if $\text{LAST}([a,b,c] \cdot p) = a$, then the path images are equal.
- Using the theorem `PROPERTIES_POLYGONAL_PATH_SNOC`, we relate the path image of a polygonal path with an appended element to the path image of the joined path.
- We utilize the properties of `pathstart` and `pathfinish` functions to establish connections between different segments of our polygonal paths.
- The path images are shown to be equal through set-theoretic equality of unions (using `UNION_ACI`).

### Mathematical insight
This theorem demonstrates a fundamental property of polygonal paths that start and end at the same point (closed polygonal paths). It shows that rotating the sequence of points that define such a path - by removing the first point and appending a copy of the second point at the end - does not change the geometric shape of the path.

This property is important in computational geometry and for working with closed paths or polygons. It confirms that the path image (the set of points traversed by the path) remains invariant under this specific rotation operation on the defining sequence of points.

The result is particularly useful when manipulating polygonal paths and wanting to ensure that certain transformations of the sequence preserve the geometric object represented.

### Dependencies
- **Theorems**:
  - `PATHSTART_POLYGONAL_PATH`: Defines the starting point of a polygonal path
  - `PATHFINISH_POLYGONAL_PATH`: Defines the ending point of a polygonal path
  - `PROPERTIES_POLYGONAL_PATH_SNOC`: Relates properties of a polygonal path with an appended element

- **Definitions**:
  - `polygonal_path`: Recursive definition of a polygonal path from a list of points

### Porting notes
- When implementing this in other systems, careful attention should be paid to the treatment of empty and singleton lists in the definition of `polygonal_path`.
- The proof relies heavily on the properties of list operations (`HD`, `TL`, `LAST`, `APPEND`), which might have different definitions or behaviors in other systems.
- The path image concept may need to be explicitly defined in other systems if not available.

---

## SIMPLE_PATH_POLYGONAL_PATH_ROTATE

### SIMPLE_PATH_POLYGONAL_PATH_ROTATE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let SIMPLE_PATH_POLYGONAL_PATH_ROTATE = prove
 (`!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> (simple_path(polygonal_path(APPEND (TL p) [HD(TL p)])) =
             simple_path(polygonal_path p))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b:real^N` THEN REWRITE_TAC[HD; TL] THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN CONJ_TAC THENL
   [REWRITE_TAC[LAST; APPEND; NOT_CONS_NIL] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `p:(real^N)list`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL] THEN ONCE_REWRITE_TAC[GSYM LAST] THEN
  DISCH_TAC THEN
  SIMP_TAC[PROPERTIES_POLYGONAL_PATH_SNOC; LENGTH;
           ARITH_RULE `2 <= SUC(SUC n)`] THEN
  ONCE_REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [polygonal_path] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST]) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
               PATHFINISH_POLYGONAL_PATH; LAST; NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[INSERT_AC; INTER_ACI; CONJ_ACI]);;
```

### Informal statement
For any list of points $p$ in $\mathbb{R}^N$, if the length of $p$ is at least 2 and the last element equals the first element (i.e., $\text{LAST}(p) = \text{HD}(p)$), then the polygonal path formed by appending the second element to the tail of $p$ is a simple path if and only if the original polygonal path is a simple path. Symbolically:

$$\forall p \in (\mathbb{R}^N)^{\text{list}}. \left(2 \leq \text{LENGTH}(p) \land \text{LAST}(p) = \text{HD}(p)\right) \Rightarrow \left(\text{simple\_path}(\text{polygonal\_path}(\text{APPEND}(\text{TL}(p), [\text{HD}(\text{TL}(p))])) = \text{simple\_path}(\text{polygonal\_path}(p))\right)$$

### Informal proof
The proof proceeds by induction on the list structure:

1. Base cases with empty or singleton lists are easily handled through the LENGTH condition as they don't satisfy the premise.

2. For the case with two elements, we manipulate the structure directly.

3. For the inductive case where $p = [a, b, c, \ldots]$:
   - We use the fact that $\text{LAST}(p) = a$ from our premise.
   - Apply `PROPERTIES_POLYGONAL_PATH_SNOC` to relate the polygonal path created by appending a point to the end of a list to a joined path.
   - Observe that for both polygonal paths under consideration, they form loops back to their starting points.
   - The theorem `SIMPLE_PATH_JOIN_LOOP_EQ` allows us to establish that both paths are simple if the underlying path segments don't self-intersect.
   - The paths are structurally equivalent with respect to whether they are simple, which completes the proof.

### Mathematical insight
This theorem establishes an invariant property of simple polygonal paths under rotation of their sequence of vertices. It demonstrates that when working with a closed polygonal path (one that starts and ends at the same point), rotating the vertex list by removing the first point and placing the second point at the end preserves the property of being a simple path.

This is intuitively expected: if a path doesn't cross itself, then starting the traversal at a different vertex shouldn't change this fact. This result is useful in computational geometry, graph theory, and when working with polygons, as it allows flexibility in the representation of closed paths without affecting their fundamental topological properties.

### Dependencies
- Theorems:
  - `PATHSTART_POLYGONAL_PATH`: Defines the starting point of a polygonal path.
  - `PATHFINISH_POLYGONAL_PATH`: Defines the ending point of a polygonal path.
  - `PROPERTIES_POLYGONAL_PATH_SNOC`: Relates properties of a polygonal path when a point is appended.
  - `SIMPLE_PATH_JOIN_LOOP_EQ`: Determines when a joined path that forms a loop is simple.

- Definitions:
  - `polygonal_path`: A path formed by connecting consecutive points in a list with straight line segments.

### Porting notes
When porting this theorem:
1. Ensure that your target system has equivalent notions of polygonal paths, simple paths, and list operations.
2. The proof relies on specific theorems about path properties that must be available or established first.
3. The induction on list structure is a common pattern, but the handling of different list cases may need adjustment depending on how lists and pattern matching work in your target system.
4. Path joining operations (represented by `++` in HOL Light) must have equivalent semantics in the target system.

---

## ROTATE_LIST_TO_FRONT_1

### ROTATE_LIST_TO_FRONT_1
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ROTATE_LIST_TO_FRONT_1 = prove
 (`!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. EL 1 l' = a /\ P l'`,
  let lemma0 = prove
     (`!P. (!i. P i /\ 0 < i ==> P(i - 1)) /\ (?k. 0 < k /\ P k)
             ==> P 1`,
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `!i:num. i < k ==> P(k - i)` MP_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_0] THEN DISCH_TAC THEN
        REWRITE_TAC[ARITH_RULE `k - SUC i = k - i - 1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        CONJ_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC;
        DISCH_THEN(MP_TAC o SPEC `k - 1`) THEN
        ASM_SIMP_TAC[ARITH_RULE `0 < k ==> k - 1 < k /\ k - (k - 1) = 1`]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?i l'. 0 < i /\ i < LENGTH l' /\ P l' /\ EL i l' = (a:A)`
  MP_TAC THENL
   [SUBGOAL_THEN `~(l:A list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH; ARITH_RULE `~(3 <= 0)`]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MEM_EXISTS_EL]) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC (ARITH_RULE `i = 0 \/ 0 < i`)
    THENL
     [EXISTS_TAC `LENGTH(l:A list) - 2` THEN
      EXISTS_TAC `(APPEND (TL l) [HD(TL l):A])` THEN
      ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TL; EL_APPEND] THEN
      REWRITE_TAC[LT_REFL; LENGTH; SUB_REFL; EL; HD] THEN
      SUBGOAL_THEN `3 <= LENGTH(l:A list)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[ARITH_RULE `3 <= n ==> n - 2 < n - 1`] THEN
      ASM_SIMP_TAC[EL_TL; ARITH_RULE `3 <= n ==> n - 2 + 1 = n - 1`] THEN
      ASM_MESON_TAC[LAST_EL];
      MAP_EVERY EXISTS_TAC [`i:num`; `l:A list`] THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT] lemma0)) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:A list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `APPEND (TL m) [HD(TL m):A]` THEN
    SUBGOAL_THEN `~(m:A list = [])` ASSUME_TAC THENL
     [ASM_MESON_TAC[LENGTH; ARITH_RULE `~(3 <= 0)`]; ALL_TAC] THEN
    ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_TL; EL_APPEND] THEN
    ASM_REWRITE_TAC[LENGTH] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    ASM_SIMP_TAC[EL_TL; ARITH_RULE `0 < k ==> k - 1 + 1 = k`]]);;
```

### Informal statement
For any predicate $P$ over lists, list $l$, and element $a$ of type $A$, if:
1. For any list $l$, if $P(l)$ is true then the length of $l$ is at least 3 and the last element equals the head element
2. For any list $l$, if $P(l)$ is true then $P(\textrm{APPEND}(\textrm{TL}(l), [\textrm{HD}(\textrm{TL}(l))])$ is also true
3. $P(l)$ is true and $a$ is a member of $l$

Then there exists a list $l'$ such that the element at index 1 (the second element) of $l'$ is $a$ and $P(l')$ is true.

### Informal proof
The proof involves showing that if an element appears in a list satisfying property $P$, then we can rotate the list until that element appears in the second position.

First, a lemma is proven:
- **Lemma 0**: If $P$ is a predicate on natural numbers such that:
  - For all $i > 0$, if $P(i)$ is true then $P(i-1)$ is also true
  - There exists some $k > 0$ such that $P(k)$ is true
  
  Then $P(1)$ is true.
  
  This lemma is proven by induction on $i$, showing that $P(k-i)$ holds for all $i < k$, which implies $P(1)$ when $i = k-1$.

For the main proof:
- First, we establish there exists an index $i > 0$ and a list $l'$ satisfying $P$ such that element $a$ appears at index $i$ in $l'$.
- We consider two cases:
  - If $a$ is at index 0 (the head element) of $l$, we can rotate the list once to get a new list $l'$ where $a$ appears at index $LENGTH(l) - 2$. We use the fact that the last element equals the head element, so after rotation, the new list still satisfies $P$.
  - If $a$ is already at a positive index $i$ in $l$, we keep $l' = l$.

- Then we use Lemma 0 to show that we can repeatedly rotate the list until element $a$ appears at index 1.
- Each rotation brings us closer to having $a$ at index 1, and property $P$ is preserved by each rotation according to our second assumption.

The proof concludes by showing that after an appropriate number of rotations, $a$ will appear at index 1 in a list that still satisfies property $P$.

### Mathematical insight
This theorem is useful for operations on cyclic lists or structures where elements can be rotated while preserving certain properties. The key insight is that for lists satisfying a predicate $P$ with the given constraints, any element in the list can be "promoted" to the second position through repeated rotations.

The theorem essentially proves that given a circular list structure (implied by the requirement that the head and last elements are equal) with certain invariants preserved under rotation, we can always position any element from the list at the second position.

This may be useful in algorithms or systems that need to operate on each element of a circular list in turn, while maintaining specific structural properties.

### Dependencies
- Lemma0: A helper lemma for inductive reasoning about predicates on natural numbers

### Porting notes
When porting this theorem to another system:
1. Consider how the list operations (APPEND, TL, HD, EL, MEM, LENGTH) are defined in the target system
2. Pay attention to zero-based vs. one-based indexing - HOL Light uses zero-based indexing, so EL 1 refers to the second element
3. The theorem relies on reasoning about rotation operations on lists that preserve certain properties, so ensure the target system has adequate list manipulation capabilities

---

## ROTATE_LIST_TO_FRONT_0

### Name of formal statement
ROTATE_LIST_TO_FRONT_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ROTATE_LIST_TO_FRONT_0 = prove
 (`!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. HD l' = a /\ P l'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`P:A list->bool`; `l:A list`; `a:A`]
    ROTATE_LIST_TO_FRONT_1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `l':A list` THEN
  STRIP_TAC THEN EXISTS_TAC `APPEND (TL l') [HD(TL l'):A]` THEN
  ASM_SIMP_TAC[] THEN UNDISCH_TAC `EL 1 l' = (a:A)` THEN
  SUBGOAL_THEN `3 <= LENGTH(l':A list)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SPEC_TAC(`l':A list`,`p:A list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  REWRITE_TAC[APPEND; HD; TL; num_CONV `1`; EL]);;
```

### Informal statement
For any predicate $P$ on lists, any list $l$, and any element $a$ of type $A$, if:
1. For all lists $l$, if $P(l)$ holds, then the length of $l$ is at least 3 and the last element of $l$ equals the head (first element) of $l$,
2. For all lists $l$, if $P(l)$ holds, then $P(\text{APPEND}(\text{TL}(l), [\text{HD}(\text{TL}(l))]))$ also holds (where APPEND concatenates lists, TL takes the tail of a list, and HD takes the head of a list), and
3. $P(l)$ holds and $a$ is a member of $l$,

then there exists a list $l'$ such that the head of $l'$ is $a$ and $P(l')$ holds.

### Informal proof
This theorem is proved by applying a related theorem `ROTATE_LIST_TO_FRONT_1`, which states that under the same conditions, there exists a list $l'$ such that the second element of $l'$ is $a$ and $P(l')$ holds.

The proof proceeds as follows:

* Begin by applying `ROTATE_LIST_TO_FRONT_1` to the same predicates and values.
* This gives us a list $l'$ where $\text{EL}(1, l') = a$ (i.e., the second element is $a$) and $P(l')$ holds.
* We then construct a new list $\text{APPEND}(\text{TL}(l'), [\text{HD}(\text{TL}(l'))])$, which effectively rotates $l'$ once.
* From the second hypothesis, we know $P$ holds for this rotated list.
* We need to show that $a$ is the head of this rotated list.
* Since $P(l')$ holds, we know $l'$ has length at least 3.
* By expanding the definition of $\text{EL}(1, l')$ and the construction of the rotated list, we can show that the head of our constructed list is indeed $a$.

### Mathematical insight
This theorem relates to the concept of rotating a cyclic list to bring a specific element to the front. A key insight is that if we have a predicate $P$ that is preserved under a specific rotation operation (appending the tail of a list with the singleton list containing the second element), and if $P$ guarantees that the list is circular (last element equals first element), then we can rotate any element to the front while preserving the predicate.

The theorem effectively shows that for lists satisfying these properties, any element in the list can be made the head of another valid list. This might be useful in scenarios involving cyclic structures or when we need to view the same circular list from different starting points.

### Dependencies
- Theorems:
  - `ROTATE_LIST_TO_FRONT_1`: A related theorem stating that under the same conditions, we can find a list where the second element is a specific element from the original list.

### Porting notes
- The proof relies on list manipulation operations like HD, TL, APPEND, and EL, which have direct equivalents in most proof assistants.
- The theorem works with circular lists (where the last element equals the first), which may require specific handling in other systems.
- The proof's approach of first rotating the element to position 1 and then rotating the whole list to bring that element to position 0 might need to be adapted based on the list manipulation tactics available in the target system.

---

## DISTINGUISHING_ROTATION_EXISTS_PAIR

### Name of formal statement
DISTINGUISHING_ROTATION_EXISTS_PAIR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISTINGUISHING_ROTATION_EXISTS_PAIR = prove
 (`!x y. ~(x = y)
         ==> FINITE {t | &0 <= t /\ t < &2 * pi /\
                         (rotate2d t x)$2 = (rotate2d t y)$2}`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  ONCE_REWRITE_TAC[GSYM ROTATE2D_SUB] THEN
  REWRITE_TAC[GSYM IM_DEF; GSYM real; GSYM ARG_EQ_0_PI] THEN
  REWRITE_TAC[FINITE_UNION; SET_RULE
   `{x | p x /\ q x /\ (r x \/ s x)} =
    {x | p x /\ q x /\ r x} UNION {x | p x /\ q x /\ s x}`] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(MESON[FINITE_SING; FINITE_SUBSET]
       `(?a. s SUBSET {a}) ==> FINITE s`) THEN
  MATCH_MP_TAC(SET_RULE
   `(!x y. x IN s /\ y IN s ==> x = y) ==> ?a. s SUBSET {a}`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ARG_ROTATE2D_UNIQUE_2PI THEN EXISTS_TAC `x - y:complex` THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_0]);;
```

### Informal statement
For any two distinct points $x$ and $y$ in $\mathbb{R}^2$, the set of angles $t$ where $0 \leq t < 2\pi$ such that the second component (y-coordinate) of the rotated point $\text{rotate2d}(t, x)$ equals the second component of the rotated point $\text{rotate2d}(t, y)$ is finite.

In mathematical notation:
$$\forall x, y \in \mathbb{R}^2, x \neq y \Rightarrow \text{FINITE}\{t \mid 0 \leq t < 2\pi \text{ and } (\text{rotate2d}(t, x))_2 = (\text{rotate2d}(t, y))_2\}$$

where $\text{rotate2d}(t, p)$ represents the point $p$ rotated counterclockwise by angle $t$, and the subscript $2$ indicates the second (y) component of the vector.

### Informal proof
The proof proceeds as follows:

- We first rewrite the condition $(\text{rotate2d}(t, x))_2 = (\text{rotate2d}(t, y))_2$ as $(\text{rotate2d}(t, x))_2 - (\text{rotate2d}(t, y))_2 = 0$.
- This is then rewritten as $(\text{rotate2d}(t, x-y))_2 = 0$ using the linearity of rotation.
- We use the connection between 2D rotations and complex numbers, where the second component corresponds to the imaginary part.
- The condition becomes equivalent to: $\text{Im}(\text{rotate2d}(t, x-y)) = 0$, which means the rotated vector $x-y$ is either on the positive or negative real axis.
- This occurs precisely when the argument (polar angle) of the rotated complex number $\text{rotate2d}(t, x-y)$ is either $0$ or $\pi$.
- By properties of rotation in the complex plane, the set of angles $t$ where this happens has at most 2 values in the range $[0, 2\pi)$.
- Therefore, the set is finite, which completes the proof.

### Mathematical insight
This theorem establishes that for any two distinct points in the plane, there are only finitely many rotation angles (in fact, at most two) at which the points have the same y-coordinate after rotation. This is a key geometric result used in computational geometry algorithms.

The insight behind this theorem is that as we rotate two distinct points around the origin, their y-coordinates generally differ except at specific critical angles. These critical angles occur precisely when the vector connecting the two points becomes horizontal after rotation.

This result is particularly useful for algorithms that need to distinguish points by their coordinates, as it guarantees we can almost always find a rotation that makes all y-coordinates distinct.

### Dependencies
- `ROTATE2D_SUB`: States that rotation distributes over vector subtraction.
- `IM_DEF`: Defines the imaginary part of a complex number.
- `real`: Relates real numbers and complex numbers.
- `ARG_EQ_0_PI`: Characterizes when a complex number has argument 0 or π.
- `ARG_ROTATE2D_UNIQUE_2PI`: States that angles of rotation are unique modulo 2π.
- `VECTOR_SUB_COMPONENT`: Relates vector subtraction to component-wise subtraction.

### Porting notes
When implementing this theorem in other proof assistants:
- Ensure the coordinate system and rotation direction are consistent with HOL Light's implementation.
- The proof relies on the connection between 2D rotations and complex numbers, which might require establishing in systems that don't have this built-in.
- The finiteness argument depends on uniqueness properties of the argument function for complex numbers, which might need explicit formalization in some systems.

---

## DISTINGUISHING_ROTATION_EXISTS

### Name of formal statement
DISTINGUISHING_ROTATION_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISTINGUISHING_ROTATION_EXISTS = prove
 (`!s. FINITE s ==> ?t. pairwise (\x y. ~(x$2 = y$2)) (IMAGE (rotate2d t) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `INFINITE ({t | &0 <= t /\ t < &2 * pi} DIFF
              UNIONS (IMAGE (\(x,y). {t | &0 <= t /\ t < &2 * pi /\
                                          (rotate2d t x)$2 = (rotate2d t y)$2})
                            ({(x,y) | x IN s /\ y IN s /\ ~(x = y)})))`
  MP_TAC THENL
   [MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
    REWRITE_TAC[INFINITE; FINITE_REAL_INTERVAL; REAL_NOT_LE] THEN
    CONJ_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{(x:real^2,y:real^2) | x IN s /\ y IN s}` THEN
      ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[DISTINGUISHING_ROTATION_EXISTS_PAIR]];
    DISCH_THEN(MP_TAC o MATCH_MP (MESON[FINITE_EMPTY; INFINITE]
     `INFINITE s ==> ~(s = {})`)) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[UNIONS_IMAGE; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[pairwise; IN_ELIM_THM] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[ROTATE2D_EQ] THEN MESON_TAC[]]);;
```

### Informal statement
For any finite set $s$ of points in the plane (represented as vectors in $\mathbb{R}^2$), there exists an angle $t$ such that when we rotate all points in $s$ by $t$ radians around the origin, no two distinct rotated points have the same $y$-coordinate.

Formally, $\forall s. \text{FINITE}(s) \Rightarrow \exists t. \text{pairwise}(\lambda x~y. \neg(x_2 = y_2))(\text{IMAGE}(\text{rotate2d}~t)~s)$, where:
- $\text{rotate2d}~t$ is the function that rotates points in the plane by $t$ radians
- $x_2$ denotes the second component (y-coordinate) of vector $x$
- $\text{pairwise}~P~S$ means that predicate $P$ holds for any two distinct elements of set $S$

### Informal proof
The proof shows that we can find a rotation angle that makes all y-coordinates distinct.

1. We first construct the set of "bad" rotation angles - those where some pair of distinct points would have the same y-coordinate after rotation.

2. For each pair of distinct points $(x,y)$ in $s$, we consider the set:
   $\{t \mid 0 \leq t < 2\pi \text{ and } (\text{rotate2d}~t~x)_2 = (\text{rotate2d}~t~y)_2\}$
   
   This represents angles where points $x$ and $y$ would have the same y-coordinate after rotation.

3. The key insight is that for any pair of distinct points, this set of "bad" angles is finite (from the dependency `DISTINGUISHING_ROTATION_EXISTS_PAIR`).

4. We prove that the set of "good" angles:
   $\{t \mid 0 \leq t < 2\pi\} \setminus \bigcup_{(x,y) \in s \times s, x \neq y} \{t \mid 0 \leq t < 2\pi \text{ and } (\text{rotate2d}~t~x)_2 = (\text{rotate2d}~t~y)_2\}$
   is infinite.

5. This follows because:
   - The interval $[0, 2\pi)$ is infinite
   - We're removing only a finite union of finite sets (the "bad" angles)
   - The difference between an infinite set and a finite set is infinite

6. Therefore, there must exist at least one angle $t$ in the "good" set. Any such $t$ satisfies our requirement.

### Mathematical insight
This theorem establishes that we can always find a rotation of a finite set of points such that no two points have the same y-coordinate. This is a useful geometric fact with applications in computational geometry and graph drawing.

Intuitively, the result makes sense because:
1. For any two distinct points, there are only finitely many rotation angles where they would have the same y-coordinate
2. With a finite set of points, we have finitely many pairs to consider
3. Since we have infinitely many possible rotation angles (in the range $[0,2\pi)$) and only finitely many "bad" angles to avoid, there must exist a "good" angle

The result can be viewed as a simple case of a general position argument: almost all rotations put the points in a configuration where no two points share a y-coordinate.

### Dependencies
#### Theorems
- `DISTINGUISHING_ROTATION_EXISTS_PAIR`: Shows that for any two distinct points, the set of rotation angles that make their y-coordinates equal is finite.
- Various utility theorems about infiniteness, finiteness, and set operations (used implicitly).

#### Functions/Definitions
- `rotate2d`: Function that rotates a point in the plane by a given angle
- `pairwise`: Predicate stating that a binary relation holds between any two distinct elements of a set
- `IMAGE`: Function that applies a function to each element of a set

### Porting notes
When porting this theorem:
1. Ensure your system has appropriate definitions for rotation in 2D and vector components
2. The proof relies on the fact that the interval $[0,2\pi)$ is infinite in the sense of cardinality, while removing finitely many points keeps it infinite
3. The key dependency `DISTINGUISHING_ROTATION_EXISTS_PAIR` should be ported first

---

## DISTINGUISHING_ROTATION_EXISTS_POLYGON

### Name of formal statement
DISTINGUISHING_ROTATION_EXISTS_POLYGON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISTINGUISHING_ROTATION_EXISTS_POLYGON = prove
 (`!p:(real^2)list.
        ?f q. (?g. orthogonal_transformation g /\ f = MAP g) /\
              (!x y. MEM x q /\ MEM y q /\ ~(x = y) ==> ~(x$2 = y$2)) /\
              f q = p`,
  GEN_TAC THEN MP_TAC(ISPEC
   `set_of_list(p:(real^2)list)` DISTINGUISHING_ROTATION_EXISTS) THEN
  REWRITE_TAC[FINITE_SET_OF_LIST; pairwise] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_SET_OF_LIST; ROTATE2D_EQ] THEN
  REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `MAP (rotate2d(--t))` THEN
  EXISTS_TAC `MAP (rotate2d t) p` THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF; GSYM ROTATE2D_ADD] THEN
  REWRITE_TAC[REAL_ADD_LINV; ROTATE2D_ZERO; MAP_ID] THEN
  CONJ_TAC THENL [MESON_TAC[ORTHOGONAL_TRANSFORMATION_ROTATE2D]; ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_SET_OF_LIST; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[IN_SET_OF_LIST; ROTATE2D_EQ] THEN ASM_MESON_TAC[]);;
```

### Informal statement
For any list of points $p$ in $\mathbb{R}^2$, there exists a function $f$ and a list of points $q$ in $\mathbb{R}^2$ such that:
1. There exists an orthogonal transformation $g$ such that $f = \text{MAP}(g)$ (i.e., $f$ applies $g$ to each element of a list).
2. For any distinct points $x$ and $y$ in $q$, their second coordinates are different: $x_2 \neq y_2$.
3. $f(q) = p$.

### Informal proof
This theorem builds on the previous result `DISTINGUISHING_ROTATION_EXISTS`, which states that for any finite set of points in $\mathbb{R}^2$, there exists an angle $t$ such that rotating the points by angle $t$ results in a set where no two points share the same second coordinate.

The proof proceeds as follows:

- Apply the theorem `DISTINGUISHING_ROTATION_EXISTS` to the set of points in the list $p$.
- This gives us an angle $t$ such that rotating each point in $p$ by $t$ produces a set where all points have distinct second coordinates.
- Define $f = \text{MAP}(\text{rotate2d}(-t))$, which means $f$ applies a rotation by $-t$ to each element of a list.
- Define $q = \text{MAP}(\text{rotate2d}(t))(p)$, which is the list $p$ with each point rotated by angle $t$.
- To show $f$ is based on an orthogonal transformation, we use the fact that rotation is an orthogonal transformation.
- To verify that points in $q$ have distinct second coordinates, we use the property from `DISTINGUISHING_ROTATION_EXISTS`.
- Finally, to show $f(q) = p$, we observe that $f(q) = \text{MAP}(\text{rotate2d}(-t))(\text{MAP}(\text{rotate2d}(t))(p))$. Since consecutive rotations by $t$ and $-t$ cancel each other out, this equals $p$.

### Mathematical insight
This theorem extends the result about finite sets to lists of points in $\mathbb{R}^2$. It demonstrates that we can find a rotation that transforms any list of points into a "nice" configuration where all points have different heights (second coordinates), and then use the inverse rotation to map back to the original list.

This is useful in computational geometry and polygon algorithms where having points with distinct y-coordinates simplifies many algorithms. For example, it helps in ensuring that no two vertices of a polygon lie on the same horizontal line after transformation, which can be beneficial for various geometric computations including triangulation, visibility, and convex hull calculations.

### Dependencies
- Theorem `DISTINGUISHING_ROTATION_EXISTS`: For any finite set of points in $\mathbb{R}^2$, there exists an angle such that rotating the set by that angle results in all points having distinct second coordinates.
- Various properties of rotations, particularly that they are orthogonal transformations.
- List and set operations in HOL Light.

### Porting notes
When implementing this theorem in other proof assistants:
- Ensure that the notion of rotation in 2D space is properly defined.
- The representation of points in $\mathbb{R}^2$ and how to access their coordinates may differ.
- Pay attention to how list-to-set conversions are handled, as this proof relies on `set_of_list` to apply the set-based theorem to a list.

---

## POLYGON_CHOP_IN_TWO

## POLYGON_CHOP_IN_TWO
- `POLYGON_CHOP_IN_TWO`

## Type of the formal statement
- theorem

## Formal Content
```ocaml
let POLYGON_CHOP_IN_TWO = prove
 (`!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p
        ==> ?a b. ~(a = b) /\ MEM a p /\ MEM b p /\
                  segment(a,b) SUBSET inside(path_image(polygonal_path p))`,
  let wlog_lemma = MESON[]
   `(!x. ?f:A->A y. transform f /\ nice y /\ f y = x)
    ==> !P. (!f x. transform f ==> (P(f x) <=> P x)) /\
            (!x. nice x ==> P x)
            ==> !x. P x` in
  let between_lemma = prove
   (`!a c u v m:real^N.
          collinear {a,c,u,v,m} /\ m IN segment[u,v] /\ m IN segment(a,c)
          ==> u IN segment(a,c) \/ v IN segment(a,c) \/
              segment[a,c] SUBSET segment[u,v]`,
    REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; LEFT_IMP_EXISTS_THM; EMPTY_SUBSET] THEN
    MAP_EVERY X_GEN_TAC [`origin:real^N`; `dir:real^N`] THEN
    GEOM_ORIGIN_TAC `origin:real^N` THEN
    REWRITE_TAC[AFFINE_HULL_2; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `dir:real^N = vec 0` THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_RZERO; SEGMENT_REFL; SUBSET_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET_SEGMENT] THEN
    ASM_SIMP_TAC[SEGMENT_SCALAR_MULTIPLE; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
    REAL_ARITH_TAC) in
  MATCH_MP_TAC(MATCH_MP wlog_lemma DISTINGUISHING_ROTATION_EXISTS_POLYGON) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MESON[] `(!x y. (?z. P z /\ x = f z) ==> Q x y) <=>
                         (!z y. P z ==> Q (f z) y)`] THEN
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION] THEN
    GEOM_TRANSFORM_TAC [];
    ALL_TAC] THEN
  X_GEN_TAC `q:(real^2)list` THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?b:real^2. MEM b q /\ !d. MEM d q ==> b$2 <= d$2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\x:real^2. x$2) (set_of_list q)`
        INF_FINITE) THEN
    SIMP_TAC[FINITE_SET_OF_LIST; FINITE_IMAGE] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; SET_OF_LIST_EQ_EMPTY] THEN
    UNDISCH_TAC `5 <= LENGTH(q:(real^2)list)` THEN
    ASM_CASES_TAC `q:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM; IN_SET_OF_LIST] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^2` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p:(real^2)list.
        EL 1 p = b /\ LAST p = HD p /\
        LENGTH p = LENGTH q /\ set_of_list p = set_of_list q /\
        path_image(polygonal_path p) = path_image(polygonal_path q) /\
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p)`
  MP_TAC THENL
   [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_1 THEN EXISTS_TAC `q:(real^2)list` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(q:(real^2)list)) =
       pathstart(polygonal_path q)`;
      `5 <= LENGTH(q:(real^2)list)`] THEN
    ASM_CASES_TAC `q:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(q:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `a IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_THEN `pathfinish(polygonal_path(q:(real^2)list)) =
                pathstart(polygonal_path q)` (K ALL_TAC) THEN
  UNDISCH_THEN `simple_path(polygonal_path(q:(real^2)list))` (K ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:(real^2)list` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [EXTENSION] THEN
  REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> REWRITE_TAC[GSYM th] THEN
              RULE_ASSUM_TAC(REWRITE_RULE[GSYM th])) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `MEM (b:real^2) r` (K ALL_TAC) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `a:real^2` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `b':real^2` THEN
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
  X_GEN_TAC `c:real^2` THEN X_GEN_TAC `p:(real^2)list` THEN
  REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN
  REWRITE_TAC[num_CONV `1`; EL; HD; TL] THEN
  ASM_CASES_TAC `b':real^2 = b` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `5 <= SUC(SUC(SUC n)) <=> ~(n = 0) /\ 2 <= n`] THEN
  ASM_CASES_TAC `p:(real^2)list = []` THEN ASM_REWRITE_TAC[LENGTH_EQ_NIL] THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS; LAST; NOT_CONS_NIL] THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `b:real^2`) THEN
  REWRITE_TAC[MESON[MEM] `MEM b (CONS a (CONS b l))`] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`linepath(a:real^2,b)`;
    `polygonal_path(CONS (b:real^2) (CONS c p))`]
   SIMPLE_PATH_JOIN_IMP) THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
  REWRITE_TAC[PATHFINISH_LINEPATH; PATHSTART_JOIN; PATHSTART_LINEPATH] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN MP_TAC th)
                MP_TAC) THEN
  SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           NOT_CONS_NIL; HD] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ; GSYM CONJ_ASSOC; PATH_IMAGE_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
           HD; NOT_CONS_NIL] THEN
  REWRITE_TAC[SET_RULE `s INTER (t UNION u) SUBSET v <=>
                        s INTER t SUBSET v /\ s INTER u SUBSET v`] THEN
  ASM_CASES_TAC `a:real^2 = c` THENL
   [DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; SEGMENT_SYM; INTER_ACI] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ_ALT]
        FINITE_SUBSET)) THEN
    REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `CONS (b:real^2) (CONS c p)`
    ARC_POLYGONAL_PATH_IMP_DISTINCT) THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
  REWRITE_TAC[PAIRWISE; ALL] THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  REWRITE_TAC[MESON[] `(!x. P x ==> ~(a = x)) <=> ~(P a)`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^2)$2 < (a:real^2)$2 /\
                (b:real^2)$2 < (c:real^2)$2 /\
                (!v. MEM v p ==> (b:real^2)$2 < (v:real^2)$2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a:real^2,b,c}` ASSUME_TAC THENL
   [REWRITE_TAC[COLLINEAR_BETWEEN_CASES; BETWEEN_IN_SEGMENT] THEN
    SUBGOAL_THEN `FINITE(segment[a:real^2,b] INTER segment[b,c])` MP_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{a:real^2,b}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `segment[a:real^2,b] INTER segment[b,c] = segment[a,b]`
       (fun th -> ASM_REWRITE_TAC[FINITE_SEGMENT; th]) THEN
      REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
      ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT];
      DISCH_TAC THEN UNDISCH_TAC `b IN segment[c:real^2,a]` THEN
      ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT] THEN
      ASM_REWRITE_TAC[IN_SEGMENT; NOT_IN_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. x$2`) THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&1 - u) * b < (&1 - u) * c /\ u * b < u * a
        ==> ~(b = (&1 - u) * c + u * a)`) THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_SUB_LT];
      SUBGOAL_THEN `segment[a:real^2,b] INTER segment[b,c] = segment[b,c]`
       (fun th -> ASM_REWRITE_TAC[FINITE_SEGMENT; th]) THEN
      REWRITE_TAC[SET_RULE `s INTER t = t <=> t SUBSET s`] THEN
      ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
         e <= (a:real^2)$2 - (b:real^2)$2 /\
         e <= (c:real^2)$2 - (b:real^2)$2 /\
         !v. MEM v p ==> e <= (v:real^2)$2 - (b:real^2)$2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\v. (v:real^2)$2 - (b:real^2)$2)
                        (set_of_list(CONS a (CONS b (CONS c p)))
                          DELETE b)`
                INF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_SET_OF_LIST; FINITE_IMAGE; FINITE_DELETE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[set_of_list; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `a:real^2` THEN ASM_REWRITE_TAC[IN_DELETE; IN_INSERT];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN
    ASM_REWRITE_TAC[set_of_list; FORALL_IN_INSERT; IMP_CONJ; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^2` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
    DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_SET_OF_LIST] THEN
    DISCH_TAC THEN EXISTS_TAC `(d:real^2)$2 - (b:real^2)$2` THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; IN_SET_OF_LIST]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a':real^2 = (&1 - e / (a$2 - b$2)) % b + e / (a$2 - b$2) % a`;
    `c':real^2 = (&1 - e / (c$2 - b$2)) % b + e / (c$2 - b$2) % c`] THEN
  SUBGOAL_THEN
   `a' IN segment[b:real^2,a] /\ c' IN segment[b,c]`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b = (&1 - v) % a + v % b <=>
      (u - v) % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
    REWRITE_TAC[UNWIND_THM1] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_DIV; REAL_SUB_LE;
                 REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':real^2 = b) /\ ~(c':real^2 = b)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % a + u % b = a <=> u % (b - a) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~collinear{a':real^2,b,c'}` ASSUME_TAC THENL
   [UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ARITH `((&1 - u) % b + u % a) - b = u % (a - b)`] THEN
    REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL; DOT_LMUL; DOT_RMUL] THEN
    MATCH_MP_TAC(REAL_FIELD
     `~(a = &0) /\ ~(c = &0)
      ==> (a * c * x) pow 2 = (a * a * y) * (c * c * z)
          ==> x pow 2 = y * z`) THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a':real^2 = c')` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~collinear{a':real^2,b,c'}` THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent{a':real^2,b,c'}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3]; ALL_TAC] THEN
  MP_TAC(ISPEC `{a':real^2,b,c'}` INTERIOR_CONVEX_HULL_EQ_EMPTY) THEN
  REWRITE_TAC[DIMINDEX_2; HAS_SIZE; ARITH; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex hull {a,b,c} INTER {x:real^2 | x$2 - b$2 <= e} =
                convex hull {a',b,c'}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
      REWRITE_TAC[CONVEX_HULL_3_ALT] THEN
      REWRITE_TAC[SUBSET; IN_INTER; FORALL_IN_GSPEC; IMP_CONJ] THEN
      REWRITE_TAC[IN_ELIM_THM; VECTOR_ARITH
       `a + x:real^N = a + y <=> x = y`] THEN
      MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN
      REPLICATE_TAC 3 DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
      REWRITE_TAC[VECTOR_ARITH
       `((&1 - u) % b + u % a) - b:real^N = u % (a - b)`] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ADD_SUB; VECTOR_SUB_COMPONENT] THEN STRIP_TAC THEN
      EXISTS_TAC `(s * ((a:real^2)$2 - (b:real^2)$2)) / e` THEN
      EXISTS_TAC `(t * ((c:real^2)$2 - (b:real^2)$2)) / e` THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_SUB_LT; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_ARITH `a / e + b / e:real = (a + b) / e`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      REWRITE_TAC[VECTOR_MUL_ASSOC] THEN BINOP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(REAL_FIELD
       `y < x /\ &0 < e ==> s = (s * (x - y)) / e * e / (x - y)`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[HULL_INC; IN_INSERT; REAL_SUB_REFL; REAL_LT_IMP_LE] THEN
      SIMP_TAC[REAL_LE_SUB_RADD; CONVEX_INTER; CONVEX_HALFSPACE_COMPONENT_LE;
               CONVEX_CONVEX_HULL] THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `a' IN segment[b:real^2,a]` THEN
        SPEC_TAC(`a':real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        EXPAND_TAC "a'";
        UNDISCH_TAC `c' IN segment[b:real^2,c]` THEN
        SPEC_TAC(`c':real^2`,`x:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
        SET_TAC[];
        EXPAND_TAC "c'"] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH
       `(&1 - u) * b + u * a <= e + b <=> (a - b) * u <= e`] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
      REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior(convex hull {a,b,c}) INTER {x:real^2 | x$2 - b$2 < e} =
    interior(convex hull {a',b,c'})`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_SUB_RADD; GSYM INTERIOR_HALFSPACE_COMPONENT_LE] THEN
    ASM_REWRITE_TAC[GSYM INTERIOR_INTER; GSYM REAL_LE_SUB_RADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^2. d IN interior(convex hull {a',b,c'}) /\ ~(d$1 = b$1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(interior(convex hull {a':real^2,b,c'}) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^2)$1 = (b:real^2)$1` THENL
     [ALL_TAC; EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o SPEC `x + k / &2 % basis 1:real^2`) THEN ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x,x + e) = norm e`] THEN
      SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; ARITH] THEN
      UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    EXISTS_TAC `x + k / &2 % basis 1:real^2` THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT; DIMINDEX_GE_1; ARITH; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> ~(b + k / &2 = b)`] THEN
    REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `k / &2` THEN
    ASM_REWRITE_TAC[REAL_HALF; SUBSET] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_BALL] THEN MATCH_MP_TAC(NORM_ARITH
     `!a. dist(x + a,y) < k / &2 /\ norm(a) = k / &2 ==> dist(x,y) < k`) THEN
    EXISTS_TAC `k / &2 % basis 1:real^2` THEN ASM_REWRITE_TAC[NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    UNDISCH_TAC `&0 < k` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `path_image(polygonal_path(CONS a (CONS b (CONS c p))))
     SUBSET {x:real^2 | x$2 >= b$2}`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC
     `convex hull(set_of_list(CONS (a:real^2) (CONS b (CONS c p))))` THEN
    SIMP_TAC[PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL; NOT_CONS_NIL] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE] THEN
    REWRITE_TAC[set_of_list; INSERT_SUBSET; IN_ELIM_THM; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[SUBSET; IN_SET_OF_LIST; real_ge; IN_ELIM_THM; REAL_LT_IMP_LE;
                 REAL_LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
    ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS; NOT_CONS_NIL] THEN
    REWRITE_TAC[IN_ELIM_THM; real_ge] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `(:real^2) DIFF {x | x$2 >= b$2} SUBSET
    outside(path_image
                 (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))`
  MP_TAC THENL
   [MATCH_MP_TAC OUTSIDE_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE] THEN
    ASM_REWRITE_TAC[SUBSET; real_ge; IN_ELIM_THM];
    REWRITE_TAC[SUBSET; real_ge; IN_ELIM_THM; IN_UNIV;
                IN_DIFF; REAL_NOT_LE] THEN
    DISCH_TAC] THEN
  ABBREV_TAC
   `d':real^2 = d - (&1 + (d:real^2)$2 - (b:real^2)$2) % basis 2` THEN
  SUBGOAL_THEN `(d':real^2) IN outside(path_image
        (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "d'" THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a':real^2)$2 - (b:real^2)$2 = e /\
                (c':real^2)$2 - (b:real^2)$2 = e`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a'"; "c'"] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `((&1 - u) * b + u * a) - b = u * (a - b)`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ARITH `b < a ==> ~(a - b = &0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^2)$2 < (d:real^2)$2 /\ (d:real^2)$2 < (b:real^2)$2 + e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^2) IN interior(convex hull {a',b,c'})` THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:real`; `s:real`; `t:real`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_EQ_SUB_RADD]) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (REAL_ARITH
     `r + s + t = &1 ==> s = &1 - (r + t)`)) THEN
    REWRITE_TAC[REAL_ARITH
     `b < r * x + (&1 - (r + t)) * b + t * x <=> (r + t) * b < (r + t) * x`;
                REAL_ARITH
     `r * (e + b) + (&1 - (r + t)) * b + t * (e + b) < b + e <=>
      (r + t) * e < &1 * e`] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_ADD; REAL_LT_RMUL_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(d':real^2)$2 + &1 = (b:real^2)$2` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a':real^2,b,c'} SUBSET convex hull {a,b,c}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
    SIMP_TAC[HULL_INC; IN_INSERT] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(a':real^2) IN segment[b,a]` THEN
      SPEC_TAC(`a':real^2`,`x:real^2`);
      UNDISCH_TAC `(c':real^2) IN segment[b,c]` THEN
      SPEC_TAC(`c':real^2`,`x:real^2`)] THEN
    REWRITE_TAC[GSYM SUBSET] THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d' IN convex hull {a:real^2,b,c})` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!t. s SUBSET t /\ ~(x IN t) ==> ~(x IN s)`) THEN
    EXISTS_TAC `{x | (x:real^2)$2 >= (b:real^2)$2}` THEN
    SIMP_TAC[SUBSET_HULL; CONVEX_HALFSPACE_COMPONENT_GE] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM; real_ge] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d' IN convex hull {a':real^2,b,c'})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(segment[d:real^2,d'] INTER frontier(convex hull {a',b,c'}) = {})`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN
    REWRITE_TAC[CONNECTED_SEGMENT; GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
     [EXISTS_TAC `d:real^2` THEN REWRITE_TAC[ENDS_IN_SEGMENT; IN_INTER] THEN
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      EXISTS_TAC `d':real^2` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT; IN_DIFF]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` MP_TAC) THEN REWRITE_TAC[IN_INTER] THEN
  ASM_CASES_TAC `x:real^2 = d` THENL
   [ASM_REWRITE_TAC[IN_DIFF; frontier]; ALL_TAC] THEN
  ASM_CASES_TAC `x:real^2 = d'` THENL
   [ASM_REWRITE_TAC[IN_DIFF; frontier] THEN
    SUBGOAL_THEN `closure(convex hull {a':real^2,b,c'}) = convex hull {a',b,c'}`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MESON_TAC[COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT; FINITE_RULES];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(d':real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
   [EXPAND_TAC "d'" THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `x:real^2`] SEGMENT_VERTICAL) THEN
    ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^2 = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2)$2 < (b:real^2)$2 + e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `x:real^2`] SEGMENT_VERTICAL) THEN
    ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^2 = a) /\ ~(x = c)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^2) IN (segment(b,a) UNION segment(b,c))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^2) IN frontier(convex hull {a':real^2,b,c'})` THEN
    ASM_SIMP_TAC[open_segment; IN_UNION; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN MATCH_MP_TAC(SET_RULE
     `~(x IN u) /\ s SUBSET s' /\ t SUBSET t'
      ==> x IN (s UNION t UNION u) ==> x IN s' \/ x IN t'`) THEN
    ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c':real^2`; `a':real^2`; `x:real^2`]
      SEGMENT_HORIZONTAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[d:real^2,d'] INTER path_image(polygonal_path(CONS c p)) = {}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!u. t SUBSET u /\ s INTER u = {} ==> s INTER t = {}`) THEN
    EXISTS_TAC `{x:real^2 | x$2 >= (b:real^2)$2 + e}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `convex hull(set_of_list(CONS c p)) :real^2->bool` THEN
      SIMP_TAC[PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL; NOT_CONS_NIL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE;
                  set_of_list; INSERT_SUBSET] THEN
      REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[real_ge; REAL_ARITH `b + e <= x <=> e <= x - b`];
      REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. x IN s ==> ~(x IN t)`] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL[`d:real^2`; `d':real^2`; `y:real^2`] SEGMENT_VERTICAL) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; real_ge] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^2) IN interior(convex hull {a,b,c})` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^2) IN interior(convex hull {a', b, c'})` THEN
    SPEC_TAC(`d:real^2`,`d:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d':real^2 = d)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN segment[d,d'] /\
               y IN (segment (b,a) UNION segment (b,c))
               ==> y = x`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `collinear {d:real^2,x,y}` MP_TAC THENL
     [REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
      MAP_EVERY EXISTS_TAC [`d:real^2`; `d':real^2`] THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; ENDS_IN_SEGMENT] THEN
      ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION];
      ALL_TAC] THEN
    REWRITE_TAC[COLLINEAR_BETWEEN_CASES; BETWEEN_IN_SEGMENT] THEN
    ASM_SIMP_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_CASES_TAC `x:real^2 = y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(x:real^2) IN frontier(convex hull {a,b,c}) /\
      (y:real^2) IN frontier(convex hull {a,b,c})`
    MP_TAC THENL
     [REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN
      REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_UNION]) THEN ASM_MESON_TAC[SEGMENT_SYM];
      REWRITE_TAC[frontier; IN_DIFF]] THEN
    ASM_CASES_TAC `y:real^2 = d` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(d:real^2) IN segment (x,y)`;
        `(y:real^2) IN segment [d,d']`;
        `(x:real^2) IN segment(d,d')`] THEN
      ASM_REWRITE_TAC[IN_SEGMENT] THEN
      REPLICATE_TAC 2 (STRIP_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; VECTOR_ARITH
       `d = (&1 - w) % ((&1 - u) % d + u % d') + w % ((&1 - v) % d + v % d') <=>
        ((&1 - w) * u + w * v) % (d' - d) = vec 0`] THEN
      DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_SIMP_TAC[REAL_SUB_LE; REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ARITH
       `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `~(x IN interior(convex hull {a:real^2, b, c}))` THEN
      UNDISCH_TAC `x IN segment (y:real^2,d)` THEN
      SPEC_TAC(`x:real^2`,`x:real^2`) THEN ASM_REWRITE_TAC[GSYM SUBSET] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
      MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL];
      UNDISCH_TAC `~(y IN interior(convex hull {a:real^2, b, c}))` THEN
      UNDISCH_TAC `y IN segment (d:real^2,x)` THEN
      SPEC_TAC(`y:real^2`,`y:real^2`) THEN ASM_REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[CONVEX_CONVEX_HULL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish(polygonal_path p) = (a:real^2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHFINISH_POLYGONAL_PATH]; ALL_TAC] THEN
  SUBGOAL_THEN `segment(a:real^2,b) INTER segment(b,c) = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `segment[a:real^2,b] INTER segment[b,c] SUBSET {a, b}` THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC MONO_FORALL THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(d:real^2) IN inside(path_image
      (linepath(a,b) ++ linepath(b,c) ++ polygonal_path(CONS c p)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `x IN segment(b:real^2,a) UNION segment (b,c)` THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `d:real^2`; `d':real^2`;
                 `linepath(b:real^2,c) ++ polygonal_path(CONS c p)`;
                 `x:real^2`] PARITY_LEMMA) THEN
      SUBGOAL_THEN
       `path_image((linepath(b:real^2,c) ++ polygonal_path(CONS c p)) ++
                   linepath(a,b)) =
        path_image(linepath(a,b) ++ linepath(b:real^2,c) ++
                   polygonal_path(CONS c p))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC PATH_IMAGE_SYM THEN
        REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
        UNDISCH_TAC `pathfinish(linepath(a,b) ++
          linepath (b,c) ++ polygonal_path(CONS c p)):real^2 = a` THEN
        ASM_REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_POLYGONAL_PATH];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_SYM o snd) THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
        REWRITE_TAC[PATHFINISH_POLYGONAL_PATH] THEN
        ASM_REWRITE_TAC[NOT_CONS_NIL; LAST];
        REWRITE_TAC[PATHSTART_JOIN; PATHSTART_LINEPATH];
        REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_POLYGONAL_PATH] THEN
        ASM_REWRITE_TAC[NOT_CONS_NIL; LAST];
        MATCH_MP_TAC(SET_RULE
         `x IN s /\ x IN t /\ (!y. y IN s /\ y IN t ==> y = x)
          ==> s INTER t = {x}`) THEN
        SUBST1_TAC(ISPECL[`a:real^2`; `b:real^2`] (CONJUNCT2 SEGMENT_SYM)) THEN
        ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_CLOSED_OPEN]) THEN ASM SET_TAC[];
        SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                 PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
        ASM_REWRITE_TAC[SET_RULE `s INTER (t UNION u) = {} <=>
                        s INTER t = {} /\ s INTER u = {}`] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:real^2` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN `(y:real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `y:real^2`]
             SEGMENT_VERTICAL) THEN
          ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION;
                        IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_CASES_TAC `y:real^2 = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        RULE_ASSUM_TAC(SUBS[ISPECL [`a:real^2`; `b:real^2`]
         (CONJUNCT2 SEGMENT_SYM)]) THEN
        ASM_CASES_TAC `y:real^2 = c` THENL [ALL_TAC; ASM SET_TAC[]] THEN
        UNDISCH_THEN `y:real^2 = c` SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `c:real^2`]
         SEGMENT_VERTICAL) THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
        ASM_REAL_ARITH_TAC];
      MP_TAC(ISPECL [`b:real^2`; `c:real^2`; `d:real^2`; `d':real^2`;
                 `polygonal_path(CONS c p) ++ linepath(a:real^2,b)`;
                 `x:real^2`] PARITY_LEMMA) THEN
      SUBGOAL_THEN
       `path_image((polygonal_path (CONS c p) ++ linepath (a,b)) ++
                   linepath(b:real^2,c)) =
        path_image(linepath(a,b) ++ linepath(b:real^2,c) ++
                   polygonal_path(CONS c p))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
                     PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                     PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                     NOT_CONS_NIL; HD; LAST] THEN
        REWRITE_TAC[UNION_ACI];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) (GSYM SIMPLE_PATH_ASSOC) o snd) THEN
        ANTS_TAC THENL
         [ALL_TAC;
          DISCH_THEN SUBST1_TAC THEN
          W(MP_TAC o PART_MATCH (lhs o rand) SIMPLE_PATH_SYM o snd) THEN
          ANTS_TAC THENL
           [ALL_TAC;
            DISCH_THEN SUBST1_TAC THEN
            W(MP_TAC o PART_MATCH (lhs o rand) (GSYM SIMPLE_PATH_ASSOC) o
              snd) THEN
            ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC]] THEN
        ASM_SIMP_TAC[GSYM SIMPLE_PATH_ASSOC;PATHSTART_JOIN;
                     PATHFINISH_JOIN;
                     PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                     PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                     NOT_CONS_NIL; HD; LAST];
        REWRITE_TAC[PATHSTART_JOIN; PATHSTART_POLYGONAL_PATH] THEN
        REWRITE_TAC[NOT_CONS_NIL; HD];
        REWRITE_TAC[PATHFINISH_JOIN; PATHFINISH_LINEPATH];
        MATCH_MP_TAC(SET_RULE
         `x IN s /\ x IN t /\ (!y. y IN s /\ y IN t ==> y = x)
          ==> s INTER t = {x}`) THEN
        SUBST1_TAC(ISPECL[`a:real^2`; `b:real^2`] (CONJUNCT2 SEGMENT_SYM)) THEN
        ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SEGMENT_CLOSED_OPEN]) THEN ASM SET_TAC[];
        ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; NOT_CONS_NIL; HD;
                     PATH_IMAGE_LINEPATH; PATHFINISH_POLYGONAL_PATH; LAST] THEN
        ASM_REWRITE_TAC[SET_RULE `s INTER (t UNION u) = {} <=>
                        s INTER t = {} /\ s INTER u = {}`] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:real^2` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        SUBGOAL_THEN `(y:real^2)$1 = (d:real^2)$1` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `y:real^2`]
             SEGMENT_VERTICAL) THEN
          ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION;
                        IN_INSERT; NOT_IN_EMPTY] THEN
        ASM_CASES_TAC `y:real^2 = b` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        RULE_ASSUM_TAC(SUBS[ISPECL [`a:real^2`; `b:real^2`]
         (CONJUNCT2 SEGMENT_SYM)]) THEN
        ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
        ASM_CASES_TAC `y:real^2 = a` THENL [ALL_TAC; ASM SET_TAC[]] THEN
        UNDISCH_THEN `y:real^2 = a` SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`d:real^2`; `d':real^2`; `a:real^2`]
         SEGMENT_VERTICAL) THEN
        ASM_REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent{a:real^2,b,c}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3]; ALL_TAC] THEN
  ASM_CASES_TAC
   `path_image(polygonal_path(CONS c p)) INTER
    convex hull {a,b,c} SUBSET {a:real^2,c}`
  THENL
   [MAP_EVERY EXISTS_TAC [`a:real^2`; `c:real^2`] THEN
    ASM_REWRITE_TAC[MEM] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
    EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[connected_component] THEN
    EXISTS_TAC `segment[d:real^2,y]` THEN
    REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
     `convex hull {a:real^2,b,c} DIFF (segment[a,b] UNION segment[b,c])` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH;
        PATHSTART_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `t INTER s SUBSET c
        ==> c SUBSET (a UNION b)
            ==> s DIFF (a UNION b) SUBSET UNIV DIFF (a UNION b UNION t)`)) THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_UNION; ENDS_IN_SEGMENT]] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `~(d IN frontier(convex hull {a:real^2,b,c}))` MP_TAC THENL
       [ASM_REWRITE_TAC[frontier; IN_DIFF];
        REWRITE_TAC[FRONTIER_OF_TRIANGLE; SEGMENT_CONVEX_HULL] THEN SET_TAC[]];
      REWRITE_TAC[IN_DIFF; IN_UNION] THEN REPEAT STRIP_TAC THENL
       [UNDISCH_TAC `y IN segment(a:real^2,c)` THEN
        REWRITE_TAC[open_segment; IN_DIFF; SEGMENT_CONVEX_HULL] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s /\ P x ==> x IN t`) THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
        MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `y:real^2` THEN
        MAP_EVERY UNDISCH_TAC
         [`y IN convex hull {a:real^2, b}`; `y IN segment(a:real^2,c)`] THEN
        REWRITE_TAC[open_segment; GSYM SEGMENT_CONVEX_HULL; IN_DIFF] THEN
        REWRITE_TAC[DE_MORGAN_THM; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[IMP_IMP; GSYM BETWEEN_IN_SEGMENT] THEN
        DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
          MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
        REWRITE_TAC[INSERT_AC; IMP_IMP];
        UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,c,a}`] THEN
        MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `y:real^2` THEN
        MAP_EVERY UNDISCH_TAC
         [`y IN convex hull {b:real^2, c}`; `y IN segment(a:real^2,c)`] THEN
        REWRITE_TAC[open_segment; GSYM SEGMENT_CONVEX_HULL; IN_DIFF] THEN
        REWRITE_TAC[DE_MORGAN_THM; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[IMP_IMP; GSYM BETWEEN_IN_SEGMENT] THEN
        DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
          MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
        REWRITE_TAC[INSERT_AC; IMP_IMP]];
      REWRITE_TAC[SET_RULE
       `s DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)`] THEN
      MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`convex hull {a:real^2,b,c}`; `convex hull{a:real^2,b}`]
          FACE_OF_STILLCONVEX) THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC(TAUT
         `p ==> (p <=> q /\ r /\ s) ==> r`) THEN
        ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
        EXISTS_TAC `{a:real^2,b}` THEN SET_TAC[];
        MP_TAC(ISPECL [`convex hull {a:real^2,b,c}`; `convex hull{b:real^2,c}`]
          FACE_OF_STILLCONVEX) THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN MATCH_MP_TAC(TAUT
         `p ==> (p <=> q /\ r /\ s) ==> r`) THEN
        ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
        EXISTS_TAC `{b:real^2,c}` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?n:real^2.
        ~(n = vec 0) /\ orthogonal n (c - a) /\
        &0 < n dot (c - b)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?n:real^2. ~(n = vec 0) /\ orthogonal n (c - a)`
    STRIP_ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
      MATCH_MP_TAC ORTHOGONAL_TO_VECTOR_EXISTS THEN
      REWRITE_TAC[DIMINDEX_2; LE_REFL];
      ALL_TAC] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
     `&0 < n dot (c - b) \/ &0 < --(n dot (c - b)) \/
      (n:real^2) dot (c - b) = &0`)
    THENL
     [EXISTS_TAC `n:real^2` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `--n:real^2` THEN ASM_REWRITE_TAC[DOT_LNEG] THEN
      ASM_REWRITE_TAC[VECTOR_NEG_EQ_0; ORTHOGONAL_LNEG];
      UNDISCH_TAC `~collinear{a:real^2,b,c}` THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      ONCE_REWRITE_TAC[COLLINEAR_3] THEN
      MATCH_MP_TAC ORTHOGONAL_TO_ORTHOGONAL_2D THEN
      EXISTS_TAC `n:real^2` THEN
      ONCE_REWRITE_TAC[GSYM ORTHOGONAL_RNEG] THEN
      ASM_REWRITE_TAC[VECTOR_NEG_SUB] THEN
      ASM_REWRITE_TAC[orthogonal]];
    ALL_TAC] THEN
  SUBGOAL_THEN `n dot (a - b:real^2) = n dot (c - b)` ASSUME_TAC THENL
   [REWRITE_TAC[DOT_RSUB; real_sub; REAL_EQ_ADD_RCANCEL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x = y <=> y - x = &0`] THEN
    ASM_REWRITE_TAC[GSYM DOT_RSUB; GSYM orthogonal];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN convex hull {a,b,c} /\ ~(y = b) ==> &0 < n dot (y - b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3_ALT; FORALL_IN_GSPEC; IMP_CONJ] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a + u % (b - a) + v % (c - a)) - b =
      (&1 - u - v) % (a - b) + v % (c - b)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    MAP_EVERY X_GEN_TAC [`r:real`; `s:real`] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `(&1 - u - v) * x + v * x = (&1 - u) * x`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `r = &1 /\ s = &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    UNDISCH_TAC `~(a + r % (b - a) + s % (c - a):real^2 = b)` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_SUB_LT] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN convex hull {a,b,c} ==> &0 <= n dot (y - b)`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `y:real^2 = b` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO; REAL_LE_REFL] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^2. y IN convex hull {a,b,c} ==> n dot (y - b) <= n dot (c - b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3_ALT; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a + u % (b - a) + v % (c - a)) - b =
      (&1 - u - v) % (a - b) + v % (c - b)`] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_ARITH
     `(&1 - u - v) * x + v * x <= x <=> &0 <= u * x`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^2. n dot (x - b)`;
  `path_image (polygonal_path(CONS c p)) INTER convex hull {a:real^2,b,c}`]
        CONTINUOUS_ATTAINS_INF) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_INTER THEN
      SIMP_TAC[COMPACT_PATH_IMAGE; PATH_POLYGONAL_PATH] THEN
      SIMP_TAC[COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT;
               FINITE_INSERT; FINITE_EMPTY];
      ASM SET_TAC[];
      SUBGOAL_THEN
       `(\x:real^2. n dot (x - b)) = (\x. n dot x) o (\x. x - b)`
      SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_LIFT_DOT] THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?mx:real^2.
      ~(mx = a) /\ ~(mx = c) /\
      mx IN path_image(polygonal_path(CONS c p)) INTER convex hull {a, b, c} /\
      (!y. y IN
           path_image(polygonal_path(CONS c p)) INTER convex hull {a, b, c}
           ==> n dot (mx - b) <= n dot (y - b))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `mx:real^2` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `n dot (mx - b:real^2) <= n dot (c - b)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN STRIP_TAC THENL
     [EXISTS_TAC `mx:real^2` THEN ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `~(path_image(polygonal_path(CONS c p)) INTER
                   convex hull {a, b, c} SUBSET {a:real^2, c})` THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_INSERT; NOT_IN_EMPTY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `my:real^2` THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `n dot (mx - b:real^2)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    FIRST_X_ASSUM(CHOOSE_THEN (K ALL_TAC))] THEN
  ABBREV_TAC `m = (n:real^2) dot (mx - b)` THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
    UNDISCH_TAC
     `segment[b:real^2,c] INTER path_image (polygonal_path (CONS c p))
      SUBSET {c}` THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `b:real^2`) THEN
    ASM_REWRITE_TAC[IN_SING; ENDS_IN_SEGMENT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?z:real^2. MEM z p /\
               z IN (convex hull {a,b,c} DIFF {a,c}) /\
               n dot (z - b) = m`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`b:real^2`; `z:real^2`] THEN
    ASM_REWRITE_TAC[MEM] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_REFL]; DISCH_TAC] THEN
    X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC INSIDE_SAME_COMPONENT THEN
    EXISTS_TAC `d:real^2` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(z:real^2 = a) /\ ~(z = c)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(z:real^2) IN path_image(polygonal_path(CONS c p)) /\
      (z:real^2) IN path_image(polygonal_path p)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
      ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(z IN segment[a:real^2,b]) /\ ~(z IN segment[b,c])`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~collinear{b:real^2,a,z} /\ ~collinear{b,c,z}`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
      MATCH_MP_TAC(SET_RULE
       `!c. x IN c /\ ~(x IN (a INTER c)) /\ ~(x IN (b INTER c))
            ==> ~(x IN a) /\ ~(x IN b)`) THEN
      EXISTS_TAC `convex hull {a:real^2,b,c}` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL;
                   INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT] THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `segment(b:real^2,z) INTER segment[a,b] = {} /\
      segment(b,z) INTER segment[b,c] = {}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      CONJ_TAC THEN X_GEN_TAC `v:real^2` THEN STRIP_TAC THENL
       [UNDISCH_TAC `~collinear{b:real^2,a,z}`;
        UNDISCH_TAC `~collinear{b:real^2,c,z}`] THEN
      REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
      MATCH_MP_TAC COLLINEAR_3_TRANS THEN
      EXISTS_TAC `v:real^2` THEN
      UNDISCH_TAC `v IN segment(b:real^2,z)` THEN
      REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[DE_MORGAN_THM; IMP_CONJ] THENL
       [UNDISCH_TAC `v IN segment[a:real^2,b]`;
        UNDISCH_TAC `v IN segment[b:real^2,c]`] THEN
      ONCE_REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR)) THEN
      REWRITE_TAC[INSERT_AC] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[b:real^2,z] SUBSET convex hull {a,b,c}`
    ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
      SIMP_TAC[HULL_INC; IN_INSERT] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment(b:real^2,z) SUBSET convex hull {a,b,c}`
    ASSUME_TAC THENL
     [REWRITE_TAC[open_segment] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `segment(b:real^2,z) INTER path_image(polygonal_path(CONS c p)) = {}`
    ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `v:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `m <= n dot (v - b:real^2)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_NOT_LE] THEN
      UNDISCH_TAC `v IN segment(b:real^2,z)` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[DOT_RMUL; VECTOR_ARITH
       `((&1 - t) % a + t % b) - a:real^N = t % (b - a)`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `t * m < m <=> &0 < m * (&1 - t)`] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LT];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment(b:real^2,z) SUBSET interior(convex hull {a,b,c})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
       `(convex hull {a:real^2,b,c}) DIFF frontier(convex hull {a,b,c})` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
         `s SUBSET u ==> s DIFF (u DIFF t) SUBSET t`) THEN
        REWRITE_TAC[CLOSURE_SUBSET]] THEN
      REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN MATCH_MP_TAC(SET_RULE
       `s INTER a = {} /\ s INTER b = {} /\ s INTER c = {} /\ s SUBSET u
        ==> s SUBSET u DIFF (a UNION b UNION c)`) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `v:real^2` THEN REWRITE_TAC[IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. n dot (x - b)`) THEN
      REWRITE_TAC[VECTOR_ARITH
         `((&1 - u) % c + u % a) - b =
          (&1 - u) % (c - b) + u % (a - b)`] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_ADD_LID; VECTOR_MUL_RZERO] THEN
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN MATCH_MP_TAC(REAL_ARITH
       `&0 < m * (&1 - t) /\ m <= x ==> ~((&1 - s) * x + s * x = t * m)`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_SUB_LT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SIMP_TAC[IN_INTER; IN_INSERT; HULL_INC] THEN MATCH_MP_TAC
       (REWRITE_RULE[SUBSET] VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
      REWRITE_TAC[set_of_list; IN_INSERT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?y:real^2. y IN segment(b,z) /\ y IN interior(convex hull {a',b,c'})`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[INTER; GSYM(ASSUME
       `interior(convex hull {a, b, c}) INTER {x:real^2 | x$2 - b$2 < e} =
        interior(convex hull {a', b, c'})`)] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(SET_RULE
       `(?y. y IN s /\ P y) /\ s SUBSET t
        ==> ?y. y IN s /\ y IN t /\ P y`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC
       `b + min (&1 / &2) (e / &2 / norm(z - b)) % (z - b):real^2` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `min (&1 / &2) (e / &2 / norm (z - b:real^2))` THEN
        REPEAT CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC; VECTOR_ARITH_TAC] THEN
        REWRITE_TAC[REAL_LT_MIN] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
        REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_ADD_SUB] THEN
        MATCH_MP_TAC(REAL_ARITH
         `abs(x$2) <= norm x /\ norm x <= e / &2 /\ &0 < e ==> x$2 < e`) THEN
        SIMP_TAC[COMPONENT_LE_NORM; DIMINDEX_2; ARITH] THEN
        ASM_REWRITE_TAC[NORM_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(min (&1 / &2) x) <= x`) THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LT_DIV THEN
        ASM_REWRITE_TAC[REAL_HALF; NORM_POS_LT; VECTOR_SUB_EQ]];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_TRANS THEN EXISTS_TAC `y:real^2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `interior(convex hull {a':real^2,b,c'})` THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR; CONVEX_CONVEX_HULL] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHSTART_LINEPATH;
         PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[SET_RULE `s SUBSET UNIV DIFF (a UNION b UNION c) <=>
        s INTER a = {} /\ s INTER b = {} /\ s INTER c = {}`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!t. s SUBSET t /\ t INTER u = {} ==> s INTER u = {}`) THEN
        EXISTS_TAC `interior(convex hull {a:real^2,b,c})` THEN
        ASM_SIMP_TAC[SUBSET_INTERIOR] THEN
        MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`]
         FRONTIER_OF_TRIANGLE) THEN
        REWRITE_TAC[PATH_IMAGE_LINEPATH; frontier] THEN
        MATCH_MP_TAC(SET_RULE
         `!s. i SUBSET s /\ s SUBSET c
          ==> c DIFF i = a UNION b ==> i INTER a = {}`) THEN
        EXISTS_TAC `convex hull {a:real^2,b,c}` THEN
        REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET];
        MATCH_MP_TAC(SET_RULE
         `!t. s SUBSET t /\ t INTER u = {} ==> s INTER u = {}`) THEN
        EXISTS_TAC `interior(convex hull {a:real^2,b,c})` THEN
        ASM_SIMP_TAC[SUBSET_INTERIOR] THEN
        MP_TAC(ISPECL [`a:real^2`; `b:real^2`; `c:real^2`]
         FRONTIER_OF_TRIANGLE) THEN
        REWRITE_TAC[PATH_IMAGE_LINEPATH; frontier] THEN
        MATCH_MP_TAC(SET_RULE
         `!s. i SUBSET s /\ s SUBSET c
          ==> c DIFF i = a UNION b UNION d ==> i INTER b = {}`) THEN
        EXISTS_TAC `convex hull {a:real^2,b,c}` THEN
        REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET];
        MATCH_MP_TAC(SET_RULE
         `!t. s SUBSET t /\ u INTER t = {} ==> s INTER u = {}`) THEN
        EXISTS_TAC `{x | (x:real^2)$2 - (b:real^2)$2 < e}` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[SET_RULE `s INTER t = {} <=> s SUBSET (UNIV DIFF t)`] THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; REAL_NOT_LT; IN_UNIV] THEN
        MP_TAC(ISPEC `CONS (c:real^2) p`
                PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL) THEN
        REWRITE_TAC[NOT_CONS_NIL] THEN
        MATCH_MP_TAC(SET_RULE
         `t SUBSET {x | P x} ==> s SUBSET t ==> !x. x IN s ==> P x`) THEN
        REWRITE_TAC[REAL_ARITH `e <= x - b <=> x >= b + e`] THEN
        SIMP_TAC[SUBSET_HULL; CONVEX_HALFSPACE_COMPONENT_GE] THEN
        REWRITE_TAC[set_of_list; REAL_ARITH `x >= b + e <=> e <= x - b`] THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[SUBSET; IN_SET_OF_LIST; IN_ELIM_THM]];
      REWRITE_TAC[connected_component] THEN
      EXISTS_TAC `segment(b:real^2,z)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONNECTED_SEGMENT] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHSTART_LINEPATH;
         PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN ASM SET_TAC[]]] THEN
  SUBGOAL_THEN
   `?u v:real^2.
        MEM u (CONS c p) /\ MEM v (CONS c p) /\
        mx IN segment[u,v] /\
        segment[u,v] SUBSET path_image(polygonal_path(CONS c p)) /\
        ~(a IN segment[u,v] /\ c IN segment[u,v]) /\
        n dot (u - b) <= m`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`CONS (c:real^2) p`; `mx:real^2`]
      PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LENGTH; ARITH_RULE `3 <= SUC n <=> 2 <= n`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; LAST; HD] THEN STRIP_TAC THEN
    SUBGOAL_THEN `n dot (u - b) <= m \/ n dot (v - b:real^2) <= m`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `n dot (mx - b:real^2) = m` THEN
      UNDISCH_TAC `(mx:real^2) IN segment[u,v]` THEN
      REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH
       `((&1 - u) % x + u % y) - a:real^N =
        (&1 - u) % (x - a) + u % (y - a)`] THEN
      MATCH_MP_TAC(REAL_ARITH `--x < --m ==> ~(x = m)`) THEN
      REWRITE_TAC[GSYM DOT_LNEG] THEN REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
      MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN
      ASM_REWRITE_TAC[DOT_LNEG; REAL_LT_NEG2] THEN ASM_REAL_ARITH_TAC;
      MAP_EVERY EXISTS_TAC [`u:real^2`; `v:real^2`] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`v:real^2`; `u:real^2`] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `n dot (u - b:real^2) < n dot (c - b)` THENL
   [SUBGOAL_THEN `~(u:real^2 = a) /\ ~(u = c)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
    UNDISCH_TAC `MEM (u:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN EXISTS_TAC `u:real^2` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_CASES_TAC `mx:real^2 = u` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN CONJ_TAC THENL
     [DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET]
        VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
      ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`segment(u:real^2,mx)`; `convex hull {a:real^2,b,c}`]
        CONNECTED_INTER_FRONTIER) THEN
    REWRITE_TAC[CONNECTED_SEGMENT] THEN MATCH_MP_TAC(SET_RULE
     `(s SUBSET c ==> u IN c) /\ s INTER f = {} /\ ~(s INTER c = {})
      ==> (~(s INTER c = {}) /\ ~(s DIFF c = {}) ==> ~(s INTER f = {}))
          ==> u IN c`) THEN
    REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `closure(segment(u:real^2,mx)) SUBSET convex hull {a,b,c}`
      MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
        SIMP_TAC[FINITE_IMP_COMPACT; FINITE_INSERT; FINITE_EMPTY];
        ASM_REWRITE_TAC[SUBSET; CLOSURE_SEGMENT] THEN
        DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]];
      REWRITE_TAC[FRONTIER_OF_TRIANGLE] THEN
      MATCH_MP_TAC(SET_RULE
       `!a b c t u.
                s SUBSET t /\ t SUBSET u /\
                a IN ca /\ c IN ca /\
                ab INTER u SUBSET {a,b} /\ bc INTER u SUBSET {c} /\
                ~(b IN u) /\ s INTER ca = {}
                ==> s INTER (ab UNION bc UNION ca) = {}`) THEN
      MAP_EVERY EXISTS_TAC
       [`a:real^2`; `b:real^2`; `c:real^2`; `segment[u:real^2,v]`;
        `path_image(polygonal_path(CONS (c:real^2) p))`] THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT; SUBSET_SEGMENT] THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `CONS (c:real^2) p`
                  PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL) THEN
        REWRITE_TAC[NOT_CONS_NIL] THEN MATCH_MP_TAC(SET_RULE
         `~(x IN t) ==> s SUBSET t ==> ~(x IN s)`) THEN
        MATCH_MP_TAC(SET_RULE
         `!t. ~(b IN t) /\ s SUBSET t ==> ~(b IN s)`) THEN
        EXISTS_TAC `{x:real^2 | (x:real^2)$2 >= (b:real^2)$2 + e}` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; real_ge; REAL_NOT_LE; REAL_LT_ADDR] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN
        REWRITE_TAC[GSYM real_ge; CONVEX_HALFSPACE_COMPONENT_GE] THEN
        REWRITE_TAC[SUBSET; set_of_list; FORALL_IN_INSERT; IN_ELIM_THM] THEN
        ASM_REWRITE_TAC[IN_SET_OF_LIST; REAL_ARITH
         `x >= b + e <=> e <= x - b`];
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        X_GEN_TAC `y:real^2` THEN REWRITE_TAC[IN_SEGMENT] THEN
        DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `t:real` THEN
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(MP_TAC o AP_TERM `\x:real^2. n dot (x - b)`) THEN
        REWRITE_TAC[VECTOR_ARITH
           `((&1 - u) % c + u % a) - b =
            (&1 - u) % (c - b) + u % (a - b)`] THEN
        ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN MATCH_MP_TAC(REAL_ARITH
         `(&1 - t) * a < (&1 - t) * m /\ t * b <= t * m
          ==> ~((&1 - s) * m + s * m = (&1 - t) * a + t * b)`) THEN
        ASM_SIMP_TAC[REAL_LT_LMUL; REAL_SUB_LT] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC] THEN
        SIMP_TAC[IN_INTER; HULL_INC; IN_INSERT] THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET]
          VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
        REWRITE_TAC[set_of_list; IN_INSERT]];
      ALL_TAC] THEN
    ASM_CASES_TAC `mx IN interior(convex hull {a:real^2,b,c})` THENL
     [UNDISCH_TAC `mx IN interior(convex hull {a:real^2,b,c})` THEN
      REWRITE_TAC[IN_INTERIOR_CBALL; SUBSET; IN_CBALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `ee:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[IN_SEGMENT] THEN
      REWRITE_TAC[MESON[]
       `(?x. (?u. P u /\ Q u /\ x = f u) /\ R x) <=>
        (?u. P u /\ Q u /\ R(f u))`] THEN
      EXISTS_TAC `min (&1 / &2) (ee / norm(u - mx:real^2))` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < min (&1 / &2) x`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ];
        REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[dist; VECTOR_ARITH
         `a - ((&1 - u) % a + u % b):real^N = u % (a - b)`] THEN
        ASM_SIMP_TAC[NORM_MUL; GSYM REAL_LE_RDIV_EQ; NORM_POS_LT;
                     VECTOR_SUB_EQ] THEN
        REWRITE_TAC[NORM_SUB] THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < x ==> abs(min (&1 / &2) x) <= x`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; VECTOR_SUB_EQ]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `{a:real^2,b,c}` AFFINE_INDEPENDENT_SPAN_EQ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DIMINDEX_2] THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    REWRITE_TAC[AFFINE_HULL_3; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^2`) THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`r:real`; `s:real`; `t:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `mx IN convex hull {a:real^2,b,c}` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN REWRITE_TAC[CONVEX_HULL_3] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    REWRITE_TAC[IN_INTER; EXISTS_IN_GSPEC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`rx:real`; `sx:real`; `tx:real`] THEN
    ASM_CASES_TAC `rx = &0` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_LID] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN STRIP_TAC THEN
      UNDISCH_TAC
        `segment[b:real^2,c] INTER path_image(polygonal_path(CONS c p))
         SUBSET {c}` THEN
      REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `mx:real^2`) THEN
      MATCH_MP_TAC(TAUT `~q /\ p ==> (p ==> q) ==> r`) THEN
      REWRITE_TAC[IN_SING] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; SEGMENT_CONVEX_HULL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `rx = &1` THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `sx = &0 /\ tx = &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_RID];
      ALL_TAC] THEN
    ASM_CASES_TAC `tx = &0` THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_ADD_RID] THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN STRIP_TAC THEN
      UNDISCH_TAC
        `segment[a:real^2,b] INTER path_image(polygonal_path(CONS c p))
         SUBSET {a,b}` THEN
      REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `mx:real^2`) THEN
      MATCH_MP_TAC(TAUT `~q /\ p ==> (p ==> q) ==> r`) THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
        UNDISCH_TAC `n dot (b - b:real^2) = m` THEN
        REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; SEGMENT_CONVEX_HULL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `tx = &1` THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `sx = &0 /\ rx = &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
     ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID];
     ALL_TAC] THEN
    ASM_CASES_TAC `sx = &1` THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `rx = &0 /\ tx = &0` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
     ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID;
                     VECTOR_ADD_RID] THEN
     DISCH_THEN SUBST_ALL_TAC THEN
     UNDISCH_TAC `n dot (b - b:real^2) = m` THEN
     REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO] THEN
     ASM_REAL_ARITH_TAC;
     ALL_TAC] THEN
    ASM_CASES_TAC `sx = &0` THENL
     [ALL_TAC;
      STRIP_TAC THEN
      UNDISCH_TAC `~(mx IN interior(convex hull {a:real^2, b, c}))` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`rx:real`; `sx:real`; `tx:real`] THEN
      REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    UNDISCH_THEN `sx = &0` SUBST_ALL_TAC THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; REAL_LE_REFL] THEN
    REWRITE_TAC[REAL_ADD_LID] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 < rx /\ rx < &1 /\ &0 < tx /\ tx < &1`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN
    SUBGOAL_THEN
     `?q. q * (rx - r) <= rx /\
          q * (tx - t) <= tx /\
          &0 < q /\ q < &1`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC
       `min (&1 / &2)
            (min (if rx:real = r then &1 / &2 else rx / abs(rx - r))
                 (if tx:real = t then &1 / &2 else tx / abs(tx - t)))` THEN
      REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LT] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
       [ASM_CASES_TAC `r:real = rx` THENL
         [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH
         `~(x = y) ==> &0 < abs(x - y)`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= a /\ &0 <= x /\ &0 <= b ==> abs(min a (min x b)) <= x`) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_CASES_TAC `t:real = tx` THENL
         [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
        REWRITE_TAC[REAL_ABS_MUL] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH
         `~(x = y) ==> &0 < abs(x - y)`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= a /\ &0 <= x /\ &0 <= b ==> abs(min a (min b x)) <= x`) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
     [`(&1 - q) * rx + q * r`;
      `q * s:real`;
      `(&1 - q) * tx + q * t:real`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      EXISTS_TAC `q:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `((&1 - q) * rx + q * r) +
      q * s +
      ((&1 - q) * tx + q * t) =
      (rx + tx) + q * ((r + s + t) - (rx + tx))`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REWRITE_TAC[REAL_ARITH
     `&0 <= (&1 - q) * r + q * s <=> q * (r - s) <= r`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `n dot (u - b:real^2) < n dot (c - b)` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `(r % a + s % b + t % c) - b =
      r % (a - b) + t % (c - b) + ((r + s + t) - &1) % b`] THEN
    REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
    REWRITE_TAC[REAL_ARITH
     `r * x + s * x < x <=> &0 < (&1 - r - s) * x`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `n dot (u - b) = m /\ n dot (c - b) = m` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!mx. n dot (u - b) <= m /\
           ~(n dot (u - b) < n dot (c - b)) /\
           n dot (mx - b) = m /\
           n dot (mx - b) <= n dot (c - b)
           ==> n dot (u - b) = m /\ n dot (c - b) = m`) THEN
    EXISTS_TAC `mx:real^2` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[IN_INTER; HULL_INC; IN_INSERT] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET]
     VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH) THEN
    REWRITE_TAC[set_of_list; IN_INSERT];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN
   (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC)) [`m <= m`; `~(m < m)`] THEN
  SUBGOAL_THEN
   `collinear {a:real^2,mx,c} /\ collinear {a,u,c}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!y:real^2. n dot (y - b) = m ==> collinear {a,y,c}`
     (fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    MATCH_MP_TAC ORTHOGONAL_TO_ORTHOGONAL_2D THEN
    EXISTS_TAC `n:real^2` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM ORTHOGONAL_RNEG] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_SUB] THEN
    MAP_EVERY UNDISCH_TAC
     [`n dot (y - b:real^2) = m`; `n dot (c - b:real^2) = m`] THEN
    REWRITE_TAC[orthogonal; DOT_RSUB] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `mx:real^2 = u` THENL
   [UNDISCH_THEN `mx:real^2 = u` SUBST_ALL_TAC THEN
    UNDISCH_TAC `MEM (u:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN EXISTS_TAC `u:real^2` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `mx:real^2 = v` THENL
   [UNDISCH_THEN `mx:real^2 = v` SUBST_ALL_TAC THEN
    UNDISCH_TAC `MEM (v:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN EXISTS_TAC `v:real^2` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {a:real^2,c,mx,u}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COLLINEAR_4_3] THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,c,b} = {a,b,c}`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {a:real^2,u,v}` ASSUME_TAC THENL
   [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `mx:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `{a:real^2,c,mx,u}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
      ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {c:real^2,u,v}` ASSUME_TAC THENL
   [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `mx:real^2` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `{a:real^2,c,mx,u}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
      ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^2 = v` THENL
   [UNDISCH_THEN `u:real^2 = v` SUBST_ALL_TAC THEN
    ASM_MESON_TAC[SEGMENT_REFL; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `collinear {a:real^2,v,c}` ASSUME_TAC THENL
   [MATCH_MP_TAC COLLINEAR_3_TRANS THEN EXISTS_TAC `u:real^2` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN
    ASM_REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^2`; `c:real^2`; `u:real^2`; `v:real^2`;
                 `mx:real^2`] between_lemma) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhs o rand) COLLINEAR_TRIPLES o snd) THEN
      ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      MP_TAC(ISPECL [`{a:real^2,b,c}`; `{a:real^2,c}`]
                AFFINE_INDEPENDENT_CONVEX_AFFINE_HULL) THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL] THEN
      MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `{a:real^2,c,mx,u}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `u:real^2` THEN
    MP_TAC(ASSUME `u IN segment(a:real^2,c)`) THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `MEM (u:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:real^2) IN segment[a,c]` THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SPEC_TAC(`u:real^2`,`u:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    EXISTS_TAC `v:real^2` THEN
    MP_TAC(ASSUME `v IN segment(a:real^2,c)`) THEN
    REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    UNDISCH_TAC `MEM (v:real^2) (CONS c p)` THEN
    ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(v:real^2) IN segment[a,c]` THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      SPEC_TAC(`v:real^2`,`v:real^2`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      UNDISCH_TAC `collinear {a:real^2, v, c}` THEN
      ONCE_REWRITE_TAC[SET_RULE `{a,v,c} = {a,c,v}`] THEN
      ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
      REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(u % a + v % c) - b:real^N =
        u % (a - b) + v % (c - b) + ((u + v) - &1) % b`] THEN
      ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; REAL_SUB_REFL] THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; GSYM REAL_ADD_RDISTRIB;
                      REAL_MUL_LID]];
    UNDISCH_TAC `segment[a:real^2,c] SUBSET segment[u,v]` THEN
    ASM_REWRITE_TAC[SUBSET_SEGMENT]]);;
```

## Informal statement
For any list of 2D points $p$ such that:
- The polygonal path formed by $p$ is a simple path (i.e., non-self-intersecting)
- The path forms a closed curve (i.e., the path finish equals the path start)
- The list has at least 5 points

There exist two distinct vertices $a$ and $b$ from $p$ such that the open segment between them lies entirely inside the polygon defined by the path.

## Informal proof
The proof employs several key lemmas and follows a multi-stage approach.

First, we apply a wlog (without loss of generality) argument using `DISTINGUISHING_ROTATION_EXISTS_POLYGON` to transform the problem so that all vertices have distinct y-coordinates.

Next, we proceed as follows:

- Find the vertex $b$ with the minimum y-coordinate 
- Rearrange the polygon's vertices to place $b$ at a canonical position in the list
- Find a point $d$ in the interior of the triangle formed by $a$, $b$, and $c$ (where $a$ and $c$ are chosen vertices)
- Extend a vertical line from $d$ until it intersects the polygon boundary at a point $x$ (not at any vertex)

The key observation is that:
- Due to the structure of the polygon and the choice of intersection, $x$ must lie on an edge of the polygon
- The point $x$ must lie on either segment $(b,a)$ or segment $(b,c)$

We then analyze three cases:
1. If $u$ (one of the polygon vertices) is in segment $(a,c)$, then the segment $(b,u)$ lies inside the polygon
2. If $v$ (another polygon vertex) is in segment $(a,c)$, then the segment $(b,v)$ lies inside the polygon
3. If segment $[a,c]$ is contained within segment $[u,v]$, then there exist vertices that form an interior segment

The geometric intuition is that we're finding vertices with a direct "line of sight" through the polygon's interior. The proof uses advanced properties of convex hulls, faces, collinearity, and polygon interiors to establish this result.

## Mathematical insight
This theorem establishes an important structural property of simple polygons: they always contain at least one interior diagonal (a line segment connecting two non-adjacent vertices that lies completely inside the polygon). 

This result is fundamental for polygon triangulation algorithms and computational geometry. It shows that any simple polygon can be "split" into simpler pieces by an interior diagonal. The requirement of at least 5 vertices ensures the polygon is complex enough to have such internal structure - polygons with fewer vertices are either trivial or have no interior diagonals.

The proof technique, using a geometric transformation to make the y-coordinates distinct, is a beautiful application of invariance - we can solve the problem in a simplified setting and then transfer the solution back to the original problem.

## Dependencies
- FACE_OF_STILLCONVEX
- FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT
- FRONTIER_OF_TRIANGLE
- PARITY_LEMMA
- POLYGONAL_PATH_CONS_CONS
- PATHSTART_POLYGONAL_PATH
- PATHFINISH_POLYGONAL_PATH
- VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH
- ARC_POLYGONAL_PATH_IMP_DISTINCT
- PATH_POLYGONAL_PATH
- PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL
- PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS
- PATH_IMAGE_POLYGONAL_PATH_ROTATE
- SIMPLE_PATH_POLYGONAL_PATH_ROTATE
- ROTATE_LIST_TO_FRONT_1
- DISTINGUISHING_ROTATION_EXISTS_POLYGON

## Porting notes
- This theorem relies heavily on polygon properties and transformation techniques. Ensure that the target system has equivalent notions for polygonal paths, simple paths, and the functions to manipulate them.
- The proof uses a rotation transformation to simplify the problem. Some systems might need different approaches for this step.
- The theorem involves complex geometric reasoning about intersections and containment. Systems with rich geometric libraries will make porting easier.
- The proof uses several helper lemmas introduced within the proof itself (wlog_lemma, between_lemma). These will need to be implemented separately.
- The theorem statement and proof use 2D vectors explicitly; ensure your target system can handle vector operations.

---

## PICK

### Name of formal statement
PICK

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let PICK = prove
 (`!p:(real^2)list.
        (!x. MEM x p ==> integral_vector x) /\
        simple_path (polygonal_path p) /\
        pathfinish (polygonal_path p) = pathstart (polygonal_path p)
        ==> measure(inside(path_image(polygonal_path p))) =
                &(CARD {x | x IN inside(path_image(polygonal_path p)) /\
                            integral_vector x}) +
                &(CARD {x | x IN path_image(polygonal_path p) /\
                            integral_vector x}) / &2 - &1`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN DISJ_CASES_TAC
  (ARITH_RULE `LENGTH(p:(real^2)list) <= 4 \/ 5 <= LENGTH p`) THENL
   [UNDISCH_TAC `LENGTH(p:(real^2)list) <= 4` THEN
    POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
    X_GEN_TAC `a:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
    X_GEN_TAC `b:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ;
                  PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `c:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REPLICATE_TAC 4 (DISCH_THEN(K ALL_TAC)) THEN
      REWRITE_TAC[polygonal_path] THEN
      REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
      ASM_CASES_TAC `c:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                   PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[ARC_LINEPATH_EQ] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
      SUBST1_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
      REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
      ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    X_GEN_TAC `d:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REPLICATE_TAC 5 (DISCH_THEN(K ALL_TAC));
      REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC(SUC(SUC(SUC(SUC n)))) <= 4)`]] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[GSYM IN_SET_OF_LIST; set_of_list] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ASM_CASES_TAC `d:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATH_IMAGE_JOIN; PATHSTART_LINEPATH;
      ARC_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN REWRITE_TAC[INSIDE_OF_TRIANGLE] THEN
    REWRITE_TAC[GSYM FRONTIER_OF_TRIANGLE] THEN
    SIMP_TAC[MEASURE_INTERIOR; NEGLIGIBLE_CONVEX_FRONTIER;
             CONVEX_CONVEX_HULL; FINITE_IMP_BOUNDED_CONVEX_HULL;
             FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_SIMP_TAC[PICK_TRIANGLE] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARC_LINEPATH_EQ] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[UNION_OVER_INTER] THEN
    REWRITE_TAC[UNION_SUBSET] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `segment[b:real^2,c] INTER segment [c,a] = segment[b,c] \/
      segment[b,c] INTER segment [c,a] = segment[c,a] \/
      segment[a,b] INTER segment [b,c] = segment[b,c]`
    (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`;
                  SET_RULE `s INTER t = t <=> t SUBSET s`] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_BETWEEN_CASES]) THEN
      REWRITE_TAC[SUBSET_SEGMENT; BETWEEN_IN_SEGMENT; ENDS_IN_SEGMENT] THEN
      REWRITE_TAC[SEGMENT_SYM; DISJ_ACI];
      UNDISCH_TAC `segment [b,c] SUBSET {c:real^2}`;
      UNDISCH_TAC `segment [c,a] SUBSET {c:real^2}`;
      UNDISCH_TAC `segment [b,c] SUBSET {a:real^2, b}`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `p:(real^2)list` POLYGON_CHOP_IN_TWO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`;`b:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?p':(real^2)list.
        HD p' = a /\
        LENGTH p' = LENGTH p /\
        path_image(polygonal_path p') = path_image(polygonal_path p) /\
        set_of_list p' = set_of_list p /\
        simple_path(polygonal_path p') /\
        pathfinish(polygonal_path p') = pathstart(polygonal_path p')`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_0 THEN
    EXISTS_TAC `p:(real^2)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 3 <= p`] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(p:(real^2)list)) =
       pathstart(polygonal_path p)`;
      `5 <= LENGTH(p:(real^2)list)`] THEN
    ASM_CASES_TAC `p:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(p:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `a IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. MEM x p <=> MEM x p'`
   (fun th -> REWRITE_TAC[th] THEN
              RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
   [`set_of_list(p':(real^2)list) = set_of_list p`;
    `path_image(polygonal_path(p':(real^2)list)) =
     path_image (polygonal_path p)`;
    `LENGTH(p':(real^2)list) = LENGTH(p:(real^2)list)`] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`simple_path(polygonal_path(p:(real^2)list))`;
    `pathfinish(polygonal_path(p:(real^2)list)) =
     pathstart(polygonal_path p)`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`p':(real^2)list`,`p:(real^2)list`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?q r. 2 <= LENGTH q /\ 2 <= LENGTH r /\
          LENGTH q + LENGTH r = LENGTH p + 1 /\
          set_of_list q UNION set_of_list r = set_of_list p /\
          pathstart(polygonal_path q) = pathstart(polygonal_path p) /\
          pathfinish(polygonal_path q) = (b:real^2) /\
          pathstart(polygonal_path r) = b /\
          pathfinish(polygonal_path r) = pathfinish(polygonal_path p) /\
          simple_path(polygonal_path q ++ polygonal_path r) /\
          path_image(polygonal_path q ++ polygonal_path r) =
          path_image(polygonal_path p)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `simple_path(polygonal_path p) /\
      2 <= LENGTH p /\ MEM (b:real^2) p /\
      ~(pathstart(polygonal_path p) = b) /\
      ~(pathfinish(polygonal_path p) = b)`
    MP_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 2 <= p`] THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; CONJ_ASSOC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM];
      POP_ASSUM_LIST(K ALL_TAC)] THEN
    WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `x:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  MEM] THEN
      MESON_TAC[];
      REWRITE_TAC[LENGTH; ARITH]] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `l:(real^2)list`] THEN
    REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN DISCH_TAC THEN
    REWRITE_TAC[polygonal_path] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `a:real^2 = b` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `x:real^2 = b` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl) THEN STRIP_TAC THEN
      EXISTS_TAC `[a:real^2;b]` THEN
      EXISTS_TAC `CONS (b:real^2) (CONS y l)` THEN
      ASM_REWRITE_TAC[polygonal_path; LENGTH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REPEAT(CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[set_of_list] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (x:real^2) (CONS y l)`) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC n`] THEN ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= SUC(SUC n)`] THEN
      ONCE_REWRITE_TAC[MEM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SIMPLE_PATH_JOIN_IMP)) THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      SIMP_TAC[PATHFINISH_LINEPATH; ARC_IMP_SIMPLE_PATH];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:(real^2)list`; `r:(real^2)list`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`CONS (a:real^2) q`; `r:(real^2)list`] THEN
    ASM_REWRITE_TAC[LENGTH; NOT_CONS_NIL; HD] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[set_of_list; SET_RULE
       `(a INSERT s) UNION t = a INSERT (s UNION t)`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `pathfinish(polygonal_path q) = (b:real^2)` THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; LAST; NOT_CONS_NIL] THEN
      UNDISCH_TAC `2 <= LENGTH(q:(real^2)list)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `polygonal_path(CONS (a:real^2) q) =
      linepath(a,x) ++ polygonal_path q`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`pathstart(polygonal_path q) =
         pathstart(polygonal_path (CONS (x:real^2) (CONS y l)))`;
        `2 <= LENGTH(q:(real^2)list)`] THEN
      SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
      SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pathstart(polygonal_path(CONS x (CONS y l))) = (x:real^2)`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) SIMPLE_PATH_ASSOC o snd) THEN
      ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `simple_path(linepath(a:real^2,x) ++
                               polygonal_path (CONS x (CONS y l)))` THEN
      ASM_CASES_TAC `pathfinish(polygonal_path r) = (a:real^2)` THENL
       [SUBGOAL_THEN
         `pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHFINISH_LINEPATH;
                     PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH] THEN
        STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        ASM_MESON_TAC[ARC_LINEPATH_EQ];
        SUBGOAL_THEN
         `~(pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a)`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHSTART_LINEPATH;
                     PATHFINISH_JOIN] THEN
        ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN] THEN
        REWRITE_TAC[ARC_LINEPATH_EQ] THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `arc(polygonal_path q ++ polygonal_path r:real^1->real^2)`
        MP_TAC THENL
         [ALL_TAC;
          ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN]] THEN
        MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
        REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL]];
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD;
               PATHSTART_POLYGONAL_PATH] THEN
      UNDISCH_THEN
       `path_image(polygonal_path q ++ polygonal_path r) =
        path_image(polygonal_path(CONS (x:real^2) (CONS y l)))`
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart(polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `5 <= LENGTH(p:(real^2)list)` THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
    ALL_TAC] THEN
  UNDISCH_THEN `pathfinish (polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THEN
  UNDISCH_THEN `path_image(polygonal_path q ++ polygonal_path r):real^2->bool =
                path_image(polygonal_path p)` (SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `(!x:real^2. MEM x q ==> integral_vector x) /\
    (!x:real^2. MEM x r ==> integral_vector x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST; IN_UNION] THEN
    UNDISCH_THEN
     `(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p`
     (SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_UNION];
    ALL_TAC] THEN
  ABBREV_TAC `n = LENGTH(p:(real^2)list)` THEN
  SUBGOAL_THEN `integral_vector(a:real^2) /\ integral_vector(b:real^2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`!x:real^2. MEM x p ==> integral_vector x`;
    `MEM (a:real^2) p`;
    `MEM (b:real^2) p`;
    `HD p = (a:real^2)`;
    `(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p`;
    `simple_path(polygonal_path p :real^1->real^2)`] THEN
  SUBGOAL_THEN `3 <= LENGTH(q:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(linepath(a,b) ++ polygonal_path r))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s' UNION t) INTER (s' UNION t) = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(s' UNION t))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(q:(real^2)list)` (K ALL_TAC)] THEN
  SUBGOAL_THEN `3 <= LENGTH(r:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(polygonal_path q ++ linepath(b,a)))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(t UNION s') INTER (t UNION s') = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(t UNION s'))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(r:(real^2)list)` (K ALL_TAC)] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(ISPEC `CONS (a:real^2) r` th) THEN
    MP_TAC(ISPEC `CONS (b:real^2) q` th)) THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (b:real^2) q) = linepath(b,a) ++ polygonal_path q`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
    SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[PATHSTART_LINEPATH]] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {b,a}`)) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s UNION t) INTER (s UNION t) = {}
      ==> s INTER inside(s UNION t) = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    STRIP_TAC] THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (a:real^2) r) = linepath(a,b) ++ polygonal_path r`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
    SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEM; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[PATHSTART_LINEPATH]] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {a,b}`)) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s UNION t) INTER (s UNION t) = {}
      ==> t INTER inside(s UNION t) = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`polygonal_path q:real^1->real^2`;
                 `reversepath(polygonal_path r):real^1->real^2`;
                 `linepath(a:real^2,b)`; `a:real^2`; `b:real^2`]
        SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    SIMPLE_PATH_LINEPATH_EQ] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[PATH_IMAGE_REVERSEPATH; ARC_IMP_SIMPLE_PATH;
     SIMPLE_PATH_REVERSEPATH] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s INTER t SUBSET {a,b} /\
        a IN s /\ b IN s /\ a IN t /\ b IN t
        ==> s INTER t = {a,b}`) THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      UNDISCH_TAC
       `segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN MATCH_MP_TAC(SET_RULE
       `a IN t /\ b IN t /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> t INTER (s UNION {a,b}) = {a,b}`) THEN
      REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      UNDISCH_TAC
       `segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN MATCH_MP_TAC(SET_RULE
       `a IN u /\ b IN u /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> u INTER (s UNION {a,b}) = {a,b}`) THEN
      REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `s SUBSET i
        ==> inside(q UNION r) INTER (q UNION r) = {} /\
            inside(q UNION r) = i /\
            ~(s = {})
            ==> ~((s UNION {a,b}) INTER inside(q UNION r) = {})`)) THEN
      ASM_REWRITE_TAC[INSIDE_NO_OVERLAP; SEGMENT_EQ_EMPTY] THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN]];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
   check (free_in `measure:(real^2->bool)->real` o concl))) THEN
  UNDISCH_TAC
   `segment(a:real^2,b) SUBSET
    inside(path_image (polygonal_path q ++ polygonal_path r))` THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[PATH_IMAGE_REVERSEPATH; PATH_IMAGE_LINEPATH] THEN
  SUBST1_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
  REPEAT STRIP_TAC THEN SUBST1_TAC(SYM(ASSUME
   `inside(path_image(polygonal_path q) UNION segment [a,b]) UNION
    inside(path_image(polygonal_path r) UNION segment [a,b]) UNION
    (segment [a:real^2,b] DIFF {a, b}) =
    inside
     (path_image(polygonal_path q) UNION path_image(polygonal_path r))`)) THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN (s UNION t) /\ P x} =
    {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `measure(inside(path_image(polygonal_path q) UNION segment[a:real^2,b])) +
    measure(inside(path_image (polygonal_path r) UNION segment [a,b]) UNION
            segment [a,b] DIFF {a, b})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INSIDE THEN
      MATCH_MP_TAC COMPACT_UNION THEN
      SIMP_TAC[COMPACT_PATH_IMAGE; COMPACT_SEGMENT; PATH_POLYGONAL_PATH];
      MATCH_MP_TAC MEASURABLE_UNION THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_INSIDE THEN
        MATCH_MP_TAC COMPACT_UNION THEN
        SIMP_TAC[COMPACT_PATH_IMAGE; COMPACT_SEGMENT; PATH_POLYGONAL_PATH];
        MATCH_MP_TAC MEASURABLE_DIFF THEN CONJ_TAC THEN
        MATCH_MP_TAC MEASURABLE_COMPACT THEN REWRITE_TAC[COMPACT_SEGMENT] THEN
        MATCH_MP_TAC FINITE_IMP_COMPACT THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]];
      ASM_REWRITE_TAC[UNION_OVER_INTER; UNION_EMPTY] THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `segment[a:real^2,b]` THEN
      REWRITE_TAC[NEGLIGIBLE_SEGMENT_2] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `measure(inside(path_image(polygonal_path q) UNION segment[a:real^2,b])) +
    measure(inside(path_image(polygonal_path r) UNION segment[a,b]))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `segment[a:real^2,b]` THEN
    REWRITE_TAC[NEGLIGIBLE_SEGMENT_2] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION segment[a,b] = segment[a,b] UNION s`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `CARD({x | x IN inside(segment[a,b] UNION path_image(polygonal_path q)) /\
              integral_vector x} UNION
         {x | x IN inside(segment[a,b] UNION path_image(polygonal_path r)) /\
              integral_vector x} UNION
         {x | x IN segment[a,b] DIFF {a, b} /\ integral_vector x}) =
    CARD {x | x IN inside(segment[a,b] UNION path_image(polygonal_path q)) /\
              integral_vector x} +
    CARD {x | x IN inside(segment[a,b] UNION path_image(polygonal_path r)) /\
              integral_vector x} +
    CARD {x:real^2 | x IN segment[a,b] DIFF {a, b} /\ integral_vector x}`
  SUBST1_TAC THENL
   [(CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS; FINITE_UNION;
      BOUNDED_INSIDE; BOUNDED_UNION; BOUNDED_SEGMENT;
      BOUNDED_PATH_IMAGE; BOUNDED_DIFF; PATH_POLYGONAL_PATH] THEN
    MATCH_MP_TAC(ARITH_RULE
     `pr = 0 /\ qrp = 0 ==> (q + (r + p) - pr) - qrp = q + r + p`) THEN
    REWRITE_TAC[UNION_OVER_INTER] THEN
    REWRITE_TAC[SET_RULE
     `{x | x IN s /\ P x} INTER {x | x IN t /\ P x} =
      {x | x IN (s INTER t) /\ P x}`] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE
     [SET_RULE `s UNION segment[a,b] = segment[a,b] UNION s`]) THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; UNION_EMPTY] THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
    MATCH_MP_TAC(SET_RULE
     `inside(s UNION t) INTER (s UNION t) = {}
      ==> {x | x IN inside(s UNION t) INTER (s DIFF ab) /\ P x} = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
   `q + r = &2 * x + y + &2
    ==> (iq + q / &2 - &1) + (ir + r / &2 - &1) =
        ((iq + ir + x) + y / &2 - &1)`) THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN (s UNION t) /\ P x} =
    {x | x IN s /\ P x} UNION {x | x IN t /\ P x}`] THEN
  (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [CARD_UNION_GEN; FINITE_BOUNDED_INTEGER_POINTS; BOUNDED_SEGMENT;
    BOUNDED_PATH_IMAGE; PATH_POLYGONAL_PATH; GSYM REAL_OF_NUM_SUB;
    INTER_SUBSET; CARD_SUBSET; ARITH_RULE `x:num <= y ==> x <= y + z`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
   `&2 * ab + qr = &2 * x + qab + rab + &2
    ==> ((ab + q) - qab) + ((ab + r) - rab) =
        &2 * x + ((q + r) - qr) + &2`) THEN
  SUBGOAL_THEN
   `{x | x IN segment[a,b] /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path q) /\ integral_vector x} = {a,b} /\
    {x:real^2 | x IN segment[a,b] /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path r) /\ integral_vector x} = {a,b}`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET inside(q UNION r)
      ==> s = c DIFF {a,b} /\ a IN q /\ b IN q /\ a IN r /\ b IN r /\
          inside(q UNION r) INTER (q UNION r) = {} /\
          P a /\ P b /\ a IN c /\ b IN c
          ==> {x | x IN c /\ P x} INTER {x | x IN q /\ P x} = {a,b} /\
              {x | x IN c /\ P x} INTER {x | x IN r /\ P x} = {a,b}`)) THEN
    ASM_REWRITE_TAC[open_segment; INSIDE_NO_OVERLAP; ENDS_IN_SEGMENT] THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:real^2 | x IN path_image(polygonal_path q) /\ integral_vector x} INTER
    {x | x IN path_image(polygonal_path r) /\ integral_vector x} = {a,b}`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      SIMPLE_PATH_JOIN_IMP)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC(SET_RULE
     `P a /\ P b /\ a IN q /\ b IN q /\ a IN r /\ b IN r
      ==> (q INTER r) SUBSET {a,b}
          ==> {x | x IN q /\ P x} INTER {x | x IN r /\ P x} = {a,b}`) THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = y + &2 ==> &2 * x + &2 = &2 * y + &2 + &2 + &2`) THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  SUBGOAL_THEN `(segment(a,b) UNION {a, b}) DIFF {a, b} = segment(a:real^2,b)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(a IN s) /\ ~(b IN s) ==> (s UNION {a,b}) DIFF {a,b} = s`) THEN
    REWRITE_TAC[open_segment; IN_DIFF] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SET_RULE
   `P a /\ P b
    ==> {x | x IN s UNION {a,b} /\ P x} =
        a INSERT b INSERT {x | x IN s /\ P x}`] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_BOUNDED_INTEGER_POINTS;
           BOUNDED_SEGMENT; FINITE_INSERT] THEN
  ASM_REWRITE_TAC[IN_INSERT; IN_ELIM_THM; ENDS_NOT_IN_SEGMENT] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; ARITH_RULE `SUC(SUC n) = n + 2`]);;
```

### Informal statement
Let $p$ be a list of points in $\mathbb{R}^2$. If all points in $p$ have integer coordinates, and the polygonal path formed by $p$ is a simple closed path, then the area of the region enclosed by this path is given by:

$$\text{area}(\text{inside}(\text{path\_image}(\text{polygonal\_path}(p)))) = I + \frac{B}{2} - 1$$

where:
- $I$ is the number of integer points (points with integer coordinates) strictly inside the polygon
- $B$ is the number of integer points on the boundary of the polygon

### Informal proof
The proof proceeds by strong induction on the length of the list $p$.

**Base case**: When the length of $p$ is at most 4.

We handle this by case analysis on list $p$. For empty or very short lists, the path doesn't form a proper closed polygon. When the list has exactly 3 points, we're forming a triangle. In this case, we apply the already proven `PICK_TRIANGLE` theorem, which establishes Pick's formula for triangles with integer vertices.

**Inductive step**: When the length of $p$ is at least 5.

We apply the theorem `POLYGON_CHOP_IN_TWO` which states that in any simple closed polygon with at least 5 vertices, we can find two vertices $a$ and $b$ such that the line segment $(a,b)$ lies entirely inside the polygon.

This allows us to:
1. Rotate the list $p$ so that vertex $a$ is at the start of the list
2. Partition the polygon into two smaller polygons by adding a "chord" from $a$ to $b$
3. Apply the induction hypothesis to each of the two smaller polygons
4. Combine the results to get the formula for the original polygon

Specifically, if we call the two smaller polygons $q$ and $r$, then:
- The path image of the original polygon equals the union of the path images of $q$ and $r$, with the interior of the line segment $[a,b]$ removed from both
- The areas add: $\text{area}(\text{inside}(p)) = \text{area}(\text{inside}(q)) + \text{area}(\text{inside}(r))$
- The interior integer points satisfy: $I_p = I_q + I_r + I_{ab}$ where $I_{ab}$ are the integer points on the segment $(a,b)$
- The boundary integer points satisfy: $B_p = B_q + B_r - 2$ because $a$ and $b$ are counted twice in $B_q + B_r$

Substituting these into the Pick formula for $q$ and $r$ and simplifying, we get the Pick formula for $p$.

### Mathematical insight
Pick's theorem provides a remarkably simple way to calculate the area of a polygon with integer vertices by just counting integer points. This theorem is a beautiful example of how discrete mathematics (counting lattice points) connects to continuous mathematics (area).

The proof strategy is elegant: we decompose a complex polygon into simpler ones and use induction. The base case is for triangles, where Pick's formula can be proven directly. Then, for more complex polygons, we use a "divide and conquer" approach.

The key insight is that adding a diagonal between two vertices of a polygon splits it into two smaller polygons, and we can combine the Pick formula for each to get the formula for the whole. This decomposition approach is common in computational geometry.

### Dependencies
- **Theorems**:
  - `MEASURABLE_UNION`: Union of two measurable sets is measurable
  - `MEASURABLE_DIFF`: Difference of two measurable sets is measurable
  - `MEASURE_NEGLIGIBLE_UNION`: Measure of union of sets with negligible intersection
  - `MEASURE_NEGLIGIBLE_SYMDIFF`: Equal measure for sets with negligible symmetric difference
  - `MEASURABLE_COMPACT`: Compact sets are measurable
  - `MEASURE_INTERIOR`: Measure of a set equals measure of its interior under certain conditions
  - `MEASURABLE_INSIDE`: Inside of a compact set is measurable
  - `NEGLIGIBLE_CONVEX_FRONTIER`: Frontier of a convex set is negligible
  - `SPLIT_INSIDE_SIMPLE_CLOSED_CURVE`: Theorem about splitting the inside of curves
  - `FRONTIER_OF_TRIANGLE`: Formula for the frontier of a triangle
  - `INSIDE_OF_TRIANGLE`: Formula for the inside of a triangle
  - `NEGLIGIBLE_SEGMENT_2`: A line segment in R² is negligible
  - `FINITE_BOUNDED_INTEGER_POINTS`: Finite number of integer points in a bounded set
  - `PICK_TRIANGLE`: Pick's formula for triangles
  - `POLYGON_CHOP_IN_TWO`: Allows splitting a polygon with a diagonal

- **Definitions**:
  - `measure`: The Lebesgue measure of a set
  - `integral_vector`: A vector with integer components
  - `polygonal_path`: A path made up of line segments connecting consecutive points

### Porting notes
When porting this theorem:
1. You'll need all the foundational measure theory results about negligible sets and measurable sets
2. The triangle case (`PICK_TRIANGLE`) should be proved separately first
3. The `POLYGON_CHOP_IN_TWO` theorem is critical and might need significant work to port
4. Pay attention to the handling of list rotations and polygon decomposition
5. The proof extensively uses set operations and careful tracking of integer points

The most challenging part will likely be the geometric argument for splitting a polygon and handling the boundary points correctly in the inductive step.

---

