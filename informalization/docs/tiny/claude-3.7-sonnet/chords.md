# chords.ml

## Overview

Number of statements: 5

This file formalizes a theorem about the product of segments of chords in Euclidean geometry. It proves that when two chords intersect inside a circle, the product of the segments of one chord equals the product of the segments of the other chord. The proof builds on the multivariate analysis and convex geometry framework from the HOL Light library, particularly leveraging results about circles and geometric constructions.

## BETWEEN_THM

### BETWEEN_THM
- State the exact name of the formal item as it appears in the HOL Light source.

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
This theorem establishes a characterization of the `between` relation:

For points $x$, $a$, and $b$ in a real vector space $\mathbb{R}^N$, $x$ is between $a$ and $b$ (denoted as `between x (a,b)`) if and only if there exists a real number $u$ such that $0 \leq u \leq 1$ and $x = u \cdot a + (1 - u) \cdot b$.

### Informal proof
The proof establishes the equivalence by showing that the `between` relation is equivalent to a point being in the convex hull of two points, which has a known parametric characterization:

- Start by applying `BETWEEN_IN_CONVEX_HULL`, which states that $x$ is between $a$ and $b$ if and only if $x$ is in the convex hull of $\{a, b\}$.
- Use `SET_RULE` to rewrite $\{a, b\}$ as $\{b, a\}$ (since sets are unordered).
- Apply `CONVEX_HULL_2_ALT`, which states that the convex hull of two points $\{b, a\}$ can be expressed as $\{b + u \cdot (a - b) \mid 0 \leq u \leq 1\}$.
- Simplify the resulting set membership condition using `IN_ELIM_THM`.
- Perform algebraic manipulation to show that $b + u \cdot (a - b) = u \cdot a + (1 - u) \cdot b$.
- This completes the proof that $x$ is between $a$ and $b$ if and only if it can be expressed as a convex combination of $a$ and $b$ with parameter $u$.

### Mathematical insight
This theorem provides an algebraic characterization of the geometric concept of "betweenness." Intuitively, a point $x$ is between $a$ and $b$ if it lies on the line segment connecting $a$ and $b$.

The parametric representation $x = u \cdot a + (1 - u) \cdot b$ with $0 \leq u \leq 1$ is particularly useful because:
1. It expresses $x$ as a convex combination of $a$ and $b$
2. The parameter $u$ can be interpreted as the relative position of $x$ along the line segment from $b$ to $a$:
   - When $u = 0$, $x = b$
   - When $u = 1$, $x = a$
   - When $0 < u < 1$, $x$ is strictly between $a$ and $b$

This characterization is fundamental in computational geometry, linear interpolation, and convex analysis.

### Dependencies
- **Theorems**:
  - `BETWEEN_IN_CONVEX_HULL`: States that a point $x$ is between points $a$ and $b$ if and only if $x$ is in the convex hull of $\{a, b\}$
  - `CONVEX_HULL_2_ALT`: Provides an alternative parametric description of the convex hull of two points
- **HOL Light rules**:
  - `SET_RULE`
  - `IN_ELIM_THM`
  - `VECTOR_ARITH_TAC`

### Porting notes
When porting this theorem:
1. Ensure your target system has a definition of "betweenness" that aligns with HOL Light's `between` relation
2. The proof relies on convex hull properties, so those theorems need to be ported first
3. The vector arithmetic simplifications might need different approaches depending on the target system's automation
4. Be aware that HOL Light's `%` notation is used for scalar multiplication, which might have different syntax in other systems

---

## length

### length

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let length = new_definition
 `length(A:real^2,B:real^2) = norm(B - A)`;;
```

### Informal statement
The function `length` is defined for two points $A$ and $B$ in $\mathbb{R}^2$ as:
$$\text{length}(A, B) = \|B - A\|$$
where $\|\cdot\|$ denotes the Euclidean norm.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition formalizes the standard notion of the Euclidean distance between two points in the plane. The length of the line segment from point $A$ to point $B$ is computed using the Euclidean norm of the vector from $A$ to $B$. 

This is a fundamental geometric concept used in various contexts, such as:
- Calculating distances between points in the plane
- Measuring the length of line segments
- Computing perimeters of polygons

The definition uses vector subtraction followed by a norm calculation, which is the standard approach to defining distance in Euclidean spaces.

### Dependencies
- The definition relies on the `norm` function, which computes the Euclidean norm of a vector.
- It also uses vector subtraction to calculate the displacement vector between two points.

### Porting notes
When porting to other proof assistants:
- Ensure the target system has an appropriate definition of Euclidean norm for vectors
- Check how vector spaces are represented in the target system
- Verify type compatibility between points and vectors in the target system

---

## lemma

### Name of formal statement
lemma

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (x pow 2 = y pow 2 <=> x = y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[REAL_POW_2] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THEN
  ASM_MESON_TAC[REAL_LT_MUL2; REAL_LT_REFL]);;
```

### Informal statement
For all real numbers $x$ and $y$, if $0 \leq x$ and $0 \leq y$, then $x^2 = y^2$ if and only if $x = y$.

### Informal proof
The proof establishes that for non-negative real numbers, having equal squares implies the numbers themselves are equal:

* First, apply the equivalence in both directions (using `EQ_TAC`):
  * The forward direction ($x = y \Rightarrow x^2 = y^2$) is handled by simplification using the definition of square (`REAL_POW_2`).
  * For the reverse direction ($x^2 = y^2 \Rightarrow x = y$), we:
    * Apply the law of trichotomy for reals (`REAL_LT_TOTAL`) to consider all possible ordering relationships between $x$ and $y$.
    * Use `ASM_MESON_TAC` with properties of real multiplication (`REAL_LT_MUL2`) and the irreflexivity of the less-than relation (`REAL_LT_REFL`) to establish that $x$ must equal $y$.

The key insight is that when both numbers are non-negative, the only way their squares can be equal is if the numbers themselves are equal.

### Mathematical insight
This lemma provides a simplification for working with squared terms in real analysis. It allows us to directly reason about equality of non-negative real numbers by examining their squares, avoiding the need to use square roots. This is particularly useful in contexts where we need to eliminate radicals or when working with distances in Euclidean spaces.

The non-negativity constraint is essential - without it, the statement would be false since $(-a)^2 = a^2$ for any real $a$.

### Dependencies
#### Theorems
- `REAL_POW_2` - Definition of real number squared as multiplication
- `REAL_LT_TOTAL` - Trichotomy law for real numbers (for any two reals, exactly one of $a < b$, $a = b$, or $a > b$ holds)
- `REAL_LT_MUL2` - Multiplication preserves order for positive reals
- `REAL_LT_REFL` - Irreflexivity of the less-than relation

### Porting notes
This lemma should be straightforward to port to other systems. Most proof assistants have built-in libraries for real numbers with similar properties. The proof relies on basic properties of ordered fields that are standard across mathematical libraries.

In systems with more automation for real arithmetic (like Isabelle or Coq), this might be provable with simpler tactics or might already exist in the standard library.

---

## NORM_CROSS

### Name of formal statement
NORM_CROSS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NORM_CROSS = prove
 (`norm(a) * norm(b) = norm(c) * norm(d) <=>
   (a dot a) * (b dot b) = (c dot c) * (d dot d)`,
  REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC(GSYM lemma) THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL]);;
```

### Informal statement
For vectors $a$, $b$, $c$, and $d$, we have:
$$\|a\| \cdot \|b\| = \|c\| \cdot \|d\| \iff (a \cdot a) \cdot (b \cdot b) = (c \cdot c) \cdot (d \cdot d)$$

where $\|\cdot\|$ denotes the norm of a vector, and $\cdot$ denotes the dot product between vectors.

### Informal proof
The proof proceeds as follows:

1. First, we rewrite using the identity relating norm squared to dot product: $\|v\|^2 = v \cdot v$ (theorem `NORM_POW_2`).
2. We also use the fact that $(x \cdot y)^2 = x^2 \cdot y^2$ (theorem `REAL_POW_MUL`).
3. After these rewrites, we apply an unnamed lemma which appears to establish that for non-negative real numbers, equality of squares implies equality of the original numbers.
4. We complete the proof by noting that norms are always non-negative (`NORM_POS_LE`) and products of non-negative numbers are non-negative (`REAL_LE_MUL`).

### Mathematical insight
This theorem establishes the equivalence between comparing products of vector norms and comparing products of squared norms (expressed as dot products). This is useful in vector algebra when manipulating expressions involving norms, allowing transformation between different forms.

The result is straightforward but provides a convenient way to convert between vector norm products and dot product expressions, which can simplify proofs in vector analysis and geometry.

### Dependencies
- Theorems:
  - `NORM_POW_2`: Relates the square of a norm to the dot product: $\|v\|^2 = v \cdot v$
  - `REAL_POW_MUL`: Relates powers of products: $(x \cdot y)^2 = x^2 \cdot y^2$
  - `lemma`: (unnamed) Appears to show that for non-negative reals, if squares are equal, the original values are equal
  - `NORM_POS_LE`: States that norms are non-negative
  - `REAL_LE_MUL`: States that product of non-negative reals is non-negative

### Porting notes
When porting this theorem, ensure that the target system:
- Has an established definition of vector norms
- Has dot product operations defined for vectors
- Has theorems relating norm squared to dot products
- Has appropriate support for real number properties

The proof is straightforward and should transfer easily to systems with standard vector algebra libraries.

---

## SEGMENT_CHORDS

### Name of formal statement
SEGMENT_CHORDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SEGMENT_CHORDS = prove
 (`!centre radius q r s t b.
        between b (q,r) /\ between b (s,t) /\
        length(q,centre) = radius /\ length(r,centre) = radius /\
        length(s,centre) = radius /\ length(t,centre) = radius
        ==> length(q,b) * length(b,r) = length(s,b) * length(b,t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[length; NORM_CROSS; BETWEEN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) MP_TAC) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
   (MP_TAC o AP_TERM `\x. x pow 2`)) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[NORM_POW_2] THEN
  ABBREV_TAC `rad = radius pow 2` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
           CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For any circle with center `centre` and radius `radius`, if two chords of the circle intersect at a point `b`, where:
- `b` lies between points `q` and `r` on one chord
- `b` lies between points `s` and `t` on the other chord
- All points `q`, `r`, `s`, and `t` lie on the circle (i.e., have distance `radius` from `centre`)

Then the product of the segments of one chord equals the product of the segments of the other chord:
$\text{length}(q,b) \cdot \text{length}(b,r) = \text{length}(s,b) \cdot \text{length}(b,t)$

### Informal proof
This proof establishes the Power of a Point theorem for two intersecting chords of a circle.

- The proof begins by expanding the definitions of `length` (which gives the Euclidean distance between two points) and `BETWEEN_THM` (which characterizes when a point lies between two other points).
- By `BETWEEN_THM`, a point `b` is between points `q` and `r` if there exists a real number `u` where $0 \leq u \leq 1$ such that $b = (1-u)q + ur$.
- Similarly, `b` is between points `s` and `t` if there exists a real number `v` where $0 \leq v \leq 1$ such that $b = (1-v)s + vt$.
- The proof applies these parameterizations to express the points in terms of the parameters `u` and `v`.
- For the points on the circle, we have $\|q-\text{centre}\|^2 = \|r-\text{centre}\|^2 = \|s-\text{centre}\|^2 = \|t-\text{centre}\|^2 = \text{radius}^2$.
- The squared distance terms are expanded using `NORM_POW_2` and the dot product definition.
- The proof abbreviates $\text{radius}^2$ as `rad` for simplicity.
- The vector operations are simplified by working with components, using `VECTOR_SUB_COMPONENT`, `VECTOR_ADD_COMPONENT`, and `VECTOR_MUL_COMPONENT`.
- The final algebraic manipulation is handled by the `REAL_RING` conversion, which completes the proof by verifying the required equality.

### Mathematical insight
This theorem establishes the Power of a Point theorem for intersecting chords of a circle. The key insight is that when two chords of a circle intersect, the product of the segments of one chord equals the product of the segments of the other chord. 

This is a fundamental result in Euclidean geometry and has numerous applications, including in constructive geometry and for proving other geometric theorems about circles.

The theorem can be visualized as follows: if we draw two lines through any point inside a circle, each intersecting the circle at two points, then the products of the segments formed on each line (from the internal point to each intersection with the circle) are equal.

This property is sometimes called the "chord-chord power theorem" and is a special case of the power of a point theorem, which also applies to points outside the circle.

### Dependencies
- Geometric definitions:
  - `length`: Euclidean distance between two points
  - `BETWEEN_THM`: Characterization of when a point lies between two others
  - `NORM_CROSS`: Norm of the cross product
  - `dot`: Dot product of vectors
  - `NORM_POW_2`: Square of the norm

- Vector operations:
  - `VECTOR_SUB_COMPONENT`
  - `VECTOR_ADD_COMPONENT`
  - `VECTOR_MUL_COMPONENT`

### Porting notes
When porting this theorem:
1. Ensure your target system has appropriate definitions for Euclidean geometry in 2D space, including vectors, distances, and the "betweenness" relation.
2. The proof relies heavily on algebraic manipulation of vector equations. Your target system needs strong support for algebraic reasoning about vectors and real numbers.
3. The HOL Light `REAL_RING` tactic handles the final algebraic verification - this might need to be replaced with a more explicit calculation in systems with weaker automation.
4. The theorem statement uses HOL Light's `length` function which computes Euclidean distance - make sure to use the equivalent in your target system.

---

