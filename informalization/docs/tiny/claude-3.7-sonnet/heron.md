# heron.ml

## Overview

Number of statements: 2

This HOL Light file provides a formalization of Heron's formula, which calculates the area of a triangle given the lengths of its three sides. Building on the multivariate measure infrastructure, it develops the necessary geometric theory and proves that the area of a triangle with sides a, b, and c equals √(s(s-a)(s-b)(s-c)) where s is the semi-perimeter (a+b+c)/2. The file serves as a standalone mathematical result that demonstrates the application of measure theory to computational geometry.

## SQRT_ELIM_TAC

### Name of formal statement
SQRT_ELIM_TAC

### Type of the formal statement
Custom tactic definition

### Formal Content
```ocaml
let SQRT_ELIM_TAC =
  let sqrt_tm = `sqrt:real->real` in
  let is_sqrt tm = is_comb tm && rator tm = sqrt_tm in
  fun (asl,w) ->
    let stms = setify(find_terms is_sqrt w) in
    let gvs = map (genvar o type_of) stms in
    (MAP_EVERY (MP_TAC o C SPEC SQRT_POW_2 o rand) stms THEN
     EVERY (map2 (fun s v -> SPEC_TAC(s,v)) stms gvs)) (asl,w);;
```

### Informal statement
`SQRT_ELIM_TAC` is a custom tactic that eliminates square roots from the goal formula. It works by:

1. Finding all terms of the form `sqrt t` in the goal formula
2. For each such term, applying the theorem `SQRT_POW_2` which states that `sqrt(x) ^ 2 = x` for real numbers
3. Replacing the square root terms with fresh variables and introducing the corresponding constraints

### Informal proof
This is a tactic definition rather than a theorem, so there is no proof. The tactic operates as follows:

- It identifies all subterms in the goal formula that have the form `sqrt t` where `sqrt` is the square root function on real numbers
- For each identified square root term `sqrt t`, it:
  1. Applies the `SQRT_POW_2` theorem using `MP_TAC` to introduce the equation `sqrt(t)^2 = t`
  2. Creates a fresh variable of the appropriate type using `genvar`
  3. Uses `SPEC_TAC` to replace the square root term with this fresh variable

This approach is a standard technique for eliminating square roots from goals, making them more amenable to algebraic manipulation.

### Mathematical insight
This tactic implements a common mathematical technique for working with square roots: introduce a new variable to represent each square root expression, and work with the property that the square of that variable equals the original expression under the square root.

This technique is particularly useful in proofs involving geometric formulas (such as Heron's formula mentioned in the comment) where square roots often appear. By eliminating square roots, one can transform a goal with irrational expressions into purely algebraic relations, which are often easier to manipulate using standard algebraic techniques.

The comment suggests this tactic is being used in the context of proving Heron's formula for the area of a triangle, which involves square roots in its standard formulation.

### Dependencies
- `SQRT_POW_2`: A theorem stating that for real numbers, `sqrt(x)^2 = x`

### Porting notes
When porting this tactic:
- Ensure the target system has an analogous theorem to `SQRT_POW_2`
- The implementation relies on HOL Light's tactical combinators like `MAP_EVERY` and `EVERY` - adapt these to equivalent combinators in the target system
- The term traversal using `find_terms` might need to be reimplemented according to the target system's term representation
- The variable generation using `genvar` needs to be mapped to the target system's fresh variable creation mechanism

---

## HERON

### Name of formal statement
HERON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HERON = prove
 (`!A B C:real^2.
        let a = dist(C,B)
        and b = dist(A,C)
        and c = dist(B,A) in
        let s = (a + b + c) / &2 in
        measure(convex hull {A,B,C}) = sqrt(s * (s - a) * (s - b) * (s - c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[MEASURE_TRIANGLE] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SQRT_UNIQUE THEN
  SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS; REAL_POS] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_POW2_ABS] THEN
  REWRITE_TAC[dist; vector_norm] THEN
  REWRITE_TAC[dot; SUM_2; DIMINDEX_2] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; ARITH; DIMINDEX_2] THEN
  SQRT_ELIM_TAC THEN SIMP_TAC[REAL_LE_SQUARE; REAL_LE_ADD] THEN
  CONV_TAC REAL_RING);;
```

### Informal statement
For any three points $A$, $B$, $C$ in $\mathbb{R}^2$, let:
- $a = \text{dist}(C, B)$ be the distance between points $C$ and $B$
- $b = \text{dist}(A, C)$ be the distance between points $A$ and $C$
- $c = \text{dist}(B, A)$ be the distance between points $B$ and $A$
- $s = \frac{a + b + c}{2}$ be the semi-perimeter of the triangle

Then the area of the triangle formed by these points is given by:
$$\text{measure}(\text{convex hull }\{A, B, C\}) = \sqrt{s(s-a)(s-b)(s-c)}$$

This is the famous Heron's formula for the area of a triangle.

### Informal proof
The proof proceeds by algebraic manipulation:

1. We start by rewriting the area using `MEASURE_TRIANGLE`, which states that the area of a triangle is $\frac{1}{2}$ times the absolute value of the determinant formed by two sides of the triangle: 
   $$\text{measure}(\text{convex hull }\{A, B, C\}) = \frac{1}{2}|((B_1 - A_1)(C_2 - A_2) - (B_2 - A_2)(C_1 - A_1))|$$

2. We then apply symmetry conversion and use `SQRT_UNIQUE` to show that the square of Heron's formula equals the square of the area.

3. Next, we rewrite terms involving distance, vector norm, and dot products according to their definitions.

4. We use `SQRT_ELIM_TAC` to eliminate the square root and reduce to showing an equality between squared expressions.

5. Finally, we apply real algebraic simplifications to prove that the squared expressions are indeed equal.

This proof effectively shows that Heron's formula is equivalent to the standard formula for the area of a triangle using the cross product of two sides.

### Mathematical insight
Heron's formula provides an elegant way to compute the area of a triangle using only the lengths of its sides, without requiring coordinates or angles. This is one of the oldest and most famous formulas in geometry, dating back to Heron of Alexandria (c. 10-70 CE).

The formula is particularly valuable because:
1. It depends only on the side lengths of the triangle
2. It works for any triangle, regardless of its shape or orientation
3. It has extensive applications in computational geometry, physics, and engineering

While the standard formula for triangle area involves a determinant or cross product, Heron's formula provides a direct calculation from the three sides, making it useful in situations where only distances are known.

### Dependencies
- **Theorems:**
  - `MEASURE_TRIANGLE`: Provides the standard formula for the area of a triangle in terms of coordinates
- **Definitions:**
  - `measure`: Gives the measure (area) of a set

### Porting notes
When porting this theorem:
1. Ensure the target system has a robust theory of Euclidean geometry with concepts of distance, convex hull, and measure already established
2. The algebraic manipulations are fairly involved, so the target system will need good support for real algebraic simplification
3. Be aware that the HOL Light proof relies heavily on conversions and tactics specific to real arithmetic; in other systems, you might need to be more explicit about algebraic steps
4. The proof transformation from the determinant formula to Heron's formula is not trivial and may require significant algebraic manipulation in other systems

---

