# heron.ml

## Overview

Number of statements: 2

`heron.ml` formalizes Heron's formula for calculating the area of a triangle. The file is part of the Multivariate analysis library, building upon measure theory. It defines and proves the relationship between a triangle's side lengths and its area.


## SQRT_ELIM_TAC

### Name of formal statement
SQRT_ELIM_TAC

### Type of the formal statement
Tactical

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
The tactic `SQRT_ELIM_TAC` takes an assumption list `asl` and a goal `w` and eliminates square roots from the goal `w`. It identifies all subterms in `w` that have the form `sqrt(t)` for some term `t`. For each such subterm `sqrt(t)`, it performs the following steps: first, it uses the theorem `SQRT_POW_2` to replace `sqrt(t)` with a variable, then it specializes the goal to introduce this variable.

### Informal sketch
The tactic `SQRT_ELIM_TAC` aims to eliminate square roots in a goal by replacing `sqrt(t)` with a fresh variable `v` and introducing the equation `v = sqrt(t)`.

- Find all subterms of the form `sqrt(t)` in the goal `w`.
- For each such subterm `sqrt(t)`, generate a fresh variable `v` of the same type as `t`.
- Introduce the equation `v = sqrt(t)` using the theorem `SQRT_POW_2` and modus ponens. The theorem `SQRT_POW_2` likely states something equivalent to `!(x:real). sqrt(x) pow 2 = x`, so applying `SPEC` and `MP_TAC` with this theorem will replace `sqrt(t)` with the variable.
- Specialize the goal with the identified subterms and corresponding generated variables using `SPEC_TAC`. This replaces each occurrence of `sqrt(t)` with `v`.

### Mathematical insight
The tactic provides a way to eliminate square roots from formulas by introducing new variables and equations, facilitating further reasoning or simplification within the formal system. Replacing complex terms involving `sqrt` with simple variables helps to clarify the formula. Commonly, this is a preliminary step to manipulate expressions where square roots create difficulty for automated reasoning.

### Dependencies
- `sqrt:real->real`
- `SQRT_POW_2`

### Porting notes (optional)
- The tactic relies on finding all subterms of a specific form, which may require different approaches in different proof assistants.
- The `SQRT_POW_2` theorem and its application via `SPEC` and `MP_TAC` need to be carefully translated, ensuring the equivalent replacement of square roots in the target system.


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
For all real vectors `A`, `B`, and `C` in the 2-dimensional real space, let `a` be the distance between `C` and `B`, `b` be the distance between `A` and `C`, and `c` be the distance between `B` and `A`. Let `s` be equal to `(a + b + c) / 2`. Then the measure (area) of the convex hull of the set containing `A`, `B`, and `C` is equal to the square root of `s * (s - a) * (s - b) * (s - c)`.

### Informal sketch
The proof demonstrates Heron's formula for the area of a triangle.
- The proof starts by expanding the definitions of the `let` bindings.
- It then uses `MEASURE_TRIANGLE` to express the area of the triangle.
- It uses `SQRT_UNIQUE` to reduce the goal to showing the square of both sides are equal, appealing to uniqueness of square root.
- Simplification steps are performed using several theorems related to real numbers, such as `REAL_LE_DIV`, `REAL_ABS_POS`, and `REAL_POS`, to establish positivity conditions.
- The definitions of `dist` and `vector_norm` are expanded.
- The definition of `dot` product and `SUM_2` along with indexing `DIMINDEX_2` are used to convert the geometric expression into an algebraic expression.
- Further simplification involves vector subtraction, arithmetic, and properties of real numbers.
- Finally, the proof uses the `REAL_RING` conversion to automatically prove the equality of the remaining real-valued expressions. This completes the proof.

### Mathematical insight
Heron's formula provides a way to calculate the area of a triangle given only the lengths of its sides. It's a fundamental result in geometry, connecting distance measurements to area. This theorem demonstrates a formal proof of Heron's formula within HOL Light, leveraging vector operations and real analysis.

### Dependencies
- `dist`
- `vector_norm`
- `dot`
- `MEASURE_TRIANGLE`
- `SQRT_UNIQUE`
- `REAL_LE_DIV`
- `REAL_ABS_POS`
- `REAL_POS`
- `REAL_POW_DIV`
- `REAL_POW2_ABS`
- `VECTOR_SUB_COMPONENT`
- `REAL_LE_SQUARE`
- `REAL_LE_ADD`
- `REAL_RING`
- `SUM_2`
- `DIMINDEX_2`


---

