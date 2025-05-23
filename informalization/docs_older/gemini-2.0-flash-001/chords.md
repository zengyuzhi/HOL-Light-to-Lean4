# chords.ml

## Overview

Number of statements: 5

The file `chords.ml` formalizes Theorem #55 concerning the product of segments of chords within a circle. It imports `Multivariate/convex.ml`, suggesting the use of convex geometry concepts in proving the theorem. The file essentially provides a formal proof of a classical geometric result related to intersecting chords in a circle.


## BETWEEN_THM

### Name of formal statement
BETWEEN_THM

### Type of the formal statement
theorem

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
For any real vector `x` and any pair of real vectors `a` and `b`, `x` lies between `a` and `b` if and only if there exists a real number `u` such that `0 <= u <= 1` and `x = u * a + (1 - u) * b`.

### Informal sketch
The proof proceeds as follows:
- Rewrite using `BETWEEN_IN_CONVEX_HULL` to express `between x (a, b)` in terms of `x IN convex_hull {a, b}`.
- Rewrite using `SET_RULE `{a,b} = {b,a}`` for set equality.
- Rewrite using `CONVEX_HULL_2_ALT` and `IN_ELIM_THM` to express `x IN convex_hull {a, b}` as the existence of `u` such that `0 <= u <= 1` and `x = u % a + (&1 - u) % b`.
- Apply `AP_TERM_TAC`, `ABS_TAC`, and `REWRITE_TAC[CONJ_ASSOC]` to massage the goal.
- Apply `AP_TERM_TAC` followed by `VECTOR_ARITH_TAC` to complete the proof by vector arithmetic.

### Mathematical insight
This theorem formalizes the concept of `x` lying between two vectors `a` and `b`. It is equivalent to saying `x` is on the line segment connecting `a` and `b`. The scalar `u` represents the proportion of the distance from `a` to `b` at which `x` is located. This is a crucial concept in convex geometry and linear interpolation.

### Dependencies
- `BETWEEN_IN_CONVEX_HULL`
- `CONVEX_HULL_2_ALT`
- `IN_ELIM_THM`
- `SET_RULE `{a,b} = {b,a}``
- `CONJ_ASSOC`

### Porting notes (optional)
The key is to ensure that the definitions of `between`, `convex_hull`, and set membership (`IN`) are consistent with those in HOL Light. The `VECTOR_ARITH_TAC` indicates that an automated tactic for vector arithmetic is needed, and this may need to be adapted depending on the target proof assistant. Handling of real numbers and their arithmetic needs to be checked.


---

## length

### Name of formal statement
length

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let length = new_definition
 `length(A:real^2,B:real^2) = norm(B - A)`;;
```

### Informal statement
The length of a line segment between two points `A` and `B`, both of type `real^2` (i.e., points in a 2D real space), is defined as the norm of the vector resulting from subtracting point `A` from point `B`.

### Informal sketch
- The definition introduces a function `length` that takes two points in `real^2` as input.
- It calculates the vector `B - A` which represents the displacement from point `A` to point `B`.
- It then computes the Euclidean norm (magnitude) of this vector using the `norm` function, effectively giving the distance between the two points.
- The definition directly applies the standard formula for Euclidean distance in 2D space.

### Mathematical insight
The `length` definition formalizes the intuitive notion of the distance between two points in a 2D Euclidean space. It is a fundamental concept in geometry and vector algebra, representing the magnitude of the displacement vector connecting the two points. This definition relies on the vector subtraction and the concept of a norm, which provides a measure of length.

### Dependencies
- Definitions: `norm`


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
For all real numbers `x` and `y`, if `0 <= x` and `0 <= y`, then `x` squared is equal to `y` squared if and only if `x` equals `y`.

### Informal sketch
The proof proceeds by first stripping quantifiers and implications. Then, equality is used to break down the equivalence into two implications. The rewriting rule `REAL_POW_2` is used to rewrite `x pow 2` to `x * x` and `y pow 2` to `y * y`.
- To prove `x * x = y * y ==> x = y`, the assumption `REAL_LT_TOTAL` (which states that for any real numbers `x` and `y`, either `x < y`, `x = y`, or `y < x`) is used with cases, specifically on `x` and `y`.
- Case 1: `x < y`. Then `x*x < y*y` (using `REAL_LT_MUL2` and the assumption that `0 <= x` and `0 <= y`), which contradicts the hypothesis `x*x = y*y`.
- Case 2: `y < x`. Then `y*y < x*x` (using `REAL_LT_MUL2` and the assumption that `0 <= x` and `0 <= y`), which contradicts the hypothesis `x*x = y*y`.
- Case 3: `x = y`. This proves the implication `x * x = y * y ==> x = y`.
- For the reverse implication `x = y ==> x * x = y * y`, it uses reflexivity `REAL_LT_REFL`.

### Mathematical insight
This lemma provides a condition to avoid square roots when comparing two real numbers for equality. That is, if two non-negative real numbers have the same square, then they must be the same number. This is frequently useful when manipulating inequalities and equations, especially in situations where one wants to avoid the introduction of square roots.

### Dependencies
- `REAL_POW_2`
- `REAL_LT_TOTAL`
- `REAL_LT_MUL2`
- `REAL_LT_REFL`


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
For any real numbers `a`, `b`, `c`, and `d`, the product of the norms of `a` and `b` equals the product of the norms of `c` and `d` if and only if the product of the squares of `a` and `b` equals the product of the squares of `c` and `d`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the norms using `NORM_POW_2` (in reverse) to express `norm(x)` as `sqrt(x dot x)`.
- Rewrite using `REAL_POW_MUL` (in reverse) to convert `(sqrt(a dot a) * sqrt(b dot b) = sqrt(c dot c) * sqrt(d dot d))` to `sqrt((a dot a) * (b dot b)) = sqrt((c dot c) * (d dot d))`.
- Apply `lemma` to remove the square roots. The exact form of `lemma` is unclear with the provided information. It likely states an equivalence between equality of square roots and equality of their squared arguments.
- Simplify using `NORM_POS_LE` to state that norms are non-negative.
- Then simplify using `REAL_LE_MUL`.

### Mathematical insight
This theorem establishes the equivalence between equality of products of norms and the equality of products of squared dot products. This is useful because working with squared dot products avoids square roots, which can simplify certain calculations and comparisons.  The underlying math relies on the non-negativity of the norms and the square root function, ensuring that taking the square root is a reversible operation in this context.

### Dependencies
- Theorems:
  - `NORM_POW_2`
  - `REAL_POW_MUL`
  - `NORM_POS_LE`
  - `REAL_LE_MUL`

### Porting notes (optional)
The tactic `MATCH_MP_TAC(GSYM lemma)` presupposes `lemma`. Identifying or recreating the precise statement of `lemma` that makes this proof work may be crucial for porting. The lemmas used here are related to properties of square roots and their relationship to inequalities with non-negative real numbers. Therefore, the target proof assistant must also have similarly sufficient theorems available.


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
For any point `centre`, radius `radius`, points `q`, `r`, `s`, `t`, and `b`, if `b` lies between `q` and `r`, `b` lies between `s` and `t`, the distance from `q` to `centre` equals `radius`, the distance from `r` to `centre` equals `radius`, the distance from `s` to `centre` equals `radius`, and the distance from `t` to `centre` equals `radius`, then the product of the distance from `q` to `b` and the distance from `b` to `r` equals the product of the distance from `s` to `b` and the distance from `b` to `t`.

### Informal sketch
The proof proceeds as follows:
- Start by generalizing all variables.
- Rewrite using the definitions of `length`, `NORM_CROSS`, and the theorem `BETWEEN_THM`.
- Eliminate existential quantifiers introduced by `BETWEEN_THM` using assumptions and introducing `u` and `v` as witnesses.
- Substitute the values of the witnesses into the main goal.
- Apply the function `\x. x pow 2` to both sides of equations derived from the assumption that `b` lies between `q`,`r` and `s`,`t`.
- Apply the symmetry rule.
- Rewrite using `NORM_POW_2`.
- Define abbreviation `rad = radius pow 2`.
- Simplify using the definitions of `dot`, `SUM_2`, `VECTOR_SUB_COMPONENT`, `DIMINDEX_2`, `VECTOR_ADD_COMPONENT`, `CART_EQ`, `FORALL_2`, `VECTOR_MUL_COMPONENT`, and `ARITH`.
- Apply real ring conversion on both sides to complete the proof automatically.

### Mathematical insight
The theorem states a geometric property regarding intersecting chords of a circle. Given a circle centered at the point `centre` with radius `radius`, and two chords `qr` and `st` that intersect at point `b`, the product of segments  `qb` and `br` equals the product of segments `sb` and `bt`. This is a standard result in Euclidean geometry.

### Dependencies
- `length`
- `NORM_CROSS`
- `BETWEEN_THM`
- `dot`
- `SUM_2`
- `VECTOR_SUB_COMPONENT`
- `DIMINDEX_2`
- `VECTOR_ADD_COMPONENT`
- `CART_EQ`
- `FORALL_2`
- `VECTOR_MUL_COMPONENT`
- `ARITH`
- `NORM_POW_2`


---

