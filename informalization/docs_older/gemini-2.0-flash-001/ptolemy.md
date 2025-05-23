# ptolemy.ml

## Overview

Number of statements: 3

`ptolemy.ml` formalizes Ptolemy's theorem. It resides within the geometry section, leveraging transcendental functions from `Multivariate/transcendentals.ml`. The file likely contains a formal statement of Ptolemy's theorem and its formal proof within HOL Light.


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
The dot product of the 2-dimensional real vectors `(vector [x1; y1])` and `(vector [x2; y2])` is equal to `x1 * x2 + y1 * y2`.

### Informal sketch
The proof uses the following steps:
- Rewrite the dot product using the definition of `dot`.
- Apply `DIMINDEX_2` to expand the dot product in 2 dimensions.
- Apply `SUM_2` to evaluate the sum.
- Apply `VECTOR_2` to expand vectors into their components.

### Mathematical insight
This theorem provides a concrete formula for the dot product of two-dimensional real vectors represented using the `vector` constructor. It expands the abstract definition of the dot product to a usable arithmetic expression. This is a fundamental identity for working with 2D vector geometry.

### Dependencies
- Definitions: `dot`, `vector`
- Theorems: `DIMINDEX_2`, `SUM_2`, `VECTOR_2`


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
For all real numbers `a1`, `a2`, and `radius`, if `0` is less than or equal to `a1`, `a1` is less than or equal to `a2`, `a2` is less than or equal to `2 * pi`, and `0` is less than or equal to `radius`, then the distance between the point `centre + radius * vector [cos(a1); sin(a1)]` and the point `centre + radius * vector [cos(a2); sin(a2)]` in the real plane is equal to `2 * radius * sin((a2 - a1) / 2)`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and assumptions.
- Rewrite using the definitions of `dist` and `vector_norm`.
- Apply `SQRT_UNIQUE` to remove the square root, which results in proving that the argument to the square root is nonnegative, and that the square of the claimed distance is equal to the squared Euclidean distance.
- The nonnegativity is established:
    - show `radius >= 0 /\ radius <= 2*pi ==> sin((a2-a1)/2)>=0` by exploiting `REAL_LE_MUL`, `REAL_POS` and `SIN_POS_PI_LE` theorems.
- Expand `(c + r % x) - (c + r % y)` to `r % (x - y)`.
- Expand `(r % x) dot (r % x)` to `(r pow 2) * (x dot x)`.
- Expand the dot product of vectors.
- Rewrite `a1` as `2 * a1 / 2` and `a2` as `2 * a2 / 2`.
- Simplify `(2 * x - 2 * y) / 2` to `x - y`.
- Apply trigonometric identities for `sin(x - y)`, `sin(2x)`, and `cos(2x)`.
- Use `SIN_CIRCLE` to replace `cos(x)^2 + sin(x)^2` by `1`.
- Use `REAL_RING` to simplify the expression.

### Mathematical insight
This theorem provides a formula for calculating the Euclidean distance between two points on a circle in the real plane, given their angular coordinates `a1` and `a2` and the radius `radius` of the circle. The formula `2 * radius * sin((a2 - a1) / 2)` expresses this distance in terms of the radius and the sine of half the angular difference. It assumes that `a1` and `a2` are between `0` and `2*pi` and that `a1 <= a2` to ensure the formula is valid.

### Dependencies
- Definitions: `dist`, `vector_norm`
- Theorems: `SQRT_UNIQUE`, `REAL_LE_MUL`, `REAL_POS`, `SIN_POS_PI_LE`, `SIN_SUB`, `SIN_DOUBLE`, `COS_DOUBLE`, `SIN_CIRCLE`, `DOT_LSUB`, `DOT_RSUB`, `DOT_VECTOR`
- Vector arithmetic: `VECTOR_ARITH` ((`c + r % x) - (c + r % y) = r % (x - y)`), `VECTOR_ARITH`(`(r % x) dot (r % x) = (r pow 2) * (x dot x)`)
- Tactics: `REAL_ARITH`, `ASM_REAL_ARITH_TAC`, `REAL_RING`

### Porting notes (optional)
- The proof relies on standard trigonometric identities, which should be available in most proof assistants.
- The `VECTOR_ARITH` rewrites might need to be expressed using explicit vector operations depending on the target system.
- The `SQRT_UNIQUE` tactic encapsulates two subgoals, one for the non-negativity of the argument of square root and another for the equality relation. In other proof assistants, these subgoals might need to be handled explicitly.


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
For all points `A`, `B`, `C`, and `D` in the real plane (represented as `real^2`), and for all real numbers `a`, `b`, `c`, `d`, `centre`, and `radius`, if:
  - `A` is equal to `centre` plus `radius` times the vector `[cos(a); sin(a)]`, and
  - `B` is equal to `centre` plus `radius` times the vector `[cos(b); sin(b)]`, and
  - `C` is equal to `centre` plus `radius` times the vector `[cos(c); sin(c)]`, and
  - `D` is equal to `centre` plus `radius` times the vector `[cos(d); sin(d)]`, and
  - `0 <= radius`, and
  - `0 <= a <= b <= c <= d <= 2 * pi`,
then:
  - `dist(A, C) * dist(B, D) = dist(A, B) * dist(C, D) + dist(A, D) * dist(B, C)`.

### Informal sketch
The proof demonstrates Ptolemy's theorem for points on a circle.

- The proof starts by stripping the assumptions and repeatedly substituting assumptions where possible.
- The distances between points `A`, `B`, `C`, and `D` are rewritten using the `DIST_SEGMENT_LEMMA` applied to appropriate terms with the help of `PART_MATCH`. Antedecents for the use of `DIST_SEGMENT_LEMMA` are then discharged using real arithmetic.
- Simplification involving distributing division over subtraction `(x - y) / &2 = x / &2 - y / &2` is performed.
- Trigonometric identities for points on unit circle, specifically `SIN_CIRCLE`, are applied to `a/2`, `b/2`, `c/2`, and `d/2`.
- Trigonometric identities like `SIN_SUB`, `SIN_ADD`, `COS_ADD`, `SIN_PI`, `COS_PI` are applied to simplify the expressions.
- Finally, the proof concludes with a ring tactic (`REAL_RING`) to prove the algebraic equality.

### Mathematical insight
This theorem states Ptolemy's theorem, which relates the distances between four points on a circle. Specifically, it asserts that for any four points A, B, C, and D on a circle, the product of the diagonals (AC and BD) is equal to the sum of the products of the opposite sides (AB * CD and AD * BC). This is a fundamental result in Euclidean geometry.  The theorem here is specialised for points that lie on a circle centred at `centre` and with radius `radius`.

### Dependencies
- `DIST_SEGMENT_LEMMA`
- `SIN_CIRCLE`
- `SIN_SUB`
- `SIN_ADD`
- `COS_ADD`
- `SIN_PI`
- `COS_PI`

### Porting notes (optional)
- Ensure that the target proof assistant has the required trigonometric identities (`SIN_SUB`, `SIN_ADD`, `COS_ADD`, `SIN_PI`, `COS_PI`) or be prepared to prove them.  The `REAL_RING` tactic may have analogs in tools like `ring` in Coq, `ring` in Isabelle, or linear arithmetic tactics in Lean.


---

