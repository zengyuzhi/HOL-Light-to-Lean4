# thales.ml

## Overview

Number of statements: 6

`thales.ml` formalizes Thales's theorem within HOL Light. It imports results about convexity and sums of squares. The file likely contains definitions and theorems related to geometric properties and relationships described by Thales's theorem.


## BETWEEN_THM

### Name of formal statement
BETWEEN_THM

### Type of the formal statement
theorem

### Formal Content
```hol
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
For any real numbers `x`, `a`, and `b`, `x` lies between `a` and `b` if and only if there exists a real number `u` such that `0 <= u <= 1` and `x = u * a + (1 - u) * b`.

### Mathematical insight
This theorem provides an alternative characterization of the `between` relation using convex combinations. The statement says that `x` lies between `a` and `b` if and only if `x` can be expressed as a convex combination of `a` and `b`. This representation is frequently used in geometric and analytic arguments, as it smoothly interpolates between the values `a` and `b` as `u` varies from 0 to 1.

### Informal sketch
The proof proceeds as follows:
- Rewrite using the definition of `between` in terms of the convex hull: `BETWEEN_IN_CONVEX_HULL`.
- Rewrite to commute the elements in the set `{a, b}` using `SET_RULE `{a,b} = {b,a}``.
- Rewrite the convex hull of two elements and the membership relation using `CONVEX_HULL_2_ALT` and `IN_ELIM_THM`. This transforms the membership in the convex hull into an existential quantification over a point in the interval [0,1] that produces a convex combination.
- Apply automatic term proof `AP_TERM_TAC` and `ABS_TAC`.
- Rewrite using associativity of conjunction `CONJ_ASSOC`.
- Apply automatic term proof again `AP_TERM_TAC`.
- Complete the proof using vector arithmetic tactic `VECTOR_ARITH_TAC`.

### Dependencies
- `BETWEEN_IN_CONVEX_HULL`
- `SET_RULE `{a,b} = {b,a}` // This is a set theory rule, not necessarily specific to HOL Light`
- `CONVEX_HULL_2_ALT`
- `IN_ELIM_THM`
- `CONJ_ASSOC`
- `VECTOR_ARITH_TAC`


---

## length_def

### Name of formal statement
length_def

### Type of the formal statement
new_definition

### Formal Content
```hol
let length_def = new_definition
 `length(A:real^2,B:real^2) = norm(B - A)`;;
```

### Informal statement
The length of the line segment between two points *A* and *B* in the real plane (real^2) is defined to be the Euclidean norm of the vector *B* - *A*.

### Mathematical insight
This definition formalizes the intuitive notion of the length of a line segment as the Euclidean distance between its endpoints. The Euclidean distance is calculated as the norm (magnitude) of the vector connecting the two points.

### Informal sketch
The definition `length_def` directly defines the length function. There is no proof associated to a definition in HOL Light. The length between two points `A` and `B` (both of type `real^2`) is defined to be equal to the norm of the vector resulting from subtracting `A` from `B`. The norm is the Euclidean norm.

### Dependencies
- **Definitions**: `norm`


---

## is_midpoint

### Name of formal statement
is_midpoint

### Type of the formal statement
new_definition

### Formal Content
```hol
let is_midpoint = new_definition
 `is_midpoint (m:real^2) (a,b) <=> m = (&1 / &2) % (a + b)`;;
```

### Informal statement
The predicate `is_midpoint m (a, b)` holds if and only if `m` is equal to one-half times the sum of `a` and `b`, where `m`, `a`, and `b` are vectors in the 2-dimensional real space `real^2`. The expression `(&1 / &2)` represents the real number one-half, and `%` represents scalar multiplication of a vector.

### Mathematical insight
This definition introduces the concept of a midpoint between two points `a` and `b` in a two-dimensional real space. The midpoint `m` is defined as the point that is exactly halfway between `a` and `b`, which corresponds to the average of their coordinates. This is a fundamental concept in geometry and linear algebra.

### Informal sketch
The definition `is_midpoint m (a, b) <=> m = (&1 / &2) % (a + b)` directly defines when a point `m` is the midpoint of two points `a` and `b`. No further proof or construction is needed as it is a direct definition. The verification of properties relating to the midpoint, such as `is_midpoint m (a, a)` is equivalent to `m = a`, would involve simplification and rewriting using this definition.

### Dependencies
None

### Porting notes (optional)
When porting to proof assistants like Coq or Lean, ensure that the vector space operations (addition and scalar multiplication) are defined and that the real number one-half is represented appropriately. The definition should translate directly, assuming the target system has similar notation for vector operations. Be mindful of how real numbers and vector spaces are represented in the different formal systems.


---

## THALES

### Name of formal statement
THALES

### Type of the formal statement
theorem

### Formal Content
```hol
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
For all points `centre`, `a`, `b`, and `c`, and for all real numbers `radius`, if the distance from `a` to `centre` is `radius`, and the distance from `b` to `centre` is `radius`, and the distance from `c` to `centre` is `radius`, and `centre` is the midpoint of `a` and `b`, then the vector from `a` to `c` is orthogonal to the vector from `b` to `c`.

### Mathematical insight
Thales' theorem states that if `A`, `B`, and `C` are distinct points on a circle where the line `AB` is a diameter of the circle, then the angle `ACB` is a right angle. In other words, any angle inscribed in a semicircle is a right angle.
This formalization represents this theorem in terms of distances, midpoints and orthogonality.

### Informal sketch
The proof proceeds as follows:
- Assume the hypotheses:
    - `length(a,centre) = radius`
    - `length(b,centre) = radius`
    - `length(c,centre) = radius`
    - `is_midpoint centre (a,b)`
- Rewrite definitions of `length`, `BETWEEN_THM`, and `is_midpoint`.
- Strip the implication to obtain the assumptions.
- Apply the fact that if `x = y` then `x^2 = y^2` to the first three assumptions.
- Rewrite using `NORM_POW_2` which should rewrite `(LENGTH (x,y)) pow 2` to `norm (y - x) pow 2`.
- Symmetrize the first assumption.
- Introduce the abbreviation `rad = radius pow 2`.
- Simplify using various vector and real arithmetic rules to show `(c - a) dot (c - b) = 0`.
- Apply a ring conversion (`REAL_RING`) to complete the proof.

### Dependencies
- Definitions:
    - `length_def`
    - `is_midpoint`
- Theorems:
    - `BETWEEN_THM`
- Other constants:
    - `orthogonal`
    - `dot`

### Porting notes (optional)
- The proof relies heavily on rewriting definitions and algebraic simplification.
- The automation using `REAL_RING` is crucial for discharging the final arithmetic goal. Other proof assistants may require more explicit tactics for ring normalization.
- The `is_midpoint` and `BETWEEN_THM` definitions and theorems may vary depending on the geometric library used in the target proof assistant.


---

## MIDPOINT

### Name of formal statement
MIDPOINT

### Type of the formal statement
theorem

### Formal Content
```hol
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
For all points `m`, `a`, and `b` in a 2-dimensional Euclidean space, if `m` lies between `a` and `b`, and the length of the line segment from `a` to `m` is equal to the length of the line segment from `b` to `m`, then `m` is the midpoint of the line segment `(a,b)`.

### Mathematical insight
This theorem states a fundamental property of midpoints in Euclidean space. If a point lies between two other points and is equidistant from them, then that point is the midpoint. It connects the geometric notions of "betweenness", "length", and "midpoint" formally and allows us to reason about them rigorously. The result makes sense because to be `between` two points means that `m = a + k * (b - a)` where `0 <= k <= 1`, so when the lengths are equal, `k` will be equal to `1/2`.

### Informal sketch
The proof proceeds as follows:
- Assume `m` lies between `a` and `b` and the distance from `a` to `m` equals the distance from `b` to `m`.
- Rewrite using definitions of `length`, `BETWEEN_THM`, and `is_midpoint` and the `NORM_EQ` theorem.
- Simplify using vector arithmetic lemmas related to `dot` products, `SUM_2`, `VECTOR_SUB_COMPONENT`, `DIMINDEX_2`, `VECTOR_ADD_COMPONENT`, `orthogonal`, `CART_EQ`, `FORALL_2`, `VECTOR_MUL_COMPONENT` and `ARITH`.
- Separate the conjuncted assumptions using `CONJUNCTS_THEN2` and assume them into the goal using `STRIP_ASSUME_TAC` and `MP_TAC`.
- Substitute assumptions into the goal using `FIRST_X_ASSUM SUBST_ALL_TAC` repeatedly.
- Drop assumptions using `POP_ASSUM MP_TAC` repeatedly.
- Apply a sum-of-squares conversion `REAL_SOS` to complete the proof.

### Dependencies
- requires `"Examples/sos.ml"`
#### Definitions:
- `length_def`
- `is_midpoint`

#### Theorems:
- `BETWEEN_THM`
- `NORM_EQ`

#### Simplification Rules:
- `dot`
- `SUM_2`
- `VECTOR_SUB_COMPONENT`
- `DIMINDEX_2`
- `VECTOR_ADD_COMPONENT`
- `orthogonal`
- `CART_EQ`
- `FORALL_2`
- `VECTOR_MUL_COMPONENT`
- `ARITH`


---

## THALES

### Name of formal statement
THALES

### Type of the formal statement
theorem

### Formal Content
```hol
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
For all points `centre`, `a`, `b`, and `c` in the real plane, and for all real numbers `radius`, if the distance from `a` to `centre` is equal to `radius`, and the distance from `b` to `centre` is equal to `radius`, and the distance from `c` to `centre` is equal to `radius`, and `centre` lies between `a` and `b`, then the vectors `c - a` and `c - b` are orthogonal.

### Mathematical insight
This theorem states that if `a`, `b`, and `c` are points on a circle, and `centre` is the center of the circle, and `centre` lies on the line segment connecting `a` and `b`, then the angle `acb` is a right angle. In other words, an angle inscribed in a semicircle is a right angle. This is Thales' theorem.

### Informal sketch
The proof proceeds as follows:
- Start with the assumptions that `length(a,centre) = radius`, `length(b,centre) = radius`, `length(c,centre) = radius`, and `between centre (a,b)`. The goal is to prove `orthogonal (c - a) (c - b)`.
- Introduce the subgoal `is_midpoint centre (a,b)` (i.e., `centre` is the midpoint of `a` and `b`). Use `MIDPOINT` to prove `is_midpoint centre (a,b)` because `centre` lies between `a` and `b`, and `length(a,centre) = radius` and `length(b,centre) = radius` and hence `length(a,centre) = length(b,centre)`. This implies that `centre` is equidistant from `a` and `b` along the line segment `ab`.
- Discharge the assumption `between centre (a,b)`.
- Square the equations `length(a,centre) = radius`, `length(b,centre) = radius`, and `length(c,centre) = radius`.
- Rewrite all the equations using the definitions of `length_def`, `is_midpoint`, and `orthogonal`, along with `NORM_POW_2`.
- Substitute `rad` for `radius pow 2`.
- Simplify using properties of dot products, vector components, the definitions of `orthogonal` and `CART_EQ`, and arithmetic.
- Use `REAL_RING` to finish off the proof.

### Dependencies
- `length_def`
- `is_midpoint`
- `orthogonal`
- `NORM_POW_2`
- `dot`
- `SUM_2`
- `VECTOR_SUB_COMPONENT`
- `DIMINDEX_2`
- `VECTOR_ADD_COMPONENT`
- `CART_EQ`
- `FORALL_2`
- `VECTOR_MUL_COMPONENT`
- `ARITH`
- `MIDPOINT`


---

