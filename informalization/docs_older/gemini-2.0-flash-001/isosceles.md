# isosceles.ml

## Overview

Number of statements: 9

`isosceles.ml` formalizes the isosceles triangle theorem within the Multivariate Geometry library. The file imports `geom.ml` and likely contains definitions and theorems related to properties of isosceles triangles, specifically proving that the base angles of an isosceles triangle are equal. Its purpose is to provide a formal proof of this geometric theorem within HOL Light.


## ISOSCELES_TRIANGLE_THEOREM

### Name of formal statement
ISOSCELES_TRIANGLE_THEOREM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_THEOREM = prove
 (`!A B C:real^N. dist(A,C) = dist(B,C) ==> angle(C,A,B) = angle(A,B,C)`,
  MP_TAC(INST_TYPE [`:N`,`:M`] CONGRUENT_TRIANGLES_SSS) THEN
  MESON_TAC[DIST_SYM; ANGLE_SYM]);;
```
### Informal statement
For any points `A`, `B`, and `C` in the real n-dimensional space, if the distance between `A` and `C` is equal to the distance between `B` and `C`, then the angle at `A` formed by the points `C`, `A`, and `B` is equal to the angle at `B` formed by the points `A`, `B`, and `C`.

### Informal sketch
The proof proceeds as follows:
- Apply the `CONGRUENT_TRIANGLES_SSS` theorem, instantiated to appropriate types to show that the triangle `A`, `B`, `C` is congurent to itself.
- Use automatic rewriting with `DIST_SYM` and `ANGLE_SYM`
- Apply the simplifier to complete the proof.

### Mathematical insight
This theorem formalizes the well-known geometric property that in an isosceles triangle, the angles opposite the equal sides are also equal. This is a fundamental result in Euclidean geometry.

### Dependencies
- `Multivariate/geom.ml`
- `DIST_SYM`
- `ANGLE_SYM`
- `CONGRUENT_TRIANGLES_SSS`


---

## ISOSCELES_TRIANGLE_CONVERSE

### Name of formal statement
ISOSCELES_TRIANGLE_CONVERSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_CONVERSE = prove
 (`!A B C:real^N. angle(C,A,B) = angle(A,B,C) /\ ~(collinear {A,B,C})
                  ==> dist(A,C) = dist(B,C)`,
  MP_TAC(INST_TYPE [`:N`,`:M`] CONGRUENT_TRIANGLES_ASA_FULL) THEN
  MESON_TAC[DIST_SYM; ANGLE_SYM]);;
```
### Informal statement
For all points `A`, `B`, and `C` in `real^N`, if the angle formed by `C`, `A`, and `B` is equal to the angle formed by `A`, `B`, and `C`, and `A`, `B`, and `C` are not collinear, then the distance between `A` and `C` is equal to the distance between `B` and `C`.

### Informal sketch
The proof proceeds as follows:
- Assume `angle(C,A,B) = angle(A,B,C)` and `~(collinear {A,B,C})`.
- Apply the `CONGRUENT_TRIANGLES_ASA_FULL` theorem (Angle-Side-Angle congruence) after instantiating the type variables `:N` and `:M`. This step relies on the fact that the side `AB` is equal to itself.
- Use `MESON_TAC` along with the theorems `DIST_SYM` (distance symmetry) and `ANGLE_SYM` (angle symmetry) to complete the proof, likely to manage the equational reasoning produced by `CONGRUENT_TRIANGLES_ASA_FULL` to derive `dist(A,C) = dist(B,C)`.

### Mathematical insight
This theorem provides the converse of a property of isosceles triangles. It states that if two angles of a triangle are equal, then the sides opposite those angles have equal length. This is a fundamental result in Euclidean geometry. The condition `~(collinear {A,B,C})` ensures that `A`, `B`, and `C` form a proper triangle and not a degenerate (collinear) one.

### Dependencies
- `CONGRUENT_TRIANGLES_ASA_FULL`
- `DIST_SYM`
- `ANGLE_SYM`


---

## lemma

### Name of formal statement
lemma

### Type of the formal statement
theorem

### Formal Content
```ocaml
let lemma = prove
 (`!A B C D:real^N.
        between D (A,B)
        ==> (orthogonal (A - B) (C - D) <=>
                angle(A,D,C) = pi / &2 /\ angle(B,D,C) = pi / &2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `D:real^N = A` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[ANGLE_REFL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ORTHOGONAL_LNEG] THEN
    REWRITE_TAC[VECTOR_NEG_SUB; ORTHOGONAL_VECTOR_ANGLE; angle];
    ALL_TAC] THEN
  ASM_CASES_TAC `D:real^N = B` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[ANGLE_REFL] THEN
    REWRITE_TAC[ORTHOGONAL_VECTOR_ANGLE; angle];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `D:real^N`; `C:real^N`]
      ANGLES_ALONG_LINE) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_VECTOR_ANGLE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = z ==> x + y = p ==> (z = p / &2 <=> x = p / &2 /\ y = p / &2)`) THEN
  REWRITE_TAC[angle] THEN MATCH_MP_TAC VECTOR_ANGLE_EQ_0_RIGHT THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_ANGLE_NEG2] THEN
  REWRITE_TAC[VECTOR_NEG_SUB; GSYM angle] THEN
  ASM_MESON_TAC[ANGLE_EQ_PI_OTHERS; BETWEEN_ANGLE]);;
```
### Informal statement
For all vectors `A`, `B`, `C`, and `D` in `real^N`, if `D` lies between `A` and `B`, then `A - B` is orthogonal to `C - D` if and only if the angle between `A`, `D`, and `C` is `pi / 2` and the angle between `B`, `D`, and `C` is `pi / 2`.

### Informal sketch
The proof proceeds by cases:
- Case 1: `D = A`. In this case, we simplify the statement and rewrite using the definition of orthogonality and angle.
- Case 2: `D = B`. Similar to the previous case, we simplify the statement and rewrite using the definition of orthogonality and angle.
- General case: `D` is strictly between `A` and `B`.
    - We use `ANGLES_ALONG_LINE`, which states that the angles `angle(A,D,C)` and `angle(B,D,C)` sum to `angle(A,D,B)`, which is `pi`.
    - We rewrite using `ORTHOGONAL_VECTOR_ANGLE` to relate orthogonality to the angle.
    - We use a real arithmetic lemma to deduce that `angle(A,D,C) = pi / 2` if and only if both `angle(A,D,C) = pi / 2` and `angle(B,D,C) = pi / 2`.
    - We rewrite using the definition of `angle` and simplify the vector expressions.
    - Finally, we use `ANGLE_EQ_PI_OTHERS` and `BETWEEN_ANGLE` to conclude the proof.

### Mathematical insight
This theorem relates the geometric concepts of orthogonality and angles. It states that if a point `D` lies between two points `A` and `B`, then the line segment `CD` is perpendicular to the line segment `AB` if and only if angles ADC and BDC are both right angles. This is a fundamental result in Euclidean geometry.

### Dependencies
- `BETWEEN`
- `ORTHOGONAL_LNEG`
- `VECTOR_NEG_SUB`
- `ORTHOGONAL_VECTOR_ANGLE`
- `angle`
- `ANGLE_REFL`
- `ANGLES_ALONG_LINE`
- `VECTOR_ANGLE_EQ_0_RIGHT`
- `VECTOR_ANGLE_NEG2`
- `ANGLE_EQ_PI_OTHERS`
- `BETWEEN_ANGLE`


---

## ISOSCELES_TRIANGLE_1

### Name of formal statement
ISOSCELES_TRIANGLE_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_1 = prove
 (`!A B C D:real^N.
        dist(A,C) = dist(B,C) /\ D = midpoint(A,B)
        ==> angle(A,C,D) = angle(B,C,D)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N`; `D:real^N`; `C:real^N`;
                 `B:real^N`; `D:real^N`; `C:real^N`]
        CONGRUENT_TRIANGLES_SSS_FULL) THEN
  ASM_REWRITE_TAC[DIST_MIDPOINT] THEN ASM_MESON_TAC[DIST_SYM; ANGLE_SYM]);;
```
### Informal statement
For all real vectors `A`, `B`, `C`, and `D` in N-dimensional space, if the distance between `A` and `C` is equal to the distance between `B` and `C`, and `D` is the midpoint of `A` and `B`, then the angle `A`, `C`, `D` is equal to the angle `B`, `C`, `D`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the universal quantifiers and the implication.
- Apply the `CONGRUENT_TRIANGLES_SSS_FULL` theorem to the triangles `(A,C,D)` and `(B,C,D)`. This requires showing that the three sides of the two triangles are pairwise equal in length.
- Rewrite using `DIST_MIDPOINT` to show that the distance between `A` and `D` equals the distance between `B` and `D`.
- Use `DIST_SYM` and `ANGLE_SYM` with `ASM_MESON_TAC` to discharge the remaining assumptions about side length equalities and conclude that the angles `angle(A,C,D)` and `angle(B,C,D)` are equal.

### Mathematical insight
This theorem captures the fundamental property of an isosceles triangle that the line segment from the apex to the midpoint of the base bisects the apex angle. This is a basic geometric result, crucial for reasoning about triangles and their symmetries. The use of vectors in N-dimensional space makes it a general result.

### Dependencies
- `DIST_MIDPOINT`
- `CONGRUENT_TRIANGLES_SSS_FULL`
- `DIST_SYM`
- `ANGLE_SYM`


---

## ISOSCELES_TRIANGLE_2

### Name of formal statement
ISOSCELES_TRIANGLE_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_2 = prove
 (`!A B C D:real^N.
        between D (A,B) /\
        dist(A,C) = dist(B,C) /\ angle(A,C,D) = angle(B,C,D)
        ==> orthogonal (A - B) (C - D)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ISOSCELES_TRIANGLE_THEOREM) THEN
  MP_TAC(ISPECL [`D:real^N`; `C:real^N`; `A:real^N`;
                 `D:real^N`; `C:real^N`; `B:real^N`]
        CONGRUENT_TRIANGLES_SAS_FULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM; ANGLE_SYM]; ALL_TAC] THEN
  ASM_CASES_TAC `D:real^N = B` THEN
  ASM_SIMP_TAC[DIST_EQ_0; DIST_REFL; VECTOR_SUB_REFL; ORTHOGONAL_0] THEN
  ASM_CASES_TAC `D:real^N = A` THENL [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[lemma] THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `D:real^N`; `C:real^N`]
      ANGLES_ALONG_LINE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all vectors A, B, C, and D in real N-dimensional space, if D is between A and B, the distance from A to C is equal to the distance from B to C, and the angle between A, C, and D is equal to the angle between B, C, and D, then the vector from A to B is orthogonal to the vector from C to D.

### Informal sketch
The proof proceeds as follows:
- Assume the antecedent: `between D (A,B)`, `dist(A,C) = dist(B,C)`, and `angle(A,C,D) = angle(B,C,D)`.
- Apply `ISOSCELES_TRIANGLE_THEOREM` using congruence of triangles (`CONGRUENT_TRIANGLES_SAS_FULL`) and symmetry of `DIST_SYM` and `ANGLE_SYM`.
- Perform case analysis on `D = B` and `D = A`. If either holds, the conclusion follows by simplification.
- Otherwise, apply theorem `ANGLES_ALONG_LINE` and real arithmetic. This completes the proof.

### Mathematical insight
The theorem states that if we have a point D on the line segment AB, and C is a point such that AC = BC and the angles ACD and BCD are equal, then CD is orthogonal to AB. This is a geometric property relating the equality of distances and angles in an isosceles triangle to orthogonality.

### Dependencies
- Theorems: `ISOSCELES_TRIANGLE_THEOREM`, `CONGRUENT_TRIANGLES_SAS_FULL`, `ANGLES_ALONG_LINE`
- Definitions: `between`, `dist`, `angle`, `orthogonal`
- Lemmas: `DIST_SYM`, `ANGLE_SYM`, `DIST_EQ_0`, `DIST_REFL`, `VECTOR_SUB_REFL`, `ORTHOGONAL_0`


---

## ISOSCELES_TRIANGLE_3

### Name of formal statement
ISOSCELES_TRIANGLE_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_3 = prove
 (`!A B C D:real^N.
        between D (A,B) /\
        dist(A,C) = dist(B,C) /\ orthogonal (A - B) (C - D)
        ==> D = midpoint(A,B)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^N = B` THEN
  ASM_SIMP_TAC[BETWEEN_REFL_EQ; MIDPOINT_REFL] THEN
  ASM_CASES_TAC `D:real^N = A` THENL
   [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] PYTHAGORAS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_LNEG; VECTOR_NEG_SUB]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist] THEN
    ASM_REWRITE_TAC[REAL_RING `a = x pow 2 + a <=> x = &0`; DIST_EQ_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `D:real^N = B` THENL
   [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] PYTHAGORAS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_LNEG; VECTOR_NEG_SUB]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist] THEN
    ASM_REWRITE_TAC[REAL_RING `a = x pow 2 + a <=> x = &0`; DIST_EQ_0];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[lemma; MIDPOINT_COLLINEAR; BETWEEN_IMP_COLLINEAR] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ISOSCELES_TRIANGLE_THEOREM) THEN
  MP_TAC(ISPECL
   [`A:real^N`; `C:real^N`; `D:real^N`;
    `B:real^N`; `C:real^N`; `D:real^N`]
        CONGRUENT_TRIANGLES_SAS) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^N`; `C:real^N`; `D:real^N`] TRIANGLE_ANGLE_SUM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `D:real^N`] TRIANGLE_ANGLE_SUM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a:real = a' /\ b = b'
    ==> a + x + b = p ==> a' + x' + b' = p ==> x' = x`) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ANGLE_SYM]] THEN
  CONV_TAC SYM_CONV THEN
  UNDISCH_TAC `angle(C:real^N,A,B) = angle (A,B,C)` THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [MATCH_MP_TAC ANGLE_EQ_0_LEFT;
    GEN_REWRITE_TAC RAND_CONV [ANGLE_SYM] THEN
    MATCH_MP_TAC ANGLE_EQ_0_RIGHT] THEN
  ASM_MESON_TAC[ANGLE_EQ_PI_OTHERS; BETWEEN_ANGLE]);;
```

### Informal statement
For all vectors A, B, C, and D in N-dimensional real space, if D lies between A and B, the distance between A and C equals the distance between B and C, and the vector from A to B is orthogonal to the vector from C to D, then D is the midpoint of A and B.

### Informal sketch
The proof proceeds by case analysis and equational reasoning.

- First, consider the cases where `A = B`, `D = A`, and `D = B`. In each case, simplification and rewriting with relevant lemmas (`BETWEEN_REFL_EQ`, `MIDPOINT_REFL`) and assumptions proves the result. Notably, in the cases where `D = A` and `D = B`, the Pythagorean theorem (`PYTHAGORAS`) is used to deduce that the distance between `A` and `B` is zero since `dist(A,C) = dist(B,C)` and `orthogonal (A - B) (C - D)`.
- In the remaining case where `A != B`, `D != A`, and `D != B`, we know `A`, `B`, and `D` are distinct and collinear due to `between D (A,B)`. Additionally, since `dist(A,C) = dist(B,C)`, `C` lies on the perpendicular bisector of segment `AB`. Because the line segment `CD` is orthogonal to `AB`, we can construct congruent triangles `ACD` and `BCD` and derive the angles `angle(C,A,B) = angle(A,B,C)`.
- Finally we show that `angle(C,A,B) = angle(A,B,C)` implies that `angle(C,A,B)` is zero, which allows us to conclude that `D = midpoint(A,B)`.

### Mathematical insight
This theorem states that in an isosceles triangle ABC, if a point D lies on the base AB and the line CD is orthogonal to AB, then D must be the midpoint of AB. This is a geometric property that relates orthogonality, betweenness, distance, and midpoints in Euclidean space.

### Dependencies

- Theorems: `PYTHAGORAS`, `ISOSCELES_TRIANGLE_THEOREM`, `CONGRUENT_TRIANGLES_SAS`, `TRIANGLE_ANGLE_SUM`
- Definitions: `between`, `dist`, `orthogonal`, `midpoint`, `angle`
- Lemmas: `BETWEEN_REFL_EQ`, `MIDPOINT_REFL`, `ORTHOGONAL_LNEG`, `VECTOR_NEG_SUB`, `NORM_SUB`, `DIST_EQ_0`, `MIDPOINT_COLLINEAR`, `BETWEEN_IMP_COLLINEAR`, `DIST_SYM`, `ANGLE_SYM`, `ANGLE_EQ_0_LEFT`, `ANGLE_EQ_0_RIGHT`, `ANGLE_EQ_PI_OTHERS`, `BETWEEN_ANGLE`
- Real arithmetic rules: `REAL_RING `a = x pow 2 + a <=> x = &0``, `REAL_ARITH `a:real = a' /\ b = b' ==> a + x + b = p ==> a' + x' + b' = p ==> x' = x``


---

## ISOSCELES_TRIANGLE_4

### Name of formal statement
ISOSCELES_TRIANGLE_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_4 = prove
 (`!A B C D:real^N.
        D = midpoint(A,B) /\ orthogonal (A - B) (C - D)
        ==> dist(A,C) = dist(B,C)`,
  REPEAT GEN_TAC THEN ASM_SIMP_TAC[IMP_CONJ; BETWEEN_MIDPOINT; lemma] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC CONGRUENT_TRIANGLES_SAS THEN
  MAP_EVERY EXISTS_TAC [`D:real^N`; `D:real^N`] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[DIST_MIDPOINT]);;
```

### Informal statement
For all points A, B, and C in N-dimensional real space, if D is the midpoint of the segment AB, and the vector (A - B) is orthogonal to the vector (C - D), then the distance from A to C is equal to the distance from B to C.

### Informal sketch
The proof demonstrates that if `D` is the midpoint of `A` and `B`, and the line segment `CD` is orthogonal to `AB`, then the triangle `ABC` is isosceles with `AC = BC`.
- Start by assuming `D` is the midpoint of `A` and `B`, and `(A - B)` is orthogonal to `(C - D)`.
- Rewrite the midpoint property using `BETWEEN_MIDPOINT`.
- Rewrite the assumption that `D` is the midpoint of `A` and `B` to isolate the condition.
- Apply the `CONGRUENT_TRIANGLES_SAS` theorem (Side-Angle-Side congruence) to triangles `ADC` and `BDC`. The sides `AD` and `BD` are equal because `D` is the midpoint of `AB`. The angle between `AD` and `DC` is a right angle, as is the angle between `BD` and `DC`, because `CD` is orthogonal to `AB`. The side `DC` is equal to itself, so the conditions for SAS congruence are met.
- Introduce existential variables `D` for both triangles
- Expand the definition of `D` and use `DIST_MIDPOINT` to simplify the distance calculations, demonstrating that `dist(A, C) = dist(B, C)`.

### Mathematical insight
This theorem states that if a line segment from a point to the midpoint of the opposite side is perpendicular to that side, then this is an isosceles triangle. In Euclidean geometry, this captures a fundamental property of isosceles triangles, linking the midpoint of the base, perpendicularity, and equal side lengths.

### Dependencies
- `IMP_CONJ`
- `BETWEEN_MIDPOINT`
- `CONGRUENT_TRIANGLES_SAS`
- `DIST_MIDPOINT`
- `orthogonal`
- `midpoint`
- `dist`
- `lemma` : a generic lemma for simplification

### Porting notes (optional)
- The tactic `ASM_SIMP_TAC` may need adjustment depending on how automation handles assumptions and rewriting in the target proof assistant.
- The key step involves applying the Side-Angle-Side (`CONGRUENT_TRIANGLES_SAS`) congruence theorem, which should be available or provable in any geometry library.
- `EXPAND_TAC` is a HOL Light specific tactic, which will need to be replaced with the appropriate unfolding tactics from other systems.


---

## ISOSCELES_TRIANGLE_5

### Name of formal statement
ISOSCELES_TRIANGLE_5

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_5 = prove
 (`!A B C D:real^N.
        ~collinear{D,C,A} /\ between D (A,B) /\
        angle(A,C,D) = angle(B,C,D) /\ orthogonal (A - B) (C - D)
        ==> dist(A,C) = dist(B,C)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `C:real^N = D` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  UNDISCH_TAC `~(C:real^N = D)` THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT; GSYM CONJ_ASSOC] THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `C:real^N = A` THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[ANGLE_REFL] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BETWEEN_ANGLE]) THEN
    ASM_CASES_TAC `D:real^N = A` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `D:real^N = B` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ANGLE_REFL_MID; REAL_ARITH `x / &2 = &0 <=> x = &0`;
                 PI_NZ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ANGLE_EQ_PI_OTHERS) THEN
    MP_TAC PI_NZ THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `C:real^N = B` THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[ANGLE_REFL] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BETWEEN_ANGLE]) THEN
    ASM_CASES_TAC `D:real^N = B` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `D:real^N = A` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ANGLE_REFL_MID; REAL_ARITH `&0 = x / &2 <=> x = &0`;
                 PI_NZ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ANGLE_EQ_PI_OTHERS) THEN
    MP_TAC PI_NZ THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[IMP_CONJ; lemma] THEN
  REPEAT DISCH_TAC THEN MP_TAC(
    ISPECL [`D:real^N`; `C:real^N`; `A:real^N`;
            `D:real^N`; `C:real^N`; `B:real^N`]
     CONGRUENT_TRIANGLES_ASA_FULL) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
  ONCE_REWRITE_TAC[ANGLE_SYM] THEN ASM_REWRITE_TAC[]);;
```
### Informal statement
For any points `A`, `B`, `C`, and `D` in `real^N` space, if `D`, `C`, and `A` are not collinear, `D` is between `A` and `B`, the angle `A`, `C`, `D` is equal to the angle `B`, `C`, `D`, and the vector from `A` to `B` is orthogonal to the vector from `C` to `D`, then the distance from `A` to `C` is equal to the distance from `B` to `C`.

### Informal sketch
The theorem states that given points A, B, C, and D in N-dimensional real space, if D lies between A and B, A, C, and D are not collinear, the angles ACD and BCD are equal, and the line segments AB and CD are orthogonal, then triangle ABC is isosceles with AC = BC.

The proof proceeds by:
- Case splitting on whether `C = D`. If `C = D`, then using `COLLINEAR_2`, it's shown the points `D`, `C`, `A` are collinear which contradicts the assumptions.
- Assuming `C` is not equal to `D` and splitting on whether `A = B`.
    - If `A = B`, then the result follows easily.
    - Assuming `A` is not equal to `B`, split on whether `C = A`:
        - If `C = A`, then angle `angle(A, C, D)` is `angle(A, A, D)` which is 0. Applying `BETWEEN_ANGLE` and cases splitting `D = A` and `D = B` we arrive at a contradiction. A similar contradiction arises if `C = B`.
- Applying the `CONGRUENT_TRIANGLES_ASA_FULL` theorem after discharging assumptions. This theorem says that two triangles are congruent if two angles and the included side are respectively equal. The assumptions are manipulated to match the hypotheses of `CONGRUENT_TRIANGLES_ASA_FULL`. Necessary rewriting and simplification are done using `ANGLE_SYM` and `DIST_SYM`

### Mathematical insight
This theorem provides a geometric condition for determining when a triangle is isosceles based on an angle bisector and orthogonality condition. The angle bisector (CD) and the perpendicularity condition establish a symmetry that forces the two sides (AC and BC) to be equal. The theorem is a useful tool in geometric reasoning and can be applied to prove other geometric properties.

### Dependencies
- `COLLINEAR_2`
- `ANGLE_REFL`
- `BETWEEN_ANGLE`
- `ANGLE_REFL_MID`
- `PI_NZ`
- `CONGRUENT_TRIANGLES_ASA_FULL`
- `DIST_SYM`
- `ANGLE_SYM`

Theorems:
- `IMP_CONJ_ALT`
- `ANGLE_EQ_PI_OTHERS`
- `GSYM`
- `CONJ_ASSOC`
- `IMP_CONJ`
- `lemma`

### Porting notes (optional)
The proof relies heavily on rewriting and simplification using theorems about angles, distances, and collinearity. Ensure that the target proof assistant has similar theorems and simplification capabilities. The tactic `ASM_CASES_TAC` is used extensively representing case splits which might be implemented in different style. The application of `CONGRUENT_TRIANGLES_ASA_FULL` is crucial and should be handled carefully. Ensure that the theorem is available with the exact definition and hypotheses.


---

## ISOSCELES_TRIANGLE_6

### Name of formal statement
ISOSCELES_TRIANGLE_6

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_6 = prove
 (`!A B C D:real^N.
        ~collinear{D,C,A} /\ D = midpoint(A,B) /\ angle(A,C,D) = angle(B,C,D)
        ==> dist(A,C) = dist(B,C)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^N`; `C:real^N`; `D:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `D:real^N`] LAW_OF_SINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[DIST_MIDPOINT] THEN
  ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ; REAL_HALF; DIST_POS_LT;
               SIN_ANGLE_EQ] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`D:real^N`; `C:real^N`; `A:real^N`;
                   `D:real^N`; `C:real^N`; `B:real^N`]
       CONGRUENT_TRIANGLES_AAS) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ANGLE_SYM] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`]
                TRIANGLE_ANGLE_SUM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `angle(A:real^N,B,C) = angle(C,B,D) /\
                  angle(B,A,C) = angle(C,A,D)`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [ANGLE_SYM] THEN
      MATCH_MP_TAC ANGLE_EQ_0_LEFT THEN
      MP_TAC(ISPECL [`A:real^N`; `B:real^N`] BETWEEN_MIDPOINT) THEN
      ASM_REWRITE_TAC[BETWEEN_ANGLE] THEN EXPAND_TAC "D" THEN
      REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[ANGLE_EQ_PI_OTHERS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `a + pi - a + x = pi <=> x = &0`] THEN
    MAP_EVERY ASM_CASES_TAC
     [`B:real^N = C`; `A:real^N = C`] THEN
    ASM_REWRITE_TAC[ANGLE_REFL; REAL_ARITH `p / &2 = &0 <=> p = &0`] THEN
    ASM_REWRITE_TAC[PI_NZ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `A:real^N`] COLLINEAR_ANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~collinear{D:real^N,C,A}` THEN
    MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> q ==> r`) THEN
    ONCE_REWRITE_TAC[SET_RULE `{bd,c,a} = {c,a,bd}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    REWRITE_TAC[COLLINEAR_LEMMA] THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[midpoint] THEN
    REWRITE_TAC[VECTOR_ARITH `inv(&2) % (A + B) - A = inv(&2) % (B - A)`] THEN
    MESON_TAC[VECTOR_MUL_ASSOC]]);;
```

### Informal statement
For any vectors `A`, `B`, `C`, and `D` in `real^N`, if `D`, `C`, and `A` are not collinear, `D` is the midpoint of `A` and `B`, and the angle between `A`, `C`, and `D` is equal to the angle between `B`, `C`, and `D`, then the distance between `A` and `C` is equal to the distance between `B` and `C`.

### Informal sketch
The proof establishes that if point `D` is the midpoint of segment `AB` and the angles `∠ACD` and `∠BCD` are equal, then the triangle `ABC` is isosceles with `AC = BC`, provided that `A`, `C`, and `D` are not collinear.
- First, consider the case where `A` and `B` are equal. In this case `dist(A, C) = dist(B, C)` follows directly.
- Then use the Law of Sines on triangles `ACD` and `BCD`.
- Simplify using the fact that `dist(A, D) = dist(B, D)` since `D` is a midpoint of `A` and `B`.
- Consider the two subgoals that can result from simplifying the equation `sin(angle(A, C, D)) / dist(A, D) = sin(angle(B, C, D)) / dist(B, D)` to `dist(A,C) = dist(B,C)`.
- In the first case, congruent triangles AAS (`CONGRUENT_TRIANGLES_AAS`) are used to directly prove the equality.
- In the second case, derive `angle(A,B,C) = angle(C,B,D) /\ angle(B,A,C) = angle(C,A,D)` as a sugoal and simplify using `ANGLE_SYM`, `BETWEEN_MIDPOINT`.
- Use `COLLINEAR_ANGLE` to show the subgoals are contradictory to the initial assumption `~collinear{D,C,A}`.

### Mathematical insight
The theorem states a geometric property related to isosceles triangles. If a line segment from a vertex `C` bisects the angle at that vertex (`∠ACD = ∠BCD`) and intersects the opposite side (`AB`) at its midpoint (`D`), then the triangle `ABC` is isosceles. The condition of `D`, `C`, and `A` not being collinear avoids the degenerate case where the points lie on a line.

### Dependencies
- `LAW_OF_SINES`
- `DIST_MIDPOINT`
- `REAL_EQ_MUL_RCANCEL`
- `REAL_LT_IMP_NZ`
- `REAL_HALF`
- `DIST_POS_LT`
- `SIN_ANGLE_EQ`
- `CONGRUENT_TRIANGLES_AAS`
- `DIST_SYM`
- `ANGLE_SYM`
- `TRIANGLE_ANGLE_SUM`
- `ANGLE_EQ_0_LEFT`
- `BETWEEN_MIDPOINT`
- `BETWEEN_ANGLE`
- `MIDPOINT_EQ_ENDPOINT`
- `ANGLE_EQ_PI_OTHERS`
- `ANGLE_REFL`
- `PI_NZ`
- `COLLINEAR_ANGLE`
- `COLLINEAR_3`
- `COLLINEAR_LEMMA`
- `VECTOR_SUB_EQ`

### Porting notes (optional)
- The proof relies on properties of real numbers and vector arithmetic in N-dimensional space, so these must be available in the target proof assistant.
- The `MESON_TAC` calls suggest that some amount of automated reasoning is used, so an equivalent automated tactic or solver may be necessary to reconstruct the proof efficiently.
- Law of Sines may need to be proved separately if it doesn't exist already.


---

