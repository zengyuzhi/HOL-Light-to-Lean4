# isosceles.ml

## Overview

Number of statements: 9

The `isosceles.ml` file formalizes the Isosceles triangle theorem, providing a mathematical foundation for this geometric concept. It imports necessary definitions and theorems from `Multivariate/geom.ml`, indicating its reliance on multivariate geometric principles. The file's primary purpose is to define and prove properties related to isosceles triangles, contributing to the development of geometric theories within the HOL Light library. Its content is focused on establishing a formal proof of the Isosceles triangle theorem.

## ISOSCELES_TRIANGLE_THEOREM

### Name of formal statement
ISOSCELES_TRIANGLE_THEOREM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_THEOREM = prove
 (`!A B C:real^N. dist(A,C) = dist(B,C) ==> angle(C,A,B) = angle(A,B,C)`,
  MP_TAC(INST_TYPE [`:N`,`:M`] CONGRUENT_TRIANGLES_SSS) THEN
  MESON_TAC[DIST_SYM; ANGLE_SYM])
```

### Informal statement
For all points A, B, and C in a real N-dimensional space, if the distance from A to C is equal to the distance from B to C, then the angle formed by points C, A, and B is equal to the angle formed by points A, B, and C.

### Informal sketch
* The proof starts by assuming that the distance from point A to C is equal to the distance from point B to C.
* It then uses the `CONGRUENT_TRIANGLES_SSS` theorem, which states that two triangles are congruent if their corresponding sides are equal, to establish a relationship between the angles of the two triangles.
* The `MP_TAC` tactic is used to apply modus ponens, which allows us to derive a conclusion from a proven statement.
* The `MESON_TAC` tactic is used with the `DIST_SYM` and `ANGLE_SYM` theorems to derive the final conclusion about the equality of the angles.
* The key idea is to use the congruence of the triangles to establish the equality of the angles.

### Mathematical insight
The Isosceles Triangle Theorem is a fundamental result in geometry that states that the base angles of an isosceles triangle are equal. This theorem is important because it provides a way to establish the equality of angles in a triangle based on the equality of the sides. It is a canonical construction because it is a basic result that is used in many other proofs in geometry.

### Dependencies
* Theorems:
  * `CONGRUENT_TRIANGLES_SSS`
  * `DIST_SYM`
  * `ANGLE_SYM`
* Definitions:
  * `dist`
  * `angle`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `CONGRUENT_TRIANGLES_SSS` theorem is properly instantiated and that the `MP_TAC` and `MESON_TAC` tactics are replaced with equivalent tactics in the target system. Additionally, the `DIST_SYM` and `ANGLE_SYM` theorems should be properly defined and used in the proof.

---

## ISOSCELES_TRIANGLE_CONVERSE

### Name of formal statement
ISOSCELES_TRIANGLE_CONVERSE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ISOSCELES_TRIANGLE_CONVERSE = prove
 (`!A B C:real^N. angle(C,A,B) = angle(A,B,C) /\ ~(collinear {A,B,C})
                  ==> dist(A,C) = dist(B,C)`,
  MP_TAC(INST_TYPE [`:N`,`:M`] CONGRUENT_TRIANGLES_ASA_FULL) THEN
  MESON_TAC[DIST_SYM; ANGLE_SYM])
```

### Informal statement
For all points A, B, and C in real N-dimensional space, if the angle at C between the line segments CA and CB is equal to the angle at A between the line segments AB and AC, and the points A, B, and C are not collinear, then the distance from A to C is equal to the distance from B to C.

### Informal sketch
* The proof starts with the assumption that `angle(C,A,B) = angle(A,B,C)` and `~(collinear {A,B,C})`.
* It then applies the `CONGRUENT_TRIANGLES_ASA_FULL` theorem, which is instantiated with types `:N` and `:M`.
* The `MP_TAC` tactic is used to apply modus ponens, allowing the conclusion of the equality of distances `dist(A,C) = dist(B,C)`.
* The `MESON_TAC` tactic is used with the `DIST_SYM` and `ANGLE_SYM` theorems to derive the final conclusion.

### Mathematical insight
This theorem is the converse of the isosceles triangle property, stating that if two angles of a triangle are equal, then the sides opposite those angles are also equal. The theorem is important in geometry as it provides a way to prove that a triangle is isosceles based on angle equality. The use of `CONGRUENT_TRIANGLES_ASA_FULL` theorem suggests that the proof relies on the concept of congruent triangles and the side-angle-side (SAS) criterion for congruence.

### Dependencies
* Theorems:
  * `CONGRUENT_TRIANGLES_ASA_FULL`
  * `DIST_SYM`
  * `ANGLE_SYM`
* Definitions:
  * `angle`
  * `dist`
  * `collinear`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of geometric concepts such as angles, distances, and collinearity. The `CONGRUENT_TRIANGLES_ASA_FULL` theorem may need to be ported or re-proved in the target system. Additionally, the use of `MP_TAC` and `MESON_TAC` tactics may need to be translated into the corresponding tactics or proof scripts in the target system.

---

## lemma

### Name of formal statement
lemma

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[ANGLE_EQ_PI_OTHERS; BETWEEN_ANGLE])
```

### Informal statement
For all points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if $D$ is between $A$ and $B$, then the vectors $A - B$ and $C - D$ are orthogonal if and only if the angle between $A$, $D$, and $C$ is $\frac{\pi}{2}$ and the angle between $B$, $D$, and $C$ is $\frac{\pi}{2}$.

### Informal sketch
* The proof proceeds by cases, first considering when $D = A$ and then when $D = B$, using `ASM_CASES_TAC` to handle these base cases.
* For the general case, it uses `MP_TAC` with `ANGLES_ALONG_LINE` to establish relationships between angles.
* It then applies `MATCH_MP_TAC` with a `REAL_ARITH` statement to reason about equalities involving angles.
* Further simplifications and rewrites are applied using `REWRITE_TAC` and `ASM_REWRITE_TAC`, involving `ORTHOGONAL_VECTOR_ANGLE`, `VECTOR_NEG_SUB`, and `angle`.
* The proof concludes with `ASM_MESON_TAC`, leveraging `ANGLE_EQ_PI_OTHERS` and `BETWEEN_ANGLE`.

### Mathematical insight
This lemma provides an equivalence between the orthogonality of two vectors and the right angles formed by three points in $\mathbb{R}^N$. It's crucial for establishing geometric properties and is related to the concept of the "Inscribed Angle Theorem" (ITT), highlighting the connection between angles and orthogonality in a geometric context.

### Dependencies
#### Theorems
* `ANGLES_ALONG_LINE`
* `REAL_ARITH`
* `VECTOR_ANGLE_EQ_0_RIGHT`
* `ANGLE_EQ_PI_OTHERS`
#### Definitions
* `orthogonal`
* `angle`
* `between`

---

## ISOSCELES_TRIANGLE_1

### Name of formal statement
ISOSCELES_TRIANGLE_1

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[DIST_MIDPOINT] THEN ASM_MESON_TAC[DIST_SYM; ANGLE_SYM])
```

### Informal statement
For all points A, B, C, and D in real N-dimensional space, if the distance from A to C is equal to the distance from B to C, and D is the midpoint of the line segment AB, then the angle formed by points A, C, and D is equal to the angle formed by points B, C, and D.

### Informal sketch
* The proof begins by assuming the conditions `dist(A,C) = dist(B,C)` and `D = midpoint(A,B)`.
* It then applies the `CONGRUENT_TRIANGLES_SSS_FULL` theorem with specific instantiations to establish a relationship between the angles.
* The `DIST_MIDPOINT` definition is used to rewrite the midpoint condition in terms of distances.
* Finally, the proof uses `DIST_SYM` and `ANGLE_SYM` properties to derive the conclusion about the equality of angles.
* The `REPEAT STRIP_TAC`, `MP_TAC`, `ASM_REWRITE_TAC`, and `ASM_MESON_TAC` tactics are used to manage the proof steps, including stripping away universal quantifiers, applying theorems, and performing rewriting and meson (meta-theory) reasoning.

### Mathematical insight
This theorem captures a fundamental property of isosceles triangles in N-dimensional space, where two sides have equal length, and the angles opposite these sides are also equal. The use of midpoints and distance equalities provides a geometric intuition that is essential in various geometric and trigonometric proofs.

### Dependencies
* Theorems:
  + `CONGRUENT_TRIANGLES_SSS_FULL`
  + `DIST_MIDPOINT`
  + `DIST_SYM`
  + `ANGLE_SYM`
* Definitions:
  + `midpoint`
  + `dist`
  + `angle`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles geometric definitions, midpoint calculations, and angle equalities. The `CONGRUENT_TRIANGLES_SSS_FULL` theorem and its instantiations might require careful handling, as the specifics of how congruent triangles are defined and proven can vary between systems. Additionally, the use of `REPEAT STRIP_TAC`, `MP_TAC`, `ASM_REWRITE_TAC`, and `ASM_MESON_TAC` tactics may need to be adapted, as their direct equivalents might not exist in the target system, requiring a strategic rephrasing of the proof steps.

---

## ISOSCELES_TRIANGLE_2

### Name of formal statement
ISOSCELES_TRIANGLE_2

### Type of the formal statement
Theorem

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
      ANGLES_ALONG_LINE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC)
```

### Informal statement
For all points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if $D$ lies between $A$ and $B$, and the distance from $A$ to $C$ is equal to the distance from $B$ to $C$, and the angle $\angle ACD$ is equal to the angle $\angle BCD$, then the vectors $A - B$ and $C - D$ are orthogonal.

### Informal sketch
* The proof starts by assuming the premises: $D$ is between $A$ and $B$, $dist(A,C) = dist(B,C)$, and $\angle(A,C,D) = \angle(B,C,D)$.
* It then applies the `ISOSCELES_TRIANGLE_THEOREM` to establish some initial properties.
* The proof proceeds by case analysis:
  + If $D = B$, it simplifies using properties of distance and orthogonality.
  + If $D = A$, it simplifies using properties of distance.
  + For other cases, it applies `CONGRUENT_TRIANGLES_SAS_FULL` and `ANGLES_ALONG_LINE` to derive the orthogonality of $A - B$ and $C - D$.
* The proof involves using `REAL_ARITH_TAC` for arithmetic reasoning and `ASM_MESON_TAC` for deriving conclusions from known properties.

### Mathematical insight
This theorem is important because it establishes a geometric property related to isosceles triangles and orthogonality in $\mathbb{R}^N$. It provides insight into the relationship between angles, distances, and vector orthogonality, which is fundamental in various areas of mathematics and physics.

### Dependencies
#### Theorems
* `ISOSCELES_TRIANGLE_THEOREM`
* `CONGRUENT_TRIANGLES_SAS_FULL`
* `ANGLES_ALONG_LINE`
#### Definitions
* `dist`
* `angle`
* `orthogonal`
#### Lemmas
* `DIST_SYM`
* `ANGLE_SYM`
* `DIST_EQ_0`
* `DIST_REFL`
* `VECTOR_SUB_REFL`
* `ORTHOGONAL_0`

---

## ISOSCELES_TRIANGLE_3

### Name of formal statement
ISOSCELES_TRIANGLE_3

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[ANGLE_EQ_PI_OTHERS; BETWEEN_ANGLE])
```

### Informal statement
For all points `A`, `B`, `C`, and `D` in `real^N`, if `D` is between `A` and `B`, the distance from `A` to `C` is equal to the distance from `B` to `C`, and the vector `A - B` is orthogonal to the vector `C - D`, then `D` is the midpoint of `A` and `B`.

### Informal sketch
* The proof starts by considering cases based on whether `A` equals `B`, and then whether `D` equals `A` or `B`.
* It applies `PYTHAGORAS` to establish relationships between the distances and uses `ORTHOGONAL_LNEG` and `VECTOR_NEG_SUB` to reason about orthogonality.
* The proof then uses `MIDPOINT_COLLINEAR`, `BETWEEN_IMP_COLLINEAR`, and `ISOSCELES_TRIANGLE_THEOREM` to derive properties about midpoints and collinearity.
* It applies `CONGRUENT_TRIANGLES_SAS` to show congruence between triangles and uses `TRIANGLE_ANGLE_SUM` to reason about angles.
* The proof concludes by using `REAL_ARITH` and `ANGLE_SYM` to derive the final equality.

### Mathematical insight
This theorem provides a condition for a point `D` to be the midpoint of line segment `AB`, given that `D` is between `A` and `B`, and the distances from `A` and `B` to a third point `C` are equal, with the additional constraint that the line segment `AB` is orthogonal to the line segment `CD`. This is a geometric property that can be useful in various geometric and trigonometric contexts.

### Dependencies
* Theorems:
  + `PYTHAGORAS`
  + `ORTHOGONAL_LNEG`
  + `VECTOR_NEG_SUB`
  + `MIDPOINT_COLLINEAR`
  + `BETWEEN_IMP_COLLINEAR`
  + `ISOSCELES_TRIANGLE_THEOREM`
  + `CONGRUENT_TRIANGLES_SAS`
  + `TRIANGLE_ANGLE_SUM`
  + `REAL_ARITH`
  + `ANGLE_SYM`
  + `ANGLE_EQ_0_LEFT`
  + `ANGLE_EQ_0_RIGHT`
  + `ANGLE_EQ_PI_OTHERS`
  + `BETWEEN_ANGLE`
* Definitions:
  + `midpoint`
  + `between`
  + `dist`
  + `orthogonal`
  + `angle`

---

## ISOSCELES_TRIANGLE_4

### Name of formal statement
ISOSCELES_TRIANGLE_4

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[DIST_MIDPOINT])
```

### Informal statement
For all points A, B, C, and D in real N-dimensional space, if D is the midpoint of the line segment AB and the vector A - B is orthogonal to the vector C - D, then the distance from A to C is equal to the distance from B to C.

### Informal sketch
* The proof starts by assuming the antecedent conditions: D is the midpoint of AB, and A - B is orthogonal to C - D.
* It then applies various simplifications and rewrites, utilizing `IMP_CONJ`, `BETWEEN_MIDPOINT`, and a `lemma` to simplify the assumptions.
* The proof proceeds by discharging assumptions and applying `CONGRUENT_TRIANGLES_SAS` to establish the congruence of triangles, which leads to the conclusion that the distances from A to C and from B to C are equal.
* Key steps involve using `EXISTS_TAC` to introduce points and `ASM_REWRITE_TAC` to simplify expressions, culminating in the application of `DIST_MIDPOINT` to relate distances and midpoints.

### Mathematical insight
This theorem captures a geometric property of isosceles triangles in N-dimensional space, providing a condition under which a triangle is isosceles based on the orthogonality of vectors and the midpoint of a side. It's a foundational result that could be used in various geometric and analytical arguments, especially those involving properties of triangles and distances in higher-dimensional spaces.

### Dependencies
* Theorems:
  - `CONGRUENT_TRIANGLES_SAS`
* Definitions:
  - `midpoint`
  - `orthogonal`
  - `dist`
* Lemmas:
  - `lemma`
* Other:
  - `IMP_CONJ`
  - `BETWEEN_MIDPOINT`
  - `DIST_MIDPOINT`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how midpoints, orthogonality, and distances are defined and handled, as these may differ between systems. Additionally, the use of `CONGRUENT_TRIANGLES_SAS` and the specific tactic script may need to be adapted based on the target system's capabilities and automation levels.

---

## ISOSCELES_TRIANGLE_5

### Name of formal statement
ISOSCELES_TRIANGLE_5

### Type of the formal statement
Theorem

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
  ONCE_REWRITE_TAC[ANGLE_SYM] THEN ASM_REWRITE_TAC[])
```

### Informal statement
For all points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if $D$ is not collinear with $C$ and $A$, and $D$ is between $A$ and $B$, and the angle formed by $A$, $C$, and $D$ is equal to the angle formed by $B$, $C$, and $D$, and the vectors $A - B$ and $C - D$ are orthogonal, then the distance from $A$ to $C$ is equal to the distance from $B$ to $C$.

### Informal sketch
* The proof starts by assuming the conditions: $D$ is not collinear with $C$ and $A$, $D$ is between $A$ and $B$, the angles $\angle ACD$ and $\angle BCD$ are equal, and vectors $A - B$ and $C - D$ are orthogonal.
* It then considers cases based on whether $C = D$, $A = B$, $C = A$, and $C = B$, using `ASM_CASES_TAC` to handle these possibilities and derive contradictions or simplifications where applicable.
* For the main case, it applies the `CONGRUENT_TRIANGLES_ASA_FULL` theorem to triangles $ACD$ and $BCD$ after establishing the necessary conditions for their congruence, utilizing `ISPECL` to instantiate the theorem with the appropriate points.
* The proof also involves simplifications using `ASM_SIMP_TAC` and `REAL_ARITH_TAC` to handle real arithmetic and geometric properties, and `MATCH_MP` with `ANGLE_EQ_PI_OTHERS` to reason about angles.
* The use of `DISCH_THEN` and `UNDISCH_TAC` helps manage assumptions and conclusions throughout the proof.

### Mathematical insight
This theorem captures a geometric property related to isosceles triangles and orthogonal vectors. It states that under specific conditions involving angles, collinearity, and orthogonality, two sides of a triangle (formed by connecting points $A$, $B$, and $C$) are of equal length. The conditions imply a form of symmetry that leads to the isosceles property.

### Dependencies
#### Theorems
* `CONGRUENT_TRIANGLES_ASA_FULL`
* `ANGLE_EQ_PI_OTHERS`
* `PI_NZ`
#### Definitions
* `collinear`
* `between`
* `angle`
* `orthogonal`
* `dist`
#### Lemmas
* `ANGLE_REFL`
* `ANGLE_REFL_MID`
* `REAL_ARITH` 
* `IMP_CONJ` 
* `DIST_SYM`

---

## ISOSCELES_TRIANGLE_6

### Name of formal statement
ISOSCELES_TRIANGLE_6

### Type of the formal statement
Theorem

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
    MESON_TAC[VECTOR_MUL_ASSOC])
```

### Informal statement
For all points `A`, `B`, `C`, and `D` in `real^N`, if `D` is not collinear with `C` and `A`, `D` is the midpoint of `A` and `B`, and the angle between `A`, `C`, and `D` is equal to the angle between `B`, `C`, and `D`, then the distance between `A` and `C` is equal to the distance between `B` and `C`.

### Informal sketch
* The proof starts by assuming the conditions `~collinear{D,C,A}`, `D = midpoint(A,B)`, and `angle(A,C,D) = angle(B,C,D)`.
* It then applies the `LAW_OF_SINES` to triangles `A`, `C`, `D` and `B`, `C`, `D` to derive equalities involving the sine of angles.
* The proof proceeds by considering cases, including when `A = B`, and applies various simplifications and rewrites using properties of real numbers, distances, and angles.
* Key steps involve using `CONGRUENT_TRIANGLES_AAS` to establish congruence between triangles, and `TRIANGLE_ANGLE_SUM` to reason about angle sums in triangles.
* The proof also uses properties of midpoints, collinearity, and vector arithmetic to derive the final conclusion about equal distances.

### Mathematical insight
This theorem establishes a condition under which a triangle is isosceles, based on the equality of angles and the midpoint property. It is a fundamental geometric result that has implications for various geometric constructions and proofs.

### Dependencies
* Theorems:
	+ `LAW_OF_SINES`
	+ `CONGRUENT_TRIANGLES_AAS`
	+ `TRIANGLE_ANGLE_SUM`
	+ `BETWEEN_MIDPOINT`
	+ `COLLINEAR_ANGLE`
* Definitions:
	+ `midpoint`
	+ `collinear`
	+ `angle`
	+ `dist`
* Properties:
	+ `REAL_EQ_MUL_RCANCEL`
	+ `REAL_LT_IMP_NZ`
	+ `REAL_HALF`
	+ `DIST_POS_LT`
	+ `SIN_ANGLE_EQ`
	+ `VECTOR_MUL_ASSOC`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of:
* Quantifiers and variables
* Geometric definitions and properties (e.g., `midpoint`, `collinear`, `angle`)
* Real number arithmetic and trigonometric functions
* Triangle congruence and properties (e.g., `CONGRUENT_TRIANGLES_AAS`, `TRIANGLE_ANGLE_SUM`)
* Vector arithmetic and properties (e.g., `VECTOR_MUL_ASSOC`)

---

