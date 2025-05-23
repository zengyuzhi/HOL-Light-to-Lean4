# isosceles.ml

## Overview

Number of statements: 9

This file contains the formalization and proof of the isosceles triangle theorem in Euclidean geometry, which states that the base angles of an isosceles triangle are equal. It builds on HOL Light's multivariate geometry library (geom.ml) and likely includes the definitions of isosceles triangles along with the formal proof of this foundational result. The file represents a concrete application of the geometric reasoning framework in HOL Light to prove a classic elementary geometry theorem.

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
For any points $A$, $B$, and $C$ in $\mathbb{R}^N$, if $\text{dist}(A,C) = \text{dist}(B,C)$ (i.e., the triangle is isosceles with two sides of equal length), then the angles at the base of the isosceles triangle are equal: $\text{angle}(C,A,B) = \text{angle}(A,B,C)$.

### Informal proof
The proof uses the SSS (Side-Side-Side) congruence criterion for triangles:

1. Start with the theorem `CONGRUENT_TRIANGLES_SSS` which states that if all corresponding sides of two triangles have equal lengths, then all corresponding angles are equal.

2. We instantiate this theorem with the same triangle twice (using different type variables):
   - The first triangle is $(A,B,C)$ in $\mathbb{R}^N$
   - The second triangle is $(A',B',C') = (B,A,C)$ in $\mathbb{R}^N$ (with $A$ and $B$ swapped)

3. For these triangles:
   - $\text{dist}(A,B) = \text{dist}(B,A)$ by symmetry of distance
   - $\text{dist}(B,C) = \text{dist}(A,C)$ by our hypothesis
   - $\text{dist}(C,A) = \text{dist}(C,B)$ by symmetry of distance

4. By `CONGRUENT_TRIANGLES_SSS`, we can conclude that all corresponding angles are equal.
   In particular, $\text{angle}(C,A,B) = \text{angle}(C,B,A)$.
   
5. Using `ANGLE_SYM`, which states that $\text{angle}(A,B,C) = \text{angle}(C,B,A)$, we obtain:
   $\text{angle}(C,A,B) = \text{angle}(A,B,C)$

The `MESON_TAC` automated proof tactic completes the proof using facts about symmetry of distance and angles.

### Mathematical insight
This theorem captures a fundamental property of isosceles triangles: the angles opposite to the equal sides are themselves equal. This result is one of the oldest in geometry, attributed to Thales of Miletus (c. 624–546 BCE) and appears in Euclid's Elements (Book I, Proposition 5).

The proof approach uses triangle congruence as a key tool, essentially showing that an isosceles triangle is congruent to itself when reflected across its line of symmetry. This emphasizes how symmetry principles can be applied in geometric proofs.

This theorem forms the basis for many other results in Euclidean geometry and is frequently used in geometric reasoning about triangles.

### Dependencies
- Theorems:
  - `CONGRUENT_TRIANGLES_SSS`: If all corresponding sides of two triangles are equal in length, then all corresponding angles are equal.
  - `DIST_SYM`: Distance function is symmetric, i.e., $\text{dist}(A,B) = \text{dist}(B,A)$.
  - `ANGLE_SYM`: Angle measure is symmetric in its outer points, i.e., $\text{angle}(A,B,C) = \text{angle}(C,B,A)$.

### Porting notes
When porting to other proof assistants:
1. Check how angles are defined in the target system. Some systems define angles using vectors rather than points.
2. Ensure the target system has a suitable version of the SSS triangle congruence theorem.
3. Note that HOL Light's `MESON_TAC` is a powerful automated reasoning tool - in other systems, this part of the proof might require more explicit reasoning steps about symmetry.

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
For all points $A$, $B$, and $C$ in $\mathbb{R}^N$, if the angle at $A$ equals the angle at $B$ (that is, $\angle CAB = \angle ABC$) and the points $A$, $B$, and $C$ are not collinear, then the distances from $A$ to $C$ and from $B$ to $C$ are equal (that is, $|AC| = |BC|$).

### Informal proof
We can prove this by applying the ASA (Angle-Side-Angle) congruence criterion for triangles.

The proof leverages the `CONGRUENT_TRIANGLES_ASA_FULL` theorem, which states that two triangles are congruent if they have two angles and the included side equal.

Here, we consider the triangle $ABC$ and essentially compare it with itself, but with vertices $A$ and $B$ swapped. Given:
- $\angle CAB = \angle ABC$ (by hypothesis)
- $|AB| = |BA|$ (by symmetry of distance)
- The points are not collinear

By the ASA criterion, we can conclude that $|AC| = |BC|$, which is what we wanted to prove.

The formal proof uses `MESON_TAC` with `DIST_SYM` (distance symmetry) and `ANGLE_SYM` (angle symmetry) to handle the technical details after applying `CONGRUENT_TRIANGLES_ASA_FULL`.

### Mathematical insight
This theorem states the converse of a well-known property of isosceles triangles: if two angles in a triangle are equal, then the sides opposite to these angles are equal. This is a fundamental result in Euclidean geometry.

The key insight is that when two angles of a triangle are equal, the triangle has an axis of symmetry passing through the third vertex and bisecting the opposite side. This symmetry forces the distances from the third vertex to the other two vertices to be equal.

This theorem, together with its direct counterpart (that equal sides imply equal angles), completely characterizes isosceles triangles.

### Dependencies
- **Theorems**:
  - `CONGRUENT_TRIANGLES_ASA_FULL`: Angle-Side-Angle congruence criterion for triangles
  - `DIST_SYM`: Symmetry of the distance function
  - `ANGLE_SYM`: Symmetry property of angles

### Porting notes
When porting to other proof assistants:
1. Ensure the target system has a properly defined angle function that satisfies the same properties.
2. Check how the target system handles non-collinearity; some systems might prefer to state this as three points not lying on a common line.
3. The ASA congruence criterion is a standard result in Euclidean geometry, but its formal statement might differ slightly in other proof assistants.

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
For all points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if $D$ lies between $A$ and $B$, then the vector $(A - B)$ is orthogonal to $(C - D)$ if and only if both $\angle ADC = \frac{\pi}{2}$ and $\angle BDC = \frac{\pi}{2}$.

In other words, if $D$ is on the line segment between $A$ and $B$, then the line from $A$ to $B$ is perpendicular to the line from $D$ to $C$ if and only if both angles at $D$ are right angles.

### Informal proof
The proof proceeds by case analysis:

- **Case 1: $D = A$**
  If $D = A$, then $\angle ADC$ is undefined (as it would require $A \neq D$), so we reinterpret using vectors. We have:
  - $\angle ADC = \angle AAC$ is undefined, but by convention of `ANGLE_REFL`, we consider its value.
  - The orthogonality condition becomes: $(A - B)$ is orthogonal to $(C - A)$
  - This can be rewritten as $-(B - A)$ is orthogonal to $(C - A)$, which is equivalent to $(B - A)$ being orthogonal to $(C - A)$
  - By the `ORTHOGONAL_VECTOR_ANGLE` theorem, this is equivalent to the vector angle being $\frac{\pi}{2}$
  - The conclusion follows directly.

- **Case 2: $D = B$**
  If $D = B$, similar reasoning applies as in Case 1, leading to the conclusion.

- **Case 3: $D \neq A$ and $D \neq B$**
  - Since $D$ is between $A$ and $B$, by `ANGLES_ALONG_LINE`, we have $\angle ADC + \angle BDC = \pi$
  - Using the definition of orthogonality in terms of vector angles, the orthogonality condition $(A - B) \perp (C - D)$ is equivalent to the vector angle being $\frac{\pi}{2}$
  - We show that the vector angle between $-(A - D)$ and $-(B - D)$ equals 0, which means $\angle ADB = \pi$ by `BETWEEN_ANGLE`
  - Using `ANGLE_EQ_PI_OTHERS`, this means various other angles are 0
  - By algebraic manipulation using the constraint $\angle ADC + \angle BDC = \pi$, we conclude that $(A - B) \perp (C - D)$ if and only if both angles equal $\frac{\pi}{2}$

### Mathematical insight
This theorem is a version of the Inscribed Thales' Theorem (ITT), which relates perpendicularity to right angles in a geometric configuration. It provides a key characterization of when a line is perpendicular to another line through a point on the first line.

The result gives an important relationship between orthogonality of vectors and the angles formed at a point between points. It's particularly useful in computational geometry and can be used to verify perpendicularity using angle measurements.

### Dependencies
- Theorems:
  - `VECTOR_ANGLE_NEG2`: The vector angle between negated vectors equals the original vector angle
  - `ORTHOGONAL_VECTOR_ANGLE`: Two vectors are orthogonal if and only if their vector angle is $\frac{\pi}{2}$
  - `VECTOR_ANGLE_EQ_0_RIGHT`: If the vector angle between x and y is 0, then the vector angle from x to z equals that from y to z
  - `ANGLE_EQ_PI_OTHERS`: If angle(A,B,C) = π, then several related angles are 0
  - `BETWEEN_ANGLE`: Point x is between points a and b if and only if x=a or x=b or angle(a,x,b) = π
  - `ANGLES_ALONG_LINE`: If C is between A and B, then angle(A,C,D) + angle(B,C,D) = π

### Porting notes
When porting this theorem:
- Be aware that different systems may handle angle definitions differently
- The proof relies on HOL Light's convention for angles at coincident points
- Be prepared to establish the dependencies like `ANGLES_ALONG_LINE` and `ANGLE_EQ_PI_OTHERS`
- The use of vector algebra might need adjustment in systems that use different approaches to geometry

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
For all points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if $\text{dist}(A,C) = \text{dist}(B,C)$ and $D = \text{midpoint}(A,B)$, then $\angle(A,C,D) = \angle(B,C,D)$.

### Informal proof
The proof follows from the properties of congruent triangles:

1. We start by applying the SSS (Side-Side-Side) congruence theorem to triangles $ACD$ and $BCD$.

2. For this application, we need to verify that:
   - $\text{dist}(A,D) = \text{dist}(B,D)$: This is true because $D$ is the midpoint of segment $AB$, so the distances from $D$ to both endpoints are equal.
   - $\text{dist}(A,C) = \text{dist}(B,C)$: This is given in the hypothesis.
   - $\text{dist}(D,C) = \text{dist}(D,C)$: This is trivially true (same segment).

3. By the SSS congruence theorem (CONGRUENT_TRIANGLES_SSS_FULL), we can conclude that all corresponding parts of the triangles are equal, including the angles.

4. Therefore, $\angle(A,C,D) = \angle(B,C,D)$.

### Mathematical insight
This theorem formalizes a basic property of isosceles triangles: in a triangle where two sides are equal, the angles opposite to these sides are also equal. Specifically, when $D$ is the midpoint of the base $AB$ of an isosceles triangle $ABC$ (where $AC = BC$), the angles formed at vertex $C$ by lines to $A$ and $D$, and by lines to $B$ and $D$, are equal.

This result is part of the foundational properties of Euclidean geometry and is related to the more general principle of symmetry in isosceles triangles. The theorem can be visualized by noting that the line from the apex to the midpoint of the base is an axis of symmetry for the isosceles triangle.

### Dependencies
- **Theorems**:
  - `CONGRUENT_TRIANGLES_SSS_FULL`: States that if all three sides of one triangle are equal in length to the corresponding sides of another triangle, then all corresponding angles are also equal.
  - `DIST_MIDPOINT`: A property about the distance from endpoints to the midpoint.
  - `DIST_SYM`: States that distance is symmetric, i.e., $\text{dist}(A,B) = \text{dist}(B,A)$.
  - `ANGLE_SYM`: States that angle measure is symmetric under certain permutations of points.

### Porting notes
When porting this theorem:
1. Ensure that the target system has a well-defined notion of Euclidean distance, midpoint, and angle measure in n-dimensional space.
2. Verify that the congruence theorems (especially SSS) are available or can be proven.
3. The proof relies on the symmetry properties of distances and angles, which should be established in the target system.

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
For any points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if $D$ lies between $A$ and $B$, the distances $\|A-C\| = \|B-C\|$ are equal (making triangle $ABC$ isosceles), and the angles $\angle ACD = \angle BCD$ are equal, then the vectors $A-B$ and $C-D$ are orthogonal.

### Informal proof
The proof uses geometric properties of isosceles triangles and congruent triangles:

* Start with the assumptions: $D$ is between $A$ and $B$, $\|A-C\| = \|B-C\|$, and $\angle ACD = \angle BCD$.

* From the isosceles triangle condition $\|A-C\| = \|B-C\|$, we apply `ISOSCELES_TRIANGLE_THEOREM` to establish additional properties of isosceles triangles. This theorem is not in the dependency list but presumably relates to properties of isosceles triangles.

* Next, apply the congruent triangles theorem `CONGRUENT_TRIANGLES_SAS_FULL` to the triangles $\Delta DCA$ and $\Delta DCB$ using:
  - Equal sides: $\|D-C\| = \|D-C\|$ (same side)
  - Equal angles: $\angle DCA = \angle DCB$ (given)
  - Equal sides: $\|C-A\| = \|C-B\|$ (from isosceles triangle property)

* Handle two special cases:
  - If $D = B$, then $A-B$ and $C-D$ are orthogonal trivially since $C-D = C-B$ and $A-B$ are orthogonal by the isosceles triangle property.
  - If $D = A$, we reach a contradiction with the distance properties.

* For the general case, use a lemma (not specified in the dependencies) that likely relates congruent triangles to the orthogonality condition.

* Apply `ANGLES_ALONG_LINE` to points $A$, $B$, $D$, and $C$, which states that when $D$ lies between $A$ and $B$, the angles $\angle ADC + \angle BDC = \pi$.

* The proof concludes with real arithmetic to establish that vectors $A-B$ and $C-D$ are orthogonal.

### Mathematical insight
This theorem establishes an important property relating isosceles triangles to orthogonality. Specifically, when a point $D$ lies on the line segment between $A$ and $B$, and $C$ forms an isosceles triangle with $A$ and $B$ (with equal angles at $C$), then the vector from $A$ to $B$ is perpendicular to the vector from $C$ to $D$.

This result is a geometric characterization connecting the symmetry of isosceles triangles to orthogonal projections. It can be visualized as stating that the line from $C$ to $D$ forms the perpendicular bisector of segment $AB$ when the conditions are met.

### Dependencies
- **Theorems:**
  - `CONGRUENT_TRIANGLES_SAS_FULL`: Establishes the Side-Angle-Side criterion for triangle congruence, showing that if corresponding sides and included angles of two triangles are equal, then all sides and angles are equal.
  - `ANGLES_ALONG_LINE`: States that if point $C$ lies between points $A$ and $B$, then for any point $D$, the angles $\angle ACD + \angle BCD = \pi$.
  - `ISOSCELES_TRIANGLE_THEOREM`: Not in the provided dependencies, but presumably states properties of isosceles triangles.
  - `lemma`: An unnamed lemma used in the proof, not provided in the dependencies.

### Porting notes
When porting this theorem:
1. Ensure your target system has appropriate definitions for distance (`dist`), vectors, angles, orthogonality, and the "between" relation.
2. The "between" relation in HOL Light indicates that a point lies on the line segment between two other points.
3. The orthogonality of vectors $A-B$ and $C-D$ may be expressed differently in other systems, possibly using inner products or dot products.
4. Check if the target system has similar theorems about isosceles triangles and triangle congruence to substitute for the dependencies.

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
For any points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if:
1. $D$ lies between $A$ and $B$,
2. $\text{dist}(A,C) = \text{dist}(B,C)$ (i.e., $C$ is equidistant from $A$ and $B$), and
3. $(A - B)$ is orthogonal to $(C - D)$,

then $D$ is the midpoint of line segment $[A,B]$.

### Informal proof
The proof proceeds by case analysis:

* First, we handle the trivial case when $A = B$. In this case, any point "between" $A$ and $B$ must equal $A = B$, and the midpoint of $(A,B)$ is also $A = B$.

* Next, we check two cases where $D$ coincides with an endpoint:

  * Case $D = A$: By the orthogonality condition and the Pythagorean theorem, we get that $B = A$, contradicting our assumption that $A \neq B$.
  
  * Case $D = B$: Similarly, we derive that $A = B$, again contradicting our assumption.

* For the main case where $D$ is strictly between $A$ and $B$:
  
  * We use a lemma that shows $D$ lies on the line through $A$ and $B$ (from the between condition).
  
  * From the isosceles condition ($\text{dist}(A,C) = \text{dist}(B,C)$), we know that the base angles are equal: $\angle(C,A,B) = \angle(A,B,C)$.
  
  * We apply the law of congruent triangles (SAS - Side-Angle-Side) to triangles $ACD$ and $BCD$.
  
  * Using the fact that the sum of angles in a triangle is $\pi$, and that $D$ being between $A$ and $B$ implies $\angle(A,D,B) = \pi$, we can show that $\text{dist}(A,D) = \text{dist}(B,D)$.
  
  * Since $D$ is on the line through $A$ and $B$ and equidistant from both points, $D$ must be the midpoint of $[A,B]$.

### Mathematical insight
This theorem provides a geometric characterization of the midpoint of a line segment using orthogonality and the properties of isosceles triangles. Specifically, it shows that if a point $D$ lies on a line segment $[A,B]$ and the perpendicular from $D$ to a point $C$ (where $C$ is equidistant from $A$ and $B$) is orthogonal to the line $AB$, then $D$ must be exactly the midpoint of $[A,B]$.

The result is related to the perpendicular bisector property - the perpendicular bisector of a line segment is the locus of points equidistant from the endpoints. Here, we're given that $C$ is equidistant from the endpoints and we're finding when a point $D$ on the segment makes the line $CD$ perpendicular to the segment.

### Dependencies
- **Theorems**:
  - `ANGLE_EQ_0_RIGHT`: If $\angle(A,B,C) = 0$, then $\angle(A,B,D) = \angle(C,B,D)$
  - `ANGLE_EQ_0_LEFT`: If $\angle(A,B,C) = 0$, then $\angle(D,B,A) = \angle(D,B,C)$
  - `ANGLE_EQ_PI_OTHERS`: If $\angle(A,B,C) = \pi$, then the angles at the other vertices of the triangle are 0
  - `CONGRUENT_TRIANGLES_SAS`: The SAS (Side-Angle-Side) congruence criterion for triangles
  - `BETWEEN_ANGLE`: A point is between two others if and only if the angle at that point is $\pi$
  - Implicitly used:
    - `PYTHAGORAS`: The Pythagorean theorem
    - `TRIANGLE_ANGLE_SUM`: The sum of angles in a triangle equals $\pi$
    - `ISOSCELES_TRIANGLE_THEOREM`: In an isosceles triangle, the base angles are equal

### Porting notes
When porting this theorem to other systems, pay attention to:
1. The representation of the "between" relation, which in HOL Light means that a point lies on the line segment between two endpoints
2. The definition of orthogonality, which uses the vector representation directly
3. The handling of midpoint and distance functions, which might have different definitions in other systems
4. How vectors are represented (e.g., as tuples, records, or objects)

The proof relies heavily on Euclidean geometry theorems that should be available in most systems, though their exact formulation may differ.

---

## ISOSCELES_TRIANGLE_4

### ISOSCELES_TRIANGLE_4
- `ISOSCELES_TRIANGLE_4`

### Type of the formal statement
- theorem

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
For all points $A, B, C, D$ in $\mathbb{R}^N$:

If $D$ is the midpoint of segment $AB$ and the vector $A - B$ is orthogonal to the vector $C - D$, then $\text{dist}(A, C) = \text{dist}(B, C)$.

In other words, if $D$ is the midpoint of $AB$ and the line $CD$ is perpendicular to line $AB$, then $C$ is equidistant from $A$ and $B$, making triangle $ABC$ isosceles.

### Informal proof
The proof follows these steps:

* We have $D = \text{midpoint}(A,B)$ and the vectors $A-B$ and $C-D$ are orthogonal.
* By the `lemma` (which appears to establish that orthogonality of $A-B$ and $C-D$ implies $\text{angle}(A,D,C) = \text{angle}(B,D,C)$), we get that $\text{angle}(A,D,C) = \text{angle}(B,D,C)$.
* We apply the SAS (Side-Angle-Side) congruence criterion for triangles using `CONGRUENT_TRIANGLES_SAS` to show that triangles $ADC$ and $BDC$ are congruent:
  * $\text{dist}(A,D) = \text{dist}(B,D)$ since $D$ is the midpoint of $AB$ (using `DIST_MIDPOINT`)
  * $\text{angle}(A,D,C) = \text{angle}(B,D,C)$ as established above
  * $\text{dist}(D,C) = \text{dist}(D,C)$ (same side)
* Therefore $\text{dist}(A,C) = \text{dist}(B,C)$, which completes the proof.

### Mathematical insight
This theorem establishes a key property of isosceles triangles: the perpendicular line from the apex to the base bisects the base. More specifically, it shows that if a point is equidistant from the endpoints of a line segment, then the point lies on the perpendicular bisector of the segment.

This is a fundamental result in Euclidean geometry and is equivalent to the characterization of the perpendicular bisector as the locus of points equidistant from two given points. The result is often used in computational geometry, in the construction of Voronoi diagrams, and in various symmetry arguments.

The theorem provides a simple criterion for identifying isosceles triangles based on perpendicularity and midpoint properties.

### Dependencies
- Theorems:
  - `CONGRUENT_TRIANGLES_SAS`: States that if two triangles have two sides and the included angle equal, then the third sides are equal
  - `BETWEEN_MIDPOINT`: Relates the midpoint property to betweenness
  - `DIST_MIDPOINT`: Relates distances and midpoints
  - `lemma`: (Not provided in dependencies, but appears to establish that orthogonality of $A-B$ and $C-D$ implies angle equality)

### Porting notes
When porting this theorem:
- Ensure your target system has a way to express orthogonality between vectors
- Check that the midpoint concept is defined and has the expected properties
- The proof relies on the SAS triangle congruence criterion, which should be available in most geometric frameworks
- You may need to expand the proof if the `lemma` referenced isn't directly available in your target system

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
For any points $A$, $B$, $C$, and $D$ in $\mathbb{R}^n$, if:
1. The points $D$, $C$, and $A$ are not collinear
2. $D$ is between $A$ and $B$ (meaning $D$ lies on the line segment connecting $A$ and $B$)
3. The angle $\angle ACD = \angle BCD$
4. The vectors $A - B$ and $C - D$ are orthogonal

Then $\text{dist}(A, C) = \text{dist}(B, C)$ (i.e., $C$ is equidistant from $A$ and $B$).

### Informal proof
The proof proceeds by case analysis:

* First, we handle the trivial cases:
  - If $C = D$, then we have a contradiction with the non-collinearity assumption.
  - If $A = B$, the conclusion is immediate.
  
* Next, we analyze the cases where $C$ coincides with either $A$ or $B$:

  - If $C = A$:
    * The angle $\angle ACD$ becomes $\angle ACD = \angle(A,A,D)$, which equals 0 (by the property of the angle measure at the same point).
    * We use `BETWEEN_ANGLE` to analyze $D$ being between $A$ and $B$, which means either $D = A$ or $D = B$ or $\angle(A,D,B) = \pi$.
    * If $D = A$ or $D = B$, we get contradictions with our assumptions.
    * The case where $\angle(A,D,B) = \pi$ leads to a contradiction via `ANGLE_EQ_PI_OTHERS` and the property that $\pi \neq 0$.

  - Similarly, if $C = B$, we reach a contradiction through analogous reasoning.

* For the main case where $C$ is different from $A$, $B$, and $D$:
  * We apply the ASA (Angle-Side-Angle) congruence theorem `CONGRUENT_TRIANGLES_ASA_FULL` to triangles $DCA$ and $DCB$.
  * The congruence conditions are satisfied because:
    - $\angle ACD = \angle BCD$ (given)
    - $\text{dist}(D,C) = \text{dist}(D,C)$ (same side)
    - By the orthogonality of $A-B$ and $C-D$, and using the intermediate lemma, we can establish that $\angle CAD = \angle CBD$.
  * From the congruence of the triangles, we conclude $\text{dist}(A,C) = \text{dist}(B,C)$.

### Mathematical insight
This theorem establishes a condition for when a point $C$ is equidistant from two points $A$ and $B$, making it part of the perpendicular bisector of segment $AB$. The key insight is the combination of:

1. The orthogonality condition between $A-B$ and $C-D$ (where $D$ is on segment $AB$)
2. The equal angles at $C$: $\angle ACD = \angle BCD$

Together, these conditions ensure that $C$ is equidistant from $A$ and $B$, which is a fundamental property in Euclidean geometry related to perpendicular bisectors and the locus of points equidistant from two fixed points.

This result can be useful in computational geometry and for constructive proofs involving isosceles triangles and perpendicular bisectors.

### Dependencies
- `ANGLE_EQ_PI_OTHERS`: If $\angle(A,B,C) = \pi$, then all other angles in the triangle are zero
- `CONGRUENT_TRIANGLES_ASA_FULL`: Angle-Side-Angle congruence theorem for triangles
- `BETWEEN_ANGLE`: Characterization of the "between" relation in terms of angles
- Other basic properties of angles and distances in Euclidean geometry:
  - `ANGLE_REFL`: Angle with repeated points
  - `ANGLE_REFL_MID`: Special case of angle measure with repeated points
  - `ANGLE_SYM`: Symmetry of angle
  - `COLLINEAR_2`: Collinearity of two points
  - `DIST_SYM`: Symmetry of distance

### Porting notes
When porting this theorem:
1. The main challenge will be ensuring that the angle properties and between-ness relations are properly defined in the target system.
2. The orthogonality condition should be translated carefully - some systems might use inner products or dot products instead of an explicit orthogonality relation.
3. The proof relies on triangle congruence theorems (ASA), which should be available in most geometry libraries but might have different formulations.
4. Note that there's a reference to a `lemma` that isn't explicitly defined in the provided dependencies - this might need to be implemented or substituted with an equivalent in the target system.

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
For points $A$, $B$, $C$, and $D$ in $\mathbb{R}^N$, if:
- The points $D$, $C$, and $A$ are not collinear
- $D$ is the midpoint of segment $AB$ (i.e., $D = \text{midpoint}(A,B)$)
- The angle $\angle ACD$ equals the angle $\angle BCD$

Then the distances $\text{dist}(A,C) = \text{dist}(B,C)$, meaning that triangle $ABC$ is isosceles with equal sides $AC$ and $BC$.

### Informal proof
The proof proceeds by considering two main cases arising from how the angles relate:

* First, we apply the Law of Sines to triangles $ACD$ and $BCD$:
  - For $\triangle ACD$: $\frac{\sin(\angle ADC)}{\text{dist}(A,C)} = \frac{\sin(\angle ACD)}{\text{dist}(A,D)}$
  - For $\triangle BCD$: $\frac{\sin(\angle BDC)}{\text{dist}(B,C)} = \frac{\sin(\angle BCD)}{\text{dist}(B,D)}$

* Since $D$ is the midpoint of $AB$, we have $\text{dist}(A,D) = \text{dist}(B,D) = \frac{1}{2}\text{dist}(A,B)$

* Given that $\angle ACD = \angle BCD$ by assumption, we have either:
  1. $\angle ADC = \angle BDC$, or
  2. $\angle ADC = \pi - \angle BDC$

* For case 1 ($\angle ADC = \angle BDC$):
  - We apply the Angle-Angle-Side (AAS) congruence criterion to triangles $\triangle ACD$ and $\triangle BCD$
  - We know that $\angle ACD = \angle BCD$ and $\angle ADC = \angle BDC$
  - The shared side $\text{dist}(C,D)$ is equal in both triangles
  - Therefore, the triangles are congruent, and $\text{dist}(A,C) = \text{dist}(B,C)$

* For case 2 ($\angle ADC = \pi - \angle BDC$):
  - We use the fact that $D$ is the midpoint of $AB$, which means $A$, $D$, and $B$ are collinear with $D$ between $A$ and $B$
  - This implies that $\angle ADB = \pi$ (points are in a straight line)
  - Using properties of angles in triangles and the angle sum theorem, we show that this case leads to a contradiction with our initial assumption that $\{D,C,A\}$ is not collinear

* Therefore, case 1 must hold, and $\text{dist}(A,C) = \text{dist}(B,C)$.

### Mathematical insight
This theorem establishes one of the key characterizations of isosceles triangles: if a point $D$ is the midpoint of a triangle's base $AB$ and the angles at the apex $C$ to this midpoint are equal, then the triangle must be isosceles.

The result captures an important property in Euclidean geometry that connects angle equality to distance equality. It's particularly useful because it provides a way to establish that a triangle is isosceles without directly measuring its sides, but by examining angle relationships involving the midpoint of one side.

This theorem is part of a broader collection of results about isosceles triangles, where various equivalent conditions can be used to characterize when two sides of a triangle are equal.

### Dependencies
- **Theorems**:
  - `SIN_ANGLE_EQ`: Relates equality of sines of angles to the angles themselves
  - `COLLINEAR_ANGLE`: Characterizes collinearity in terms of angles
  - `ANGLE_EQ_0_LEFT`: Property of zero angles
  - `ANGLE_EQ_PI_OTHERS`: Properties of angles in a triangle when one angle equals π
  - `CONGRUENT_TRIANGLES_AAS`: Angle-Angle-Side triangle congruence criterion
  - `BETWEEN_ANGLE`: Relationship between the "between" relation and angles
  - `LAW_OF_SINES`: The Law of Sines for triangles
  - `TRIANGLE_ANGLE_SUM`: Sum of angles in a triangle equals π
  - `BETWEEN_MIDPOINT`: Properties of midpoints related to the "between" relation

### Porting notes
When porting this theorem:
1. Make sure the definition of `midpoint` is consistent - in HOL Light it's defined as `midpoint(A,B) = (A + B) / 2`
2. The proof heavily uses angle properties and triangle congruence theorems, so ensure these fundamental results are available in the target system
3. The Law of Sines plays a critical role, so verify its formulation in the target system
4. Pay attention to how angles are defined in the target system - HOL Light uses the standard definition where angles are measured in radians and lie between 0 and π

---

