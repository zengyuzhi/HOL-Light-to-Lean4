# ceva.ml

## Overview

Number of statements: 7

The `ceva.ml` file formalizes Ceva's theorem, a geometric concept. It builds upon definitions and results imported from `convex.ml` and `sos.ml`, suggesting a connection to convexity and possibly semidefinite optimization. The file's primary purpose is to provide a formal proof of Ceva's theorem within the HOL Light system. Its content is likely to include definitions, lemmas, and theorems related to this geometric concept.

## BETWEEN_THM

### Name of formal statement
BETWEEN_THM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BETWEEN_THM = prove
 (`between x (a,b) <=>
       ?u. &0 <= u /\ u <= &1 /\ x = u % a + (&1 - u) % b`,
  REWRITE_TAC[BETWEEN_IN_CONVEX_HULL] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b} = {b,a}`] THEN
  REWRITE_TAC[CONVEX_HULL_2_ALT; IN_ELIM_THM] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  AP_TERM_TAC THEN VECTOR_ARITH_TAC)
```

### Informal statement
The theorem `BETWEEN_THM` states that a point `x` is between points `a` and `b` if and only if there exists a real number `u` such that `0 ≤ u ≤ 1` and `x` can be expressed as the convex combination of `a` and `b` with `u` as the coefficient for `a` and `1 - u` as the coefficient for `b`.

### Informal sketch
* The proof starts by applying the `BETWEEN_IN_CONVEX_HULL` rule to rewrite the `between` relation in terms of convex hulls.
* It then uses `SET_RULE` to reorder the points `a` and `b`, allowing for symmetry in the definition.
* The `CONVEX_HULL_2_ALT` and `IN_ELIM_THM` rules are applied to further transform the expression into a form involving convex combinations.
* The proof involves applying `AP_TERM_TAC` and `ABS_TAC` to manipulate the terms and `REWRITE_TAC[CONJ_ASSOC]` to rearrange conjunctions, ultimately leading to a form where `VECTOR_ARITH_TAC` can be applied to conclude the proof.

### Mathematical insight
This theorem provides an alternative characterization of the `between` relation in terms of convex combinations, which is a fundamental concept in geometry and linear algebra. The `BETWEEN_THM` theorem is important because it connects the geometric notion of a point being between two others with algebraic expressions involving linear combinations, facilitating proofs and calculations in geometric contexts.

### Dependencies
* `BETWEEN_IN_CONVEX_HULL`
* `SET_RULE`
* `CONVEX_HULL_2_ALT`
* `IN_ELIM_THM`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to how each system handles convex combinations and the `between` relation, as these may be defined or axiomatized differently. Additionally, the tactic script may need to be adapted to the target system's proof automation and term manipulation capabilities, potentially requiring manual intervention to guide the proof search or term rewriting.

---

## NORM_CROSS

### Name of formal statement
NORM_CROSS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NORM_CROSS = prove
 (`norm(a) * norm(b) * norm(c) = norm(d) * norm(e) * norm(f) <=>
   (a dot a) * (b dot b) * (c dot c) = (d dot d) * (e dot e) * (f dot f)`,
  let lemma = prove
   (`!x y. &0 <= x /\ &0 <= y ==> (x pow 2 = y pow 2 <=> x = y)`,
    REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[REAL_POW_2] THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [`x:real`; `y:real`] REAL_LT_TOTAL) THEN
    ASM_MESON_TAC[REAL_LT_MUL2; REAL_LT_REFL]) in
  REWRITE_TAC[GSYM NORM_POW_2; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC(GSYM lemma) THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL])
```

### Informal statement
The theorem `NORM_CROSS` states that for any vectors `a`, `b`, `c`, `d`, `e`, and `f`, the following equivalence holds: the product of the norms of `a`, `b`, and `c` is equal to the product of the norms of `d`, `e`, and `f` if and only if the product of the dot products of each vector with itself (i.e., the square of the magnitudes) for `a`, `b`, and `c` is equal to the product of the dot products of each vector with itself for `d`, `e`, and `f`. This is proven under the condition that a helper lemma is established, which states that for any non-negative real numbers `x` and `y`, `x` squared equals `y` squared if and only if `x` equals `y`.

### Informal sketch
* The proof starts by establishing a lemma that for non-negative real numbers `x` and `y`, `x` squared equals `y` squared if and only if `x` equals `y`. This involves using `REAL_POW_2` and `REAL_LT_TOTAL` to handle cases where `x` or `y` could be zero or positive, leveraging `REAL_LT_MUL2` and `REAL_LT_REFL` for comparisons.
* The main theorem `NORM_CROSS` is then proven by rewriting the expressions involving norms using `GSYM NORM_POW_2` and `GSYM REAL_POW_MUL`, which relates norms and dot products.
* The proof applies the previously established lemma to show the equivalence between the products of norms and the products of squared magnitudes, using `MATCH_MP_TAC` with the lemma and simplifying with `NORM_POS_LE` and `REAL_LE_MUL`.

### Mathematical insight
This theorem provides a relationship between the norms (magnitudes) of vectors and their dot products with themselves, essentially showing that under certain conditions, equality in the product of norms implies equality in the product of squared magnitudes, and vice versa. This is built on the principle that for non-negative numbers, equality of squares implies equality of the numbers themselves, which is a fundamental property used to bridge between different representations of vector properties.

### Dependencies
- `REAL_POW_2`
- `REAL_LT_TOTAL`
- `REAL_LT_MUL2`
- `REAL_LT_REFL`
- `NORM_POW_2`
- `NORM_POS_LE`
- `REAL_LE_MUL`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to how each system handles non-negative real numbers, vector norms, and dot products. The `REAL_POW_2` and similar theorems might need to be restated or proved in the target system, and the automation tactics like `REPEAT STRIP_TAC`, `EQ_TAC`, and `SIMP_TAC` might have analogous but differently named tactics in other systems. Additionally, the use of `MATCH_MP_TAC` with a previously proved lemma suggests that the target system should support a similar mechanism for applying previously established results to current goals.

---

## COLLINEAR

### Name of formal statement
COLLINEAR

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COLLINEAR = prove
 (`!a b c:real^2.
        collinear {a:real^2,b,c} <=>
        ((a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1))`,
  let lemma = prove
   (`~(y1 = &0) /\ x2 * y1 = x1 * y2 ==> ?c. x1 = c * y1 /\ x2 = c * y2`,
    STRIP_TAC THEN EXISTS_TAC `x1 / y1` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^2 = b` THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
    REWRITE_TAC[COLLINEAR_SING; COLLINEAR_2; INSERT_AC];
    ALL_TAC] THEN
  REWRITE_TAC[collinear] THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (fun th ->
        MP_TAC(SPECL [`a:real^2`; `b:real^2`] th) THEN
        MP_TAC(SPECL [`b:real^2`; `c:real^2`] th))) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH] THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `a - b:real^2` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; ARITH; DE_MORGAN_THM] THEN STRIP_TAC THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_MUL_COMPONENT;
           VECTOR_SUB_COMPONENT; ARITH]
  THENL [ALL_TAC; ONCE_REWRITE_TAC[CONJ_SYM]] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN(REPEAT_TCL STRIP_THM_THEN SUBST1_TAC)) THEN
  MATCH_MP_TAC lemma THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD)
```

### Informal statement
The theorem `COLLINEAR` states that for any three points `a`, `b`, and `c` in the 2-dimensional real space, the set `{a, b, c}` is collinear if and only if the cross product of the vectors `a - b` and `b - c` is zero, which is equivalent to the condition `(a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1)`. This condition essentially checks if the slopes between pairs of points are equal, indicating they lie on the same line.

### Informal sketch
* The proof starts by considering the case when `a = b`. In this scenario, it simplifies the condition using properties of real numbers and the definition of `collinear`.
* For `a ≠ b`, it employs the `collinear` definition and uses `EQ_TAC` to split the proof into two directions: 
  + The forward direction involves choosing a point `th` and applying it to both `a` and `b`, and then to `b` and `c`, to derive the relationship between the points.
  + The backward direction involves assuming the condition `(a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1)` holds and proving that `{a, b, c}` is collinear by showing there exists a vector `a - b` such that `a`, `b`, and `c` are related by this vector.
* The proof uses various tactics such as `REAL_ARITH_TAC` for arithmetic manipulations, `ASM_SIMP_TAC` and `SIMP_TAC` for simplifications, and `MATCH_MP_TAC lemma` to apply a previously proven lemma about the existence of a scalar `c` such that `x1 = c * y1` and `x2 = c * y2` given certain conditions.

### Mathematical insight
The `COLLINEAR` theorem provides a necessary and sufficient condition for three points to be collinear in a 2D real space. It's based on the geometric intuition that three points are on the same line if the slope between any two pairs of points is the same. This theorem is crucial in geometry and has applications in various fields such as computer graphics, robotics, and geographic information systems.

### Dependencies
- `COLLINEAR_SING`
- `COLLINEAR_2`
- `INSERT_AC`
- `REAL_SUB_REFL`
- `REAL_MUL_RZERO`
- `REAL_MUL_LZERO`
- `VECTOR_SUB_COMPONENT`
- `VECTOR_MUL_COMPONENT`
- `CART_EQ`
- `DIMINDEX_2`
- `FORALL_2`
- `DE_MORGAN_THM`
- `REAL_FIELD`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles real numbers, vectors, and geometric concepts. The use of `REAL_ARITH_TAC` and `CONV_TAC REAL_FIELD` suggests that HOL Light's handling of real arithmetic might need special care, potentially requiring the use of specific libraries or tactics in the target system. Additionally, the `MATCH_MP_TAC lemma` application indicates a dependency on a specific lemma that might need to be ported or proven anew in the target system.

---

## CEVA_WEAK

### Name of formal statement
CEVA_WEAK

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CEVA_WEAK = prove
 (`!A B C X Y Z P:real^2.
        ~(collinear {A,B,C}) /\
        between X (B,C) /\ between Y (A,C) /\ between Z (A,B) /\
        between P (A,X) /\ between P (B,Y) /\ between P (C,Z)
        ==> dist(B,X) * dist(C,Y) * dist(A,Z) =
            dist(X,C) * dist(Y,A) * dist(Z,B)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[dist; NORM_CROSS; COLLINEAR; BETWEEN_THM] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN
  SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; VECTOR_ADD_COMPONENT;
           CART_EQ; FORALL_2; VECTOR_MUL_COMPONENT; ARITH] THEN
  FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
  CONV_TAC REAL_RING)
```

### Informal statement
For all points A, B, C, X, Y, Z, and P in the 2-dimensional real space, if A, B, and C are not collinear, and X lies between B and C, Y lies between A and C, Z lies between A and B, and P lies between A and X, B and Y, and C and Z, then the product of the distances from B to X, C to Y, and A to Z is equal to the product of the distances from X to C, Y to A, and Z to B.

### Informal sketch
* Start by assuming the conditions: A, B, and C are not `collinear`, and the `between` conditions for X, Y, Z, and P are met.
* Apply `REWRITE_TAC` to expand definitions of `dist`, `NORM_CROSS`, `COLLINEAR`, and `BETWEEN_THM`.
* Use `STRIP_TAC` to remove the implication, and then apply `SUBST_ALL_TAC` and `MP_TAC` with `SYM` to manipulate the assumptions and conclusions.
* Simplify using `SIMP_TAC` with various theorems and definitions, including `dot`, `SUM_2`, `VECTOR_SUB_COMPONENT`, `DIMINDEX_2`, `VECTOR_ADD_COMPONENT`, `CART_EQ`, `FORALL_2`, `VECTOR_MUL_COMPONENT`, and `ARITH`.
* Apply `CONV_TAC REAL_RING` to finalize the proof.

### Mathematical insight
This theorem, CEVA_WEAK, relates to geometric properties of points in 2-dimensional space, specifically addressing the relationship between distances of points under certain conditions. The theorem's importance lies in its application to geometric reasoning and its potential use in proving other geometric theorems.

### Dependencies
* Theorems:
  + `dist`
  + `NORM_CROSS`
  + `COLLINEAR`
  + `BETWEEN_THM`
  + `dot`
  + `SUM_2`
  + `VECTOR_SUB_COMPONENT`
  + `DIMINDEX_2`
  + `VECTOR_ADD_COMPONENT`
  + `CART_EQ`
  + `FORALL_2`
  + `VECTOR_MUL_COMPONENT`
  + `ARITH`
* Definitions:
  + `real^2` (2-dimensional real space)
  + `between` (point between two other points)
  + `collinear` (points lying on the same line)

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of geometric definitions and theorems, such as `dist`, `collinear`, and `between`. Additionally, the use of `REAL_RING` in the final step may require careful consideration of how the target system handles real numbers and arithmetic. The `REPEAT` and `FIRST_X_ASSUM` tactics may also need to be adapted to the target system's tactical language.

---

## CEVA

### Name of formal statement
CEVA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CEVA = prove
 (`!A B C X Y Z:real^2.
        ~(collinear {A,B,C}) /\
        between X (B,C) /\ between Y (C,A) /\ between Z (A,B)
        ==> (dist(B,X) * dist(C,Y) * dist(A,Z) =
             dist(X,C) * dist(Y,A) * dist(Z,B) <=>
             (?P. between P (A,X) /\ between P (B,Y) /\ between P (C,Z)))`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`A:real^2 = B`; `A:real^2 = C`; `B:real^2 = C`] THEN
  ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SING; COLLINEAR_2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[BETWEEN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x:real`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `y:real`)
    (X_CHOOSE_TAC `z:real`)) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC)) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN REWRITE_TAC[dist] THEN
  REWRITE_TAC[VECTOR_ARITH `B - (x % B + (&1 - x) % C) = (&1 - x) % (B - C)`;
              VECTOR_ARITH `(x % B + (&1 - x) % C) - C = x % (B - C)`] THEN
  REWRITE_TAC[NORM_MUL] THEN
  REWRITE_TAC[REAL_ARITH `(a * a') * (b * b') * (c * c') =
                          (a * b * c) * (a' * b' * c')`] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; REAL_EQ_MUL_RCANCEL; REAL_ENTIRE] THEN
  ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ] THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 <= &1 - x <=> x <= &1`; real_abs] THEN
  EQ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [COLLINEAR]) THEN
    SIMP_TAC[dot; SUM_2; VECTOR_SUB_COMPONENT; DIMINDEX_2; FORALL_2;
            VECTOR_ADD_COMPONENT; CART_EQ; VECTOR_MUL_COMPONENT; ARITH] THEN
    CONV_TAC REAL_RING] THEN
  DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  SUBGOAL_THEN
   `?u v w. w = (&1 - u) * (&1 - x) /\
            v = (&1 - u) * x /\
            u = (&1 - v) * (&1 - y) /\
            u = (&1 - w) * z /\
            v = (&1 - w) * (&1 - z) /\
            w = (&1 - v) * y /\
            &0 <= u /\ u <= &1 /\ &0 <= v /\ v <= &1 /\ &0 <= w /\ w <= &1`
  (STRIP_ASSUME_TAC o GSYM) THENL
   [ALL_TAC;
    EXISTS_TAC `u % A + v % B + w % C:real^2` THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `u:real`; EXISTS_TAC `v:real`; EXISTS_TAC `w:real`] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC] THEN
  REWRITE_TAC[UNWIND_THM2] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. p x /\ q x ==> r x) /\ (?x. p x /\ q x)
    ==> (?x. p x /\ q x /\ r x)`) THEN
  CONJ_TAC THENL
   [GEN_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_neg o concl))) THEN
    REWRITE_TAC[IMP_IMP] THEN
    REPEAT(MATCH_MP_TAC(TAUT `(a ==> b /\ c) /\ (a /\ b /\ c ==> d)
                              ==> a ==> b /\ c /\ d`) THEN
           CONJ_TAC THENL
            [CONV_TAC REAL_RING ORELSE CONV_TAC REAL_SOS; ALL_TAC]) THEN
    CONV_TAC REAL_SOS;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR]) THEN
  ASM_CASES_TAC `x = &0` THENL
   [EXISTS_TAC `&1 - y / (&1 - x + x * y)` THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_neg o concl))) THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  EXISTS_TAC `&1 - (&1 - z) / (x + (&1 - x) * (&1 - z))` THEN
  SUBGOAL_THEN `~(x + (&1 - x) * (&1 - z) = &0)` MP_TAC THENL
   [ALL_TAC;
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_neg o concl))) THEN
    CONV_TAC REAL_FIELD] THEN
  MATCH_MP_TAC(REAL_ARITH
   `z * (&1 - x) < &1 ==> ~(x + (&1 - x) * (&1 - z) = &0)`) THEN
  ASM_CASES_TAC `z = &0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LT_01] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * (&1 - x)` THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; REAL_ARITH `x <= &1 ==> &0 <= &1 - x`] THEN
  ASM_REAL_ARITH_TAC)
```

### Informal statement
For all points `A`, `B`, `C`, `X`, `Y`, `Z` in `real^2`, if `A`, `B`, and `C` are not collinear and `X` lies between `B` and `C`, `Y` lies between `C` and `A`, and `Z` lies between `A` and `B`, then the following equivalence holds: the product of the distances from `B` to `X`, `C` to `Y`, and `A` to `Z` equals the product of the distances from `X` to `C`, `Y` to `A`, and `Z` to `B` if and only if there exists a point `P` that lies between `A` and `X`, between `B` and `Y`, and between `C` and `Z`.

### Informal sketch
* The proof starts by assuming the non-collinearity of points `A`, `B`, and `C`, and the betweenness conditions for `X`, `Y`, and `Z`.
* It then proceeds to analyze the given equivalence, leveraging various properties and theorems such as `COLLINEAR`, `BETWEEN_THM`, and `VECTOR_ARITH`.
* Key steps involve choosing real numbers `x`, `y`, and `z` and using them to express distances and apply vector arithmetic.
* The proof also involves assuming and deriving the existence of real numbers `u`, `v`, and `w` that satisfy specific conditions related to the betweenness of points.
* The `MATCH_MP_TAC` and `CONJ_TAC` tactics are used to manage the logical structure of the proof, applying rules and combining conclusions.
* The use of `REAL_ARITH`, `VECTOR_ADD_LDISTRIB`, and `VECTOR_MUL_ASSOC` indicates the manipulation of real numbers and vectors according to their respective axioms and properties.
* The proof concludes by establishing the desired equivalence through a combination of these steps and the application of specific theorems like `UNWIND_THM2` and `REAL_LET_TRANS`.

### Mathematical insight
This theorem provides insight into the geometric and algebraic relationship between points and distances in a two-dimensional real space, highlighting the conditions under which a specific equivalence involving distances and betweenness holds. It is likely used in more complex geometric or topological proofs, relying on the non-collinearity of points and the properties of real numbers and vectors.

### Dependencies
* Theorems:
  + `COLLINEAR`
  + `BETWEEN_THM`
  + `UNWIND_THM2`
  + `REAL_LET_TRANS`
* Definitions:
  + `dist`
  + `between`
  + `collinear`
* Axioms and Properties:
  + `VECTOR_ARITH`
  + `REAL_ARITH`
  + `VECTOR_ADD_LDISTRIB`
  + `VECTOR_MUL_ASSOC`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to the handling of real numbers, vectors, and the specific tactics used, as these may differ significantly between systems. The use of `MATCH_MP_TAC`, `CONJ_TAC`, and other tactics may need to be adapted to the target system's tactic language. Additionally, ensure that the necessary theorems and definitions are available or can be readily translated in the target system.

---

## BETWEEN_SYM

### Name of formal statement
BETWEEN_SYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BETWEEN_SYM = prove
 (`!u v w. between v (u,w) <=> between v (w,u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETWEEN_THM] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN EXISTS_TAC `&1 - u` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY VECTOR_ARITH_TAC THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)
```

### Informal statement
For all real numbers $u$, $v$, and $w$, $v$ is between $u$ and $w$ if and only if $v$ is between $w$ and $u$.

### Informal sketch
* The proof starts by assuming the statement to be proven, `!u v w. between v (u,w) <=> between v (w,u)`.
* It then applies `GEN_TAC` to generalize the variables, followed by `REWRITE_TAC` with `BETWEEN_THM` to rewrite the `between` relation.
* The proof proceeds with `EQ_TAC` to split the equivalence into two implications, and then uses `DISCH_THEN` with `X_CHOOSE_TAC` to introduce an existential quantifier.
* The `EXISTS_TAC` tactic is used to introduce a witness, and `ASM_REWRITE_TAC` is applied to simplify the resulting expression.
* The proof then uses `REPEAT CONJ_TAC` to split conjunctions and `TRY VECTOR_ARITH_TAC` to perform vector arithmetic.
* Finally, `POP_ASSUM MP_TAC` and `REAL_ARITH_TAC` are used to discharge assumptions and perform real arithmetic.

### Mathematical insight
This theorem establishes the symmetry of the `between` relation, which is a fundamental property in geometry and real analysis. The `between` relation is often used to define intervals and segments, and this symmetry property ensures that the order of the endpoints does not affect the definition.

### Dependencies
* `BETWEEN_THM`: a theorem that defines or characterizes the `between` relation.
* `REAL_ARITH_TAC`: a tactic for performing real arithmetic.
* `VECTOR_ARITH_TAC`: a tactic for performing vector arithmetic.

### Porting notes
When porting this theorem to another proof assistant, note that the `between` relation and the `BETWEEN_THM` theorem may need to be defined or imported separately. Additionally, the `REAL_ARITH_TAC` and `VECTOR_ARITH_TAC` tactics may have different names or behaviors in other systems, and may require additional setup or configuration to work correctly.

---

## BETWEEN_METRICAL

### Name of formal statement
BETWEEN_METRICAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let BETWEEN_METRICAL = prove
 (`!u v w:real^N. between v (u,w) <=> dist(u,v) + dist(v,w) = dist(u,w)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[BETWEEN_SYM] THEN REWRITE_TAC[BETWEEN_THM; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `x % u + (&1 - x) % v = v + x % (u - v)`] THEN
  SUBST1_TAC(VECTOR_ARITH `u - w:real^N = (u - v) + (v - w)`) THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN REWRITE_TAC[NORM_TRIANGLE_EQ] THEN
  EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `u - (u + x):real^N = --x`; NORM_NEG;
                VECTOR_ARITH `(u + c % (w - u)) - w = (&1 - c) % (u - w)`] THEN
    REWRITE_TAC[VECTOR_ARITH `a % --(c % (x - y)) = (a * c) % (y - x)`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `c <= &1 ==> abs(&1 - c) = &1 - c`;
                 REAL_ARITH `&0 <= c ==> abs c = c`] THEN
    REWRITE_TAC[NORM_SUB; REAL_MUL_AC]] THEN
  DISCH_TAC THEN ASM_CASES_TAC `&0 < norm(u - v:real^N) + norm(v - w)` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `~(&0 < x + y) ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0`)) THEN
    REWRITE_TAC[NORM_POS_LE; NORM_EQ_0; VECTOR_SUB_EQ] THEN
    STRIP_TAC THEN EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_POS] THEN
    VECTOR_ARITH_TAC] THEN
  EXISTS_TAC `norm(u - v:real^N) / (norm(u - v) + norm(v - w))` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO;
               REAL_MUL_LID; REAL_LE_ADDR; NORM_POS_LE] THEN
  MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
  EXISTS_TAC `norm(u - v:real^N) + norm(v - w)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `x % (y + z % v) = x % y + (x * z) % v`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_DIV_LMUL] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN VECTOR_ARITH_TAC)
```

### Informal statement
For all vectors `u`, `v`, and `w` in `real^N`, `v` is between `u` and `w` if and only if the distance from `u` to `v` plus the distance from `v` to `w` equals the distance from `u` to `w`.

### Informal sketch
* The proof starts by assuming `v` is between `u` and `w`, and then uses the `BETWEEN_SYM` and `BETWEEN_THM` theorems to simplify the expression for the distance between `u` and `w`.
* It then applies vector arithmetic properties to express `u - w` as `(u - v) + (v - w)`, and uses the `NORM_TRIANGLE_EQ` theorem to relate the norms of these vectors.
* The proof then proceeds by cases, considering whether `&0 < norm(u - v) + norm(v - w)`.
* In the case where `&0 < norm(u - v) + norm(v - w)`, it constructs a specific value `c` such that `v` can be expressed as `u + c % (w - u)`, and uses properties of vector arithmetic and norm to show that `dist(u, v) + dist(v, w) = dist(u, w)`.
* In the case where `~(&0 < norm(u - v) + norm(v - w))`, it uses real arithmetic properties to show that `norm(u - v) = 0` and `norm(v - w) = 0`, and thus `u = v` and `v = w`.
* The proof uses various tactics, including `CONV_TAC`, `REWRITE_TAC`, `SUBST1_TAC`, and `ASM_SIMP_TAC`, to simplify and manipulate the expressions involved.

### Mathematical insight
This theorem provides a characterization of the `between` relation in terms of distances between vectors. It shows that `v` is between `u` and `w` if and only if the distance from `u` to `v` plus the distance from `v` to `w` equals the distance from `u` to `w`. This is a fundamental property of the `between` relation, and is useful in a variety of geometric and analytical contexts.

### Dependencies
* Theorems:
	+ `BETWEEN_SYM`
	+ `BETWEEN_THM`
	+ `NORM_TRIANGLE_EQ`
	+ `VECTOR_MUL_LCANCEL_IMP`
	+ `REAL_ARITH`
* Definitions:
	+ `between`
	+ `dist`
	+ `norm`
* Axioms:
	+ `VECTOR_ARITH`
	+ `REAL_ARITH`

---

