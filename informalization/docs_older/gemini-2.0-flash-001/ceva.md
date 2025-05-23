# ceva.ml

## Overview

Number of statements: 7

`ceva.ml` formalizes Ceva's theorem, a fundamental result in plane geometry concerning the concurrency of cevians in a triangle. The file likely relies on convex geometry and sums-of-squares results from imported files to prove Ceva's theorem within the HOL Light system. This theorem is part of a larger collection of formalized mathematical results.


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
For any real vector `x` and any two real vectors `a` and `b`, `x` is `between` `a` and `b` if and only if there exists a real number `u` such that `0 <= u`, `u <= 1` and `x = u * a + (1 - u) * b`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting using the definition `BETWEEN_IN_CONVEX_HULL`. This likely expresses `between x (a, b)` in terms of `convex_hull {a,b}`.
- Rewrite using the set rule `{a,b} = {b,a}` to handle the unordered nature of the set.
- Rewrite `convex_hull {a,b}` using an alternative formulation `CONVEX_HULL_2_ALT` involving the existence of a `u` in the interval `[0,1]` and eliminate the `in` predicate with `IN_ELIM_THM`.
- Apply `AP_TERM_TAC` and `ABS_TAC` to prepare the terms for arithmetic simplification.
- Rewrite using associativity of conjunction `CONJ_ASSOC`.
- Apply `AP_TERM_TAC` again.
- Finally, apply a vector arithmetic tactic `VECTOR_ARITH_TAC` to complete the proof.

### Mathematical insight
This theorem provides an alternative characterization of the `between` relation for vectors. It states that a point `x` is between two points `a` and `b` if and only if it can be expressed as a convex combination of `a` and `b`. This is a fundamental concept in convex geometry.

### Dependencies
- Definitions:
  - `between`
  - `CONVEX_HULL_2_ALT`

- Theorems:
  - `BETWEEN_IN_CONVEX_HULL`
  - `SET_RULE `{a,b} = {b,a}`
  - `IN_ELIM_THM`
  - `CONJ_ASSOC`

### Porting notes
The main challenge in porting this theorem will be to ensure that the definitions of `between` and `convex_hull` are consistent, and that the vector arithmetic tactic `VECTOR_ARITH_TAC` has a corresponding automated procedure in the target proof assistant. You may need to manually expand `VECTOR_ARITH_TAC` into individual rewriting steps using arithmetic lemmas.
The `SET_RULE` might be named differently or directly embedded in other tactics.


---

## NORM_CROSS

### Name of formal statement
NORM_CROSS

### Type of the formal statement
theorem

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
  MATCH_MP_TAC(GSYM lemma) THEN SIMP_TAC[NORM_POS_LE; REAL_LE_MUL]);;
```

### Informal statement
The product of the norms of `a`, `b`, and `c` is equal to the product of the norms of `d`, `e`, and `f` if and only if the product of the squared norms of `a`, `b`, and `c` is equal to the product of the squared norms of `d`, `e`, and `f`. Here, `a`, `b`, `c`, `d`, `e`, and `f` are vectors.

### Informal sketch
The proof proceeds as follows:
- First, establishes a lemma: For any non-negative real numbers x and y, x squared equals y squared if and only if x equals y. The proof of this lemma involves stripping quantifiers and implications, simplifying using the definition of `REAL_POW_2`, considering cases based on the total order of real numbers (`REAL_LT_TOTAL`), and using assumptions with `ASM_MESON_TAC` along with `REAL_LT_MUL2` and `REAL_LT_REFL`.
- Then, the theorem uses the previously proven lemma. It begins by rewriting the original goal using the reversed versions of `NORM_POW_2` (norm(x)^2 = x dot x) and `REAL_POW_MUL` (x^2 * y^2 = (x*y)^2).
- `MATCH_MP_TAC` applies the lemma, reducing the problem to showing that the products of the norms are non-negative, which follows from the subsequent simplification.
- Finally, it simplifies using `NORM_POS_LE` (norms are non-negative) and `REAL_LE_MUL` which states that the product of non-negative numbers is non-negative.

### Mathematical insight
This theorem provides a practical way to relate the equality of products of norms to the equality of products of squared norms. Because norms are non-negative, squaring effectively removes the square root in the original norm definition, often making calculation easier in formal settings.

### Dependencies
- `NORM_POW_2`: Relates the square of the norm to the dot product.
- `REAL_POW_MUL`: Relates the product of squares to the square of the product.
- `NORM_POS_LE`: States that the norm is non-negative.
- `REAL_LE_MUL`: Deals with multiplication of non-negative real numbers.
- `REAL_LT_TOTAL`: Law of trichotomy for real numbers.
- `REAL_LT_MUL2`: Properties of multiplication with inequalities.
- `REAL_LT_REFL`: Reflexivity of less than relation.
- `REAL_POW_2`: Definition of squaring.

### Porting notes (optional)
The key is that norms are non-negative, so squaring them preserves equality. The proof relies on basic real number properties, which should be available in most proof assistants.


---

## COLLINEAR

### Name of formal statement
COLLINEAR

### Type of the formal statement
theorem

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
  MATCH_MP_TAC lemma THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;
```

### Informal statement
For all real vectors `a`, `b`, and `c` in a 2-dimensional space, the set `{a, b, c}` is collinear if and only if `(a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1)`.

### Informal sketch
The proof proceeds as follows:
- First, a lemma is proven: If `~(y1 = &0) /\ x2 * y1 = x1 * y2`, then there exists `c` such that `x1 = c * y1 /\ x2 = c * y2`. This is proved by choosing `x1 / y1` for `c` and using real field arithmetic.
- The main proof starts by assuming the universally quantified vectors `a`, `b`, and `c`.
- Case split based on whether `a = b`.
  - If `a = b`, then use the theorems `COLLINEAR_SING`, `COLLINEAR_2` and `INSERT_AC` to show that `{a,b,c}` is collinear.
  - Otherwise, assume `~(a = b)`.
- Expand the definition of `collinear`.
- Split the equivalence into two implications.
  - For the first implication, assume `collinear {a, b, c}` and prove `(a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1)`.
    - Instantiate an existential quantifier and simplify using vector component subtraction, multiplication, and arithmetic facts.
    - Use `REAL_ARITH_TAC` to close the goal.
  - For the second implication, assume `(a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1)` and prove `collinear {a, b, c}`.
    - Introduce an existential variable `a - b:real^2`.
    - Expand definitions, rewrite with cartesian equality, and simplify.
    - Apply the proven lemma based on the hypothesis.
    - Use real field arithmetic to finish.

### Mathematical insight
This theorem provides an algebraic criterion to determine if three points (represented as 2D real vectors) are collinear. The condition `(a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1)` is equivalent to saying that the vectors `a - b` and `b - c` are parallel, which is a standard test for collinearity.

### Dependencies
- `COLLINEAR_SING`
- `COLLINEAR_2`
- `INSERT_AC`
- `collinear`
- `VECTOR_SUB_COMPONENT`
- `DIMINDEX_2`
- `ARITH`
- `VECTOR_MUL_COMPONENT`
- `CART_EQ`
- `FORALL_2`
- `DE_MORGAN_THM`



---

## CEVA_WEAK

### Name of formal statement
CEVA_WEAK

### Type of the formal statement
theorem

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
  CONV_TAC REAL_RING);;
```

### Informal statement
For all points `A`, `B`, `C`, `X`, `Y`, `Z`, and `P` in the real plane, if `A`, `B`, and `C` are not collinear, `X` lies between `B` and `C`, `Y` lies between `A` and `C`, `Z` lies between `A` and `B`, `P` lies between `A` and `X`, `P` lies between `B` and `Y`, and `P` lies between `C` and `Z`, then `dist(B,X) * dist(C,Y) * dist(A,Z) = dist(X,C) * dist(Y,A) * dist(Z,B)`.

### Informal sketch
The proof uses a series of rewrites and simplification steps.
- The initial goal is to prove Ceva's theorem under the 'between' condition.
- First, rewrite the goal using definitions of `dist`, `NORM_CROSS`, `COLLINEAR`, and `BETWEEN_THM`. This expresses the condition in terms of vector arithmetic.
- Then, repeatedly substitute assumptions based on variable names in the conclusion.
- Subsequently, repeatedly apply modus ponens using symmetrically transformed assumptions.
- Simplify the expression using vector arithmetic properties such as `dot`, `SUM_2`, `VECTOR_SUB_COMPONENT`, `DIMINDEX_2`, `VECTOR_ADD_COMPONENT`, `CART_EQ`, `FORALL_2`, `VECTOR_MUL_COMPONENT`, and `ARITH`.
- Use modus ponens with the negation of the conclusion.
- Finally, apply real ring tactics `REAL_RING` to complete the proof by showing that the resulting expression simplifies to true under the laws of real arithmetic.

### Mathematical insight
This theorem provides a specific case of Ceva's Theorem. Ceva's Theorem relates the ratios in which the sides of a triangle are divided by concurrent cevians. This weak form of the theorem focuses on the case where the point of concurrency lies within the triangle and relies heavily on the `between` relation existing between points.

### Dependencies
- `dist`
- `NORM_CROSS`
- `COLLINEAR`
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


---

## CEVA

### Name of formal statement
CEVA

### Type of the formal statement
theorem

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
  ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any four points `A`, `B`, `C`, `X`, `Y`, `Z` in the real plane, if `A`, `B`, and `C` are not collinear and `X` lies between `B` and `C`, `Y` lies between `C` and `A`, and `Z` lies between `A` and `B`, then the following holds: the product of the distances from `B` to `X`, `C` to `Y`, and `A` to `Z` is equal to the product of the distances from `X` to `C`, `Y` to `A`, and `Z` to `B` if and only if there exists a point `P` such that `P` lies between `A` and `X`, `P` lies between `B` and `Y`, and `P` lies between `C` and `Z`.

### Informal sketch
The proof proceeds as follows:
- Assume `A`, `B`, `C` are not collinear, `X` is between `B` and `C`, `Y` is between `C` and `A`, `Z` is between `A` and `B`.
- Express `X`, `Y`, `Z` as convex combinations of `B` and `C`, `C` and `A`, and `A` and `B` respectively.
- Rewrite distance in terms of norms.
- Simplify the equation involving distances to an equation involving `x`, `y`, `z` which are coefficients in the convex combinations.
- The existence of `P` between `A` and `X`, `B` and `Y`, `C` and `Z` is equivalent to the existence of real numbers `u`, `v`, `w` between 0 and 1 satisfying equations relating them to `x`, `y`, `z`.
- Show the equivalence between the simplified equation and the existence of the `u`, `v`, `w` using real arithmetic.
- `COLLINEAR` is used to resolve goals related to collinearity.
- Case split on `x = &0`, applying field and arithmetic tactics on real numbers.

### Mathematical insight
Ceva's Theorem provides a necessary and sufficient condition for the concurrency of three cevians of a triangle. A cevian is a line segment that joins a vertex of a triangle to a point on the opposite side. The theorem is a fundamental result in Euclidean geometry and has applications in various geometric constructions and problems.

### Dependencies
- `INSERT_AC` (likely related to associativity and commutativity)
- `COLLINEAR_SING`
- `COLLINEAR_2`
- `BETWEEN_THM`
- `dist`
- `VECTOR_ARITH`
- `NORM_MUL`
- `REAL_ARITH`
- `REAL_MUL_ASSOC`
- `REAL_EQ_MUL_RCANCEL`
- `REAL_ENTIRE`
- `NORM_EQ_0`
- `VECTOR_SUB_EQ`
- `real_abs`
- `COLLINEAR`
- `dot`
- `SUM_2`
- `VECTOR_SUB_COMPONENT`
- `DIMINDEX_2`
- `FORALL_2`
- `VECTOR_ADD_COMPONENT`
- `CART_EQ`
- `VECTOR_MUL_COMPONENT`
- `ARITH`
- `VECTOR_ADD_LDISTRIB`
- `VECTOR_MUL_ASSOC`
- `UNWIND_THM2`
- `REAL_MUL_LZERO`
- `REAL_LT_01`
- `REAL_LET_TRANS`
- `REAL_LE_RMUL`


---

## BETWEEN_SYM

### Name of formal statement
BETWEEN_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BETWEEN_SYM = prove
 (`!u v w. between v (u,w) <=> between v (w,u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETWEEN_THM] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN EXISTS_TAC `&1 - u` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY VECTOR_ARITH_TAC THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers `u`, `v`, and `w`, `v` is between `u` and `w` if and only if `v` is between `w` and `u`.

### Informal sketch
The proof demonstrates the symmetry property of the `between` relation for real numbers.

- The proof starts by universally generalizing over `u`, `v`, and `w`.
- The definition of `between` (`BETWEEN_THM`) is rewritten.
- The equivalence is split into two implications to prove.
- For the forward direction `between v (u,w) ==> between v (w,u)`, assuming `between v (u, w)`, we need witnesses `s` and `t` such that `&0 <= s /\ &0 <= t /\ s + t = &1 /\ v = u + s * (w - u)`. Given `between v (u,w)`, we know such `s` exists. So we choose `s` and create `t = 1 - s`. Then we rewrite, apply vector arithmetic tactics, and simplify to prove the claim.
- The reverse direction `between v (w,u) ==> between v (u,w)` can then be proved similarly by an analogous argument.

### Mathematical insight
This theorem states that the `between` relationship is symmetric. Geometrically, `v` lying on the line segment between `u` and `w` is equivalent to `v` lying on the line segment between `w` and `u`. This reflects the intuition that a line segment is invariant under reversing the order of its endpoints.

### Dependencies
- `BETWEEN_THM`


---

## BETWEEN_METRICAL

### Name of formal statement
BETWEEN_METRICAL

### Type of the formal statement
theorem

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
  FIRST_X_ASSUM(MP_TAC o SYM) THEN VECTOR_ARITH_TAC);;
```

### Informal statement
For all vectors `u`, `v`, and `w` in `real^N`, `v` is between `u` and `w` if and only if the distance from `u` to `v` plus the distance from `v` to `w` equals the distance from `u` to `w`.

### Informal sketch
The proof demonstrates the equivalence between the geometric notion of a point lying between two others and the algebraic condition on distances.

- The proof starts by rewriting the definition of `between v (u, w)` which uses the `BETWEEN_THM` to an existential statement `exists x. &0 <= x /\ x <= &1 /\ v = x % u + (&1 - x) % w`.
- It uses vector arithmetic to rewrite  `x % u + (&1 - x) % w` to `w + x % (u - w)`.
- Then `u - w` rewrites to `(u - v) + (v - w)`.
- Subsequently, the proof splits into two branches to show the equivalence:

    - (Forward direction): Assuming `exists x. &0 <= x /\ x <= &1 /\ v = w + x % (u - w)`, it's shown that `norm(u - v) + norm(v - w) = norm(u - w)`. This relies on rewriting and properties of norms, and real arithmetic.
    - (Reverse direction): Assuming `norm(u - v) + norm(v - w) = norm(u - w)`, the proof constructs a value `x` such that `v = w + x % (u - w)` and `&0 <= x /\ x <= &1`. Real arithmetic and the vector multiplication cancellation are applied. The existence of such an `x` is explicitly given by  `norm(u - v:real^N) / (norm(u - v) + norm(v - w))`.

### Mathematical insight
This theorem provides a metrical characterization of the concept of "betweenness" in a vector space. It links the geometric intuition of a point lying on a line segment defined by two other points to a condition involving distances. This equivalence is crucial for many geometric arguments and constructions.

### Dependencies
- `BETWEEN_SYM`
- `BETWEEN_THM`
- `dist` (definition of the distance function)
- `VECTOR_ARITH` library
- `NORM_TRIANGLE_EQ`
- `NORM_NEG`
- `NORM_MUL`
- `NORM_SUB`
- `REAL_MUL_AC`
- `NORM_POS_LE`
- `NORM_EQ_0`
- `VECTOR_SUB_EQ`
- `REAL_POS`
- `REAL_LE_RDIV_EQ`
- `REAL_LE_LDIV_EQ`
- `REAL_MUL_LZERO`
- `REAL_MUL_LID`
- `REAL_LE_ADDR`
- `VECTOR_MUL_LCANCEL_IMP`
- `REAL_LT_IMP_NZ`
- `REAL_DIV_LMUL`

### Porting notes (optional)
- The proof makes heavy use of rewriting with vector arithmetic identities. Ensure that the target proof assistant has a comparable library with similar lemmas about vector operations and norms.
- The tactics `ASM_CASES_TAC`, `FIRST_X_ASSUM` and `ASM_SIMP_TAC` will need to be translated into something similar in other proof assistants. These are automation tactics to apply assumptions on an assumption list.


---

