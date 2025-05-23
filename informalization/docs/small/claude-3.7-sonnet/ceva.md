# ceva.ml

## Overview

Number of statements: 7

This file formalizes Ceva's theorem in geometry, which relates the concurrent cevians of a triangle. It provides the formal statement and proof of the theorem, utilizing the multivariate geometric foundations from convex.ml and algebraic techniques from sos.ml. The implementation likely includes vector-based representations of triangles and their associated lines, as well as the necessary conditions for concurrency expressed in terms of ratios.

## BETWEEN_THM

### BETWEEN_THM
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem characterizes the betweenness relation `between x (a,b)` for points in a real vector space. It states that:

$$\text{between}(x, (a,b)) \iff \exists u. 0 \leq u \land u \leq 1 \land x = u \cdot a + (1-u) \cdot b$$

where $x$, $a$, and $b$ are points in $\mathbb{R}^N$, and $u$ is a real number. The symbol $\cdot$ represents scalar multiplication.

### Informal proof
The proof proceeds as follows:

- Start by using the theorem `BETWEEN_IN_CONVEX_HULL` which establishes that $x$ is between points $a$ and $b$ if and only if $x$ is in the convex hull of the set $\{a,b\}$.
- Apply a symmetric reordering of the set using `SET_RULE` to get $\{a,b\} = \{b,a\}$.
- Use the alternate characterization of a two-point convex hull from `CONVEX_HULL_2_ALT`, which states that the convex hull of $\{a,b\}$ is the set $\{a + u \cdot (b-a) \mid 0 \leq u \land u \leq 1\}$.
- Apply transformations using `IN_ELIM_THM` to eliminate set membership notation.
- Use vector arithmetic to equivalently rewrite the expression $a + u \cdot (b-a)$ as $u \cdot a + (1-u) \cdot b$.

### Mathematical insight
This theorem provides a parametric representation of points that lie between two given points in a vector space. The parameter $u$ represents a weighted average, with $u=0$ corresponding to point $b$, $u=1$ corresponding to point $a$, and intermediate values of $u$ giving points that lie on the line segment between $a$ and $b$.

The betweenness relation is fundamental in geometry and serves as a building block for many spatial concepts. This particular characterization is useful because it expresses betweenness in terms of a convex combination of the endpoints, which aligns with the definition of line segments in vector spaces.

### Dependencies
- Theorems:
  - `BETWEEN_IN_CONVEX_HULL`: Relates the betweenness relation to membership in a convex hull
  - `CONVEX_HULL_2_ALT`: Provides an alternate characterization of the convex hull of two points

### Porting notes
When porting to other systems:
- Ensure that the betweenness relation is defined compatibly with HOL Light's definition
- The proof relies on vector arithmetic, so the target system should have good support for vector operations
- The parametric representation using scalar $u$ is standard across most mathematical formalizations

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
The theorem states that for vectors $a$, $b$, $c$, $d$, $e$, and $f$, the following equivalence holds:
$$\|a\| \cdot \|b\| \cdot \|c\| = \|d\| \cdot \|e\| \cdot \|f\| \iff (a \cdot a) \cdot (b \cdot b) \cdot (c \cdot c) = (d \cdot d) \cdot (e \cdot e) \cdot (f \cdot f)$$

where $\|\cdot\|$ represents the norm of a vector and $\cdot$ represents the dot product.

### Informal proof
The proof proceeds as follows:

- First, a lemma is established: For any real numbers $x$ and $y$, if $x \geq 0$ and $y \geq 0$, then $x^2 = y^2 \iff x = y$.
  
  This lemma is proven by:
  - Converting $x^2 = y^2$ to $x \cdot x = y \cdot y$
  - For the forward direction ($\Rightarrow$), it's trivial when $x = y$
  - For the reverse direction ($\Leftarrow$), we examine the cases from the total ordering of reals:
    - If $x < y$, then $x \cdot x < y \cdot y$ (by REAL_LT_MUL2)
    - If $y < x$, then $y \cdot y < x \cdot x$ (by REAL_LT_MUL2)
    - Both contradict our assumption, so $x = y$ must hold

- The main theorem is proven by:
  1. Rewriting the norm terms using the identity $\|v\|^2 = v \cdot v$ (NORM_POW_2)
  2. Rewriting the products of powers using the identity $(a^n \cdot b^n) = (a \cdot b)^n$ (REAL_POW_MUL)
  3. Applying the lemma to show equivalence between the squared forms
  4. Using NORM_POS_LE to verify that norms of vectors are non-negative, satisfying the lemma's conditions

### Mathematical insight
This theorem establishes that comparing products of norms of vectors is equivalent to comparing products of their squared lengths (dot products with themselves). This is useful for simplifying geometric calculations and proofs, as it allows for working with dot products instead of norms when comparing magnitudes.

The result is particularly useful in computational geometry or in situations where dot products are easier to work with than explicit norms. It shows that the relationship between squared norms preserves the relationship between the norms themselves, simplifying algebraic manipulations in vector analysis.

### Dependencies
- Theorems:
  - `NORM_POW_2`: Relates a vector's norm squared to its dot product with itself
  - `REAL_POW_MUL`: Property of powers of products of real numbers
  - `NORM_POS_LE`: States that norms of vectors are non-negative
  - `REAL_LT_TOTAL`: Total ordering property of real numbers
  - `REAL_LT_MUL2`: Multiplication preserves strict inequalities for positive reals
  - `REAL_LT_REFL`: Reflexivity property of the strict less-than relation

### Porting notes
When porting to other systems:
- Ensure that the system has appropriate libraries for vector operations, particularly dot products and norms
- The proof relies on properties of real numbers and vector operations that should be available in most proof assistants
- The internal lemma about squared real numbers might need to be proven separately or imported from a standard library

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
For any three points $a$, $b$, and $c$ in $\mathbb{R}^2$, the set $\{a, b, c\}$ is collinear if and only if
$$(a_1 - b_1)(b_2 - c_2) = (a_2 - b_2)(b_1 - c_1)$$

where $a_1, a_2, b_1, b_2, c_1, c_2$ are the first and second components of the points $a, b, c$ respectively.

### Informal proof
The proof establishes the equivalence between the geometric definition of collinearity and an algebraic condition based on cross products.

First, an auxiliary lemma is proven: if $y_1 \neq 0$ and $x_2 y_1 = x_1 y_2$, then there exists a scalar $c$ such that $x_1 = c \cdot y_1$ and $x_2 = c \cdot y_2$.

The main proof proceeds as follows:

* Special case: If $a = b$, then the algebraic condition simplifies to $0 = 0$, which is true. In this case, $\{a, b, c\} = \{a, c\}$ contains only two points, which are always collinear.

* For the general case where $a \neq b$, we prove both directions of the equivalence:

  * ($\Rightarrow$) If the points are collinear, then by definition there exists a vector $v$ such that both $b-a$ and $c-b$ are scalar multiples of $v$. From this, we can derive that $(a_1 - b_1)(b_2 - c_2) = (a_2 - b_2)(b_1 - c_1)$ using vector component relationships.

  * ($\Leftarrow$) If $(a_1 - b_1)(b_2 - c_2) = (a_2 - b_2)(b_1 - c_1)$, we show that $c-b$ is a scalar multiple of $a-b$, which implies collinearity. We use the vector $a-b$ as the direction vector in the definition of collinearity, and prove that all points in $\{a, b, c\}$ lie on the line determined by this vector.

The proof completes by applying the lemma to show that the components of the vectors satisfy the necessary proportionality relationships.

### Mathematical insight
This theorem provides an elegant algebraic characterization of when three points in a plane are collinear. The condition $(a_1 - b_1)(b_2 - c_2) = (a_2 - b_2)(b_1 - c_1)$ is essentially checking if the cross product of vectors $\overrightarrow{ab}$ and $\overrightarrow{bc}$ is zero, which happens precisely when the vectors are parallel (or one is zero).

The formula can be seen as a determinant criterion: three points are collinear if and only if the determinant of the matrix formed by the vectors from one point to the others is zero. This is a standard result in analytic geometry and provides a computationally efficient way to test collinearity.

This result is particularly useful in computational geometry, computer graphics, and formal verification of geometric theorems.

### Dependencies
- `collinear`: Definition of collinearity in a vector space
- `COLLINEAR_SING`: Theorem about collinearity of singleton sets
- `COLLINEAR_2`: Theorem stating that any two points are collinear

### Porting notes
When porting this theorem:
1. Ensure that the target system has an appropriate representation of 2D points and vector operations
2. Pay attention to how vector components and subscripts are represented in the target system
3. The proof uses a substantial amount of real arithmetic simplification, so appropriate tactics or lemmas for field arithmetic will be helpful

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
For points $A$, $B$, $C$, $X$, $Y$, $Z$, $P$ in $\mathbb{R}^2$, if:
- The points $A$, $B$, and $C$ are not collinear (i.e., they don't lie on a straight line)
- $X$ lies between $B$ and $C$
- $Y$ lies between $A$ and $C$
- $Z$ lies between $A$ and $B$
- $P$ lies between $A$ and $X$
- $P$ lies between $B$ and $Y$
- $P$ lies between $C$ and $Z$

Then:
$$\text{dist}(B,X) \cdot \text{dist}(C,Y) \cdot \text{dist}(A,Z) = \text{dist}(X,C) \cdot \text{dist}(Y,A) \cdot \text{dist}(Z,B)$$

where $\text{dist}(P,Q)$ denotes the Euclidean distance between points $P$ and $Q$.

### Informal proof
This theorem is a weaker version of Ceva's theorem where all the points lie on line segments rather than the lines containing them.

The proof proceeds algebraically by expressing the geometric conditions in terms of vector equations:

- We begin by rewriting the statement using the definitions of distance, cross product norm, collinearity, and the between relation
- The "between" relations for points $X$, $Y$, $Z$, and $P$ give us parametric representations of these points in terms of $A$, $B$, and $C$
- We substitute these parametric expressions into our equation
- We work with components of the vectors and express everything in the 2-dimensional Cartesian coordinate system
- The non-collinearity condition of points $A$, $B$, and $C$ is used to ensure that the geometric configuration is valid
- Finally, we apply real algebraic simplifications to derive the desired equality

The final step uses a real ring decision procedure to complete the proof by showing that the resulting algebraic expression is true.


### Mathematical insight
This theorem is a variant of Ceva's theorem in plane geometry. The classical Ceva's theorem deals with lines from vertices of a triangle to points on the opposite sides, while this version specifically considers the case where all the points lie between the vertices.

The statement relates the products of certain distances when three lines from the vertices of a triangle intersect at a common point. In this setup:
- $X$, $Y$, and $Z$ lie on the sides of triangle $ABC$
- Point $P$ is chosen so that it lies on the line segments $AX$, $BY$, and $CZ$

The resulting equation provides an elegant relationship between the relative distances. This type of relationship is fundamental in projective geometry and has applications in computer graphics, computational geometry, and geometric constructions.

### Dependencies
- `dist`: Definition of Euclidean distance
- `NORM_CROSS`: Theorem about the norm of the cross product
- `COLLINEAR`: Definition of collinearity
- `BETWEEN_THM`: Theorem characterizing when a point is between two others
- `dot`: Definition of the dot product
- `SUM_2`: Theorem about summation over 2 indices
- `VECTOR_SUB_COMPONENT`: Theorem about vector subtraction components
- `DIMINDEX_2`: Theorem about dimension of 2D space
- `VECTOR_ADD_COMPONENT`: Theorem about vector addition components
- `CART_EQ`: Theorem about equality of Cartesian vectors
- `FORALL_2`: Theorem about universal quantification over 2D vectors
- `VECTOR_MUL_COMPONENT`: Theorem about scalar multiplication components

### Porting notes
When porting this theorem:
1. Ensure that the destination system has appropriate definitions for "between" and "collinear" that match HOL Light's implementations
2. The proof relies heavily on algebraic manipulation of vector equations, so a system with good support for vector algebra would be preferable
3. The final step uses a real algebraic decision procedure (`REAL_RING`); an equivalent automation capability would be helpful in the target system
4. The theorem statement assumes points in $\mathbb{R}^2$, but the proof approach could be adapted to other geometric settings with appropriate modifications

---

## CEVA

### CEVA
- `CEVA`

### Type of the formal statement
- theorem

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
Let $A, B, C, X, Y, Z$ be points in $\mathbb{R}^2$ such that:
- The points $A, B, C$ are not collinear
- $X$ lies between $B$ and $C$
- $Y$ lies between $C$ and $A$
- $Z$ lies between $A$ and $B$

Then the following are equivalent:
1. $\frac{|BX|}{|XC|} \cdot \frac{|CY|}{|YA|} \cdot \frac{|AZ|}{|ZB|} = 1$
2. There exists a point $P$ such that $P$ lies on all three line segments $AX$, $BY$, and $CZ$

where $|PQ|$ denotes the distance between points $P$ and $Q$.

### Informal proof
This is a proof of Ceva's theorem for triangles.

We'll start by eliminating degenerate cases where any two points among $A$, $B$, and $C$ are equal. In these cases, the points would be collinear, contradicting our hypothesis.

Given that $X$ lies between $B$ and $C$, $Y$ between $C$ and $A$, and $Z$ between $A$ and $B$, we can express these points as convex combinations:
- $X = x B + (1-x) C$ for some $x \in [0,1]$
- $Y = y C + (1-y) A$ for some $y \in [0,1]$
- $Z = z A + (1-z) B$ for some $z \in [0,1]$

Now we calculate the distances:
- $|BX| = |(1-x)(B-C)|$ $= |1-x| \cdot |B-C|$ $= (1-x) \cdot |B-C|$ (since $0 \leq x \leq 1$)
- $|XC| = |x(B-C)|$ $= x \cdot |B-C|$
- $|CY| = |(1-y)(C-A)|$ $= (1-y) \cdot |C-A|$
- $|YA| = |y(C-A)|$ $= y \cdot |C-A|$
- $|AZ| = |(1-z)(A-B)|$ $= (1-z) \cdot |A-B|$
- $|ZB| = |z(A-B)|$ $= z \cdot |A-B|$

The condition $\frac{|BX|}{|XC|} \cdot \frac{|CY|}{|YA|} \cdot \frac{|AZ|}{|ZB|} = 1$ becomes:
$\frac{(1-x)}{x} \cdot \frac{(1-y)}{y} \cdot \frac{(1-z)}{z} = 1$

For the second part of the theorem, we need to prove that this equation holds if and only if there exists a point $P$ that lies on all three line segments $AX$, $BY$, and $CZ$.

If there is such a point $P$, then:
- $P = uA + (1-u)X$ for some $u \in [0,1]$
- $P = vB + (1-v)Y$ for some $v \in [0,1]$
- $P = wC + (1-w)Z$ for some $w \in [0,1]$

The key insight is to prove that such values $u, v, w$ exist if and only if the Ceva's ratio equals 1.

For the forward direction:
If $\frac{(1-x)}{x} \cdot \frac{(1-y)}{y} \cdot \frac{(1-z)}{z} = 1$, we need to find $u, v, w$ satisfying:
- $w = (1-u)(1-x)$
- $v = (1-u)x$
- $u = (1-v)(1-y)$
- $u = (1-w)z$
- $v = (1-w)(1-z)$
- $w = (1-v)y$
- $0 \leq u,v,w \leq 1$

The proof uses algebraic manipulations to show that such values exist.

For the reverse direction:
If there exists a point $P$ with the given properties, then the system of equations must be consistent, which implies the Ceva's condition.

### Mathematical insight
Ceva's theorem establishes a powerful connection between metric properties (ratios of distances) and a purely geometric condition (concurrent lines) in a triangle. Originally published by Giovanni Ceva in 1678, this theorem belongs to projective geometry and has numerous applications in geometric proofs.

The theorem provides an elegant way to verify whether three lines drawn from the vertices of a triangle to points on the opposite sides are concurrent. The ratio condition is particularly useful because it's invariant under affine transformations.

The proof presented here uses both algebraic and geometric techniques, demonstrating how vector algebra can be used to establish classical geometric results.

### Dependencies
- Definitions:
  - `between`: Defines when a point lies between two other points
  - `collinear`: Defines when a set of points lies on a single line
  - `dist`: Defines the Euclidean distance between two points

### Porting notes
When porting this theorem:
- Ensure that the `between` relation correctly captures the notion of a point lying on a line segment
- Be careful with the handling of degenerate cases (when points coincide)
- The theorem relies on vector algebra in $\mathbb{R}^2$, which should be available in most proof assistants
- The proof uses a combination of algebraic manipulations and geometric insights, so a system with good support for both algebraic simplification and geometric reasoning would be advantageous

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
For any points $u$, $v$, and $w$, the point $v$ is between $u$ and $w$ if and only if $v$ is between $w$ and $u$.

Formally: $\forall u,v,w. \text{between}(v, (u,w)) \Leftrightarrow \text{between}(v, (w,u))$

### Informal proof
The proof demonstrates the symmetry of the "between" relation with respect to its endpoint arguments:

- We begin by using the `BETWEEN_THM` definition of "between", which states that $v$ is between $u$ and $w$ if there exists a real number $t \in [0,1]$ such that $v = (1-t)u + tw$.
- We prove both directions of the equivalence:
  - For the forward direction, if $v$ is between $u$ and $w$, then there exists $t \in [0,1]$ such that $v = (1-t)u + tw$.
  - We choose the witness $1-t$ for the reverse direction and show that $v = (1-(1-t))w + (1-t)u = tw + (1-t)u$.
  - We verify that $1-t \in [0,1]$ because $t \in [0,1]$.
  - The vector arithmetic and real arithmetic tactics complete the proof by confirming the algebraic equivalence.

### Mathematical insight
This theorem formalizes the intuitive geometric fact that the notion of "betweenness" is symmetric with respect to the endpoints. If a point lies on the line segment between two points, the order in which we specify those two endpoints doesn't matter.

According to the comment, this result was initially included for geometric intuition but became redundant because the symmetry property became part of the definition of "between". It serves as a verification that the formal definition of "between" aligns with the intuitive geometric concept.

### Dependencies
- `BETWEEN_THM`: Definition of a point being between two other points in terms of convex combinations

### Porting notes
When porting this theorem, ensure that your system's definition of "between" corresponds to the one in HOL Light, which uses convex combinations. The proof relies heavily on arithmetic reasoning (vector and real), so you'll need to ensure similar automation is available in your target system.

---

## BETWEEN_METRICAL

### BETWEEN_METRICAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem establishes an equivalence between the betweenness relation and metric properties for points in a Euclidean space $\mathbb{R}^N$. Specifically:

For all points $u, v, w \in \mathbb{R}^N$, the point $v$ is between $u$ and $w$ if and only if:
$$d(u,v) + d(v,w) = d(u,w)$$

Where $d(x,y)$ represents the Euclidean distance between points $x$ and $y$.

### Informal proof
The proof establishes the equivalence between the betweenness relation and the metric characterization.

First, we use symmetry properties of betweenness and rewrite using the theorem `BETWEEN_THM`, which defines betweenness in terms of convex combinations.

From `BETWEEN_THM`, we know that $v$ lies between $u$ and $w$ if and only if $v = (1-t)u + tw$ for some $t \in [0,1]$.

We rewrite this using vector arithmetic as $v = v + t(u-v)$, and note that $u-w = (u-v)+(v-w)$.

For the forward direction:
- Assuming $v$ is between $u$ and $w$, we show there exists a $t \in [0,1]$ such that $v$ is a convex combination of $u$ and $w$.
- The key step is to choose $t = \frac{\|u-v\|}{\|u-v\|+\|v-w\|}$ when $\|u-v\|+\|v-w\| > 0$.
- For the degenerate case where $\|u-v\|+\|v-w\| = 0$, we know that $u = v = w$, so we can use $t = 0$.

For the reverse direction:
- Assuming $d(u,v) + d(v,w) = d(u,w)$, we use the equality case in the triangle inequality, which implies that the vectors $u-v$ and $v-w$ are parallel and point in the same direction.
- This allows us to express $v$ as a convex combination of $u$ and $w$, showing that $v$ is between $u$ and $w$.

The key mathematical insight comes from using the vector form and the equality case of the triangle inequality (`NORM_TRIANGLE_EQ`).

### Mathematical insight
This theorem provides a metric characterization of betweenness in Euclidean space. The fact that a point lies between two others is equivalent to saying that the distances add up exactly (with no "detour").

This equivalence connects the geometric notion of betweenness (a point lying on the line segment between two other points) with the metric structure of the space. It's a fundamental result that shows how the axiomatically defined betweenness relation can be characterized purely in terms of distances.

This characterization is useful for proving other properties of Euclidean geometry and can simplify many geometric arguments by allowing a switch between algebraic (vector) and metric perspectives.

### Dependencies
- `BETWEEN_SYM`: Symmetry property of betweenness relation
- `BETWEEN_THM`: Definition of betweenness in terms of convex combinations
- `NORM_TRIANGLE_EQ`: The equality case of the triangle inequality
- `dist`: Definition of Euclidean distance
- Various theorems about vector arithmetic and properties of norms

### Porting notes
When porting this theorem:
- Ensure that the definition of `between` matches HOL Light's definition in terms of convex combinations
- Make sure the `dist` function correctly represents Euclidean distance
- The proof uses various vector arithmetic identities which may need to be established separately in another system

---

