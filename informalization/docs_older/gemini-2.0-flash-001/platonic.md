# platonic.ml

## Overview

Number of statements: 91

`platonic.ml` formalizes the existence of the five Platonic solids and proves their uniqueness. It builds upon the `polyhedron.ml` and `cross.ml` files which provides definitions and theorems about polyhedra and cross products in multivariate analysis. Thus, it contributes a key result to the formalization of geometry in HOL Light.


## std_tetrahedron

### Name of formal statement
std_tetrahedron

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let std_tetrahedron = new_definition
 `std_tetrahedron =
     convex hull
       {vector[&1;&1;&1],vector[-- &1;-- &1;&1],
        vector[-- &1;&1;-- &1],vector[&1;-- &1;-- &1]}:real^3->bool`;;
```

### Informal statement
The definition of `std_tetrahedron` is given as the convex hull of the set containing four vectors in 3-dimensional real space: `vector[&1;&1;&1]`, `vector[-- &1;-- &1;&1]`, `vector[-- &1;&1;-- &1]`, and `vector[&1;-- &1;-- &1]`.

### Informal sketch
The definition introduces `std_tetrahedron` as the convex hull of a specific set of four points in `real^3`.
- The definition relies on the previously defined `convex hull` and `vector` concepts. The four specific vectors represent the vertices of a regular tetrahedron centered at the origin, with a side length related to `sqrt(8/3)`.

### Mathematical insight
This definition constructs the standard tetrahedron as the convex hull of its four vertices.  This facilitates reasoning about the tetrahedron using properties and theorems related to convex hulls and vectors. The chosen coordinates provide a symmetric representation centered around the origin. The regular tetrahedron is a fundamental Platonic solid.

### Dependencies
- Base:
    - `convex hull`
    - `vector`

### Porting notes
- Ensure that the target proof assistant has a well-defined notion of convex hull, vector spaces, and real numbers.
- Special care might be needed when porting the `vector` constructor, particularly ensuring the correct interpretation of indexing and dimension. Lean, Coq, and Isabelle all provide sufficient vector space libraries that should allow straightforward representation, if rewritten in a more idiomatic style.


---

## std_cube

### Name of formal statement
std_cube

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let std_cube = new_definition
 `std_cube =
     convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1]}:real^3->bool`;;
```
### Informal statement
The standard cube, `std_cube`, is defined as the convex hull of the set containing the following eight vertices in three-dimensional real space: (1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), and (-1, -1, -1).

### Informal sketch
The definition introduces `std_cube` and equates it to applying the `convex hull` operator to a specific set of eight vectors. The set consists of all possible vertices of a cube centered at the origin with side length 2, where each coordinate is either 1 or -1.

### Mathematical insight
This definition provides a formal characterization of the standard cube in 3D space. It leverages the concept of the convex hull, which, when applied to the vertices of a geometric object, yields the entire object, including its interior. This definition is useful in various geometric proofs and constructions within HOL Light. It represents the cube as the smallest convex set containing the given vertices.

### Dependencies
- Definitions:
  - `convex hull`
  - `vector`


---

## std_octahedron

### Name of formal statement
- std_octahedron

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let std_octahedron = new_definition
 `std_octahedron =
      convex hull
       {vector[&1;&0;&0],vector[-- &1;&0;&0],
        vector[&0;&0;&1],vector[&0;&0;-- &1],
        vector[&0;&1;&0],vector[&0;-- &1;&0]}:real^3->bool`;;
```
### Informal statement
- The variable `std_octahedron` is defined to be the convex hull of the set containing the following six points in three-dimensional real space: the point with coordinates (1, 0, 0), the point with coordinates (-1, 0, 0), the point with coordinates (0, 0, 1), the point with coordinates (0, 0, -1), the point with coordinates (0, 1, 0), and the point with coordinates (0, -1, 0).

### Informal sketch
- The definition introduces `std_octahedron` as the convex hull of a specific set of six points in 3D real space.
- The points are (1,0,0), (-1,0,0), (0,0,1), (0,0,-1), (0,1,0) and (0,-1,0), which are the vertices of a regular octahedron centered at the origin.
- The `convex hull` operation is applied to this set.

### Mathematical insight
- The definition provides a formal representation of a standard octahedron centered at the origin in 3D space.
- The description using `convex hull` ensures that the octahedron consists of all points that can be expressed as a convex combination of its vertices.
- This is a standard and canonical way to define geometric objects in formal settings.

### Dependencies
- `convex`
- `hull`
- `vector`


---

## std_dodecahedron

### Name of formal statement
std_dodecahedron

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let std_dodecahedron = new_definition
 `std_dodecahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1],
        vector[&0;inv p;p],vector[&0;inv p;--p],
        vector[&0;--inv p;p],vector[&0;--inv p;--p],
        vector[inv p;p;&0],vector[inv p;--p;&0],
        vector[--inv p;p;&0],vector[--inv p;--p;&0],
        vector[p;&0;inv p],vector[--p;&0;inv p],
        vector[p;&0;--inv p],vector[--p;&0;--inv p]}:real^3->bool`;;
```

### Informal statement
The standard dodecahedron, `std_dodecahedron`, is defined as the convex hull of a set of 20 points in 3-dimensional real space. These points are the vertices of a regular dodecahedron centered at the origin. The vertices are defined using the golden ratio `p`, which is equal to `(1 + sqrt(5)) / 2`. The set of vertices includes points with coordinates `(±1, ±1, ±1)`, `(0, ±(1/p), ±p)`, `(±(1/p), ±p, 0)`, and `(±p, 0, ±(1/p))`, where all possible sign combinations are included.

### Informal sketch
The definition constructs the standard dodecahedron directly by specifying its 20 vertices and then taking the `convex hull` of this set of points.

*   First, the golden ratio `p` is defined as `(1 + sqrt(5)) / 2`.
*   Then, a set of 20 points in 3D space (`real^3`) is explicitly constructed. These coordinates represent the vertices of a regular dodecahedron. The vertices are given as cartesian coordinates defined with the golden ratio, where each coordinate is either `1`, `-1`, `0`, `p`, `-p`, `1/p` or `-1/p`.
*   Finally, the `convex hull` of this set of points is taken. The `convex hull` operation yields the smallest convex set containing all the defined points.

### Mathematical insight
This definition provides a concrete representation of the standard dodecahedron as the convex hull of its vertices in 3D space, using the golden ratio to define their coordinates. This is a standard approach to defining polyhedra in computational geometry.

### Dependencies
- `convex hull`
- `sqrt`
- `/`
- `+`
- `-`
- `*`
- `&`
- `vector`


---

## std_icosahedron

### Name of formal statement
- std_icosahedron

### Type of the formal statement
- new_definition

### Formal Content
- The full HOL Light statement will be inserted here **after generation**.
```ocaml
let std_icosahedron = new_definition
 `std_icosahedron =
      let p = (&1 + sqrt(&5)) / &2 in
      convex hull
       {vector[&0; &1; p],vector[&0; &1; --p],
        vector[&0; -- &1; p],vector[&0; -- &1; --p],
        vector[&1; p; &0],vector[&1; --p; &0],
        vector[-- &1; p; &0],vector[-- &1; --p; &0],
        vector[p; &0; &1],vector[--p; &0; &1],
        vector[p; &0; -- &1],vector[--p; &0; -- &1]}:real^3->bool`;;
```
### Informal statement
- The `std_icosahedron` is defined as the convex hull of the set containing the following twelve vertices in 3-dimensional real space: (0, 1, p), (0, 1, -p), (0, -1, p), (0, -1, -p), (1, p, 0), (1, -p, 0), (-1, p, 0), (-1, -p, 0), (p, 0, 1), (-p, 0, 1), (p, 0, -1), and (-p, 0, -1), where p is equal to (1 + sqrt(5)) / 2. The type of `std_icosahedron` is `real^3 -> bool`, meaning it is a predicate that determines whether a point in 3D space is inside the icosahedron.

### Informal sketch
- The definition constructs the standard icosahedron in 3D space by first computing the value `p = (1 + sqrt(5)) / 2`, which is the golden ratio. Then, it creates a set containing twelve specific vectors in `real^3`. These vectors represent the vertices of the icosahedron. Finally, it takes the convex hull of this set of vertices, defining the solid icosahedron as the smallest convex set containing these vertices.

### Mathematical insight
- The `std_icosahedron` definition provides a formal representation of a standard icosahedron centered at the origin. The twelve vertices are chosen such that they lie on the unit sphere and form the vertices of a regular icosahedron. The golden ratio `p` appears naturally in the coordinates of the vertices, reflecting the icosahedron's relationship to the golden ratio. This definition is an important foundational step in formalizing properties and theorems related to icosahedra and other polyhedra.

### Dependencies
- Requires definition of `convex hull` and `vector` (presumably, `vector[x; y; z]` is a notation for a 3D vector). Definition of `sqrt` and `/`.


---

## REAL_RAT5_OF_RAT_CONV

### Name of formal statement
REAL_RAT5_OF_RAT_CONV

### Type of the formal statement
Definition

### Formal Content
```ocaml
let REAL_RAT5_OF_RAT_CONV =
  let pth = prove
   (`p = p + &0 * sqrt(&5)`,
    REAL_ARITH_TAC) in
  let conv = REWR_CONV pth in
  fun tm -> if is_ratconst tm then conv tm else REFL tm;;
```

### Informal statement
Define a conversion `REAL_RAT5_OF_RAT_CONV` as follows: 
First, prove the theorem that for any `p`, `p` is equal to `p + &0 * sqrt(&5)`.
Then, define a conversion `conv` by rewriting using this theorem.
Finally, define `REAL_RAT5_OF_RAT_CONV` to be a function that, if the term `tm` is a rational constant, applies the conversion `conv` to it, otherwise returns the reflexive theorem `tm = tm`.

### Informal sketch
*   The conversion `REAL_RAT5_OF_RAT_CONV` aims to express a rational number `p` in the form `p + 0 * sqrt(5)`.
*   This is achieved by proving the theorem `p = p + &0 * sqrt(&5)` using `REAL_ARITH_TAC`.
*   The proved theorem is then used to create a rewriting conversion `REWR_CONV`.
*   The conversion is only applied if the term is a rational constant to avoid unnecessary application of rewrite rule.
*    If the term is not a rational number then return the reflexivity theorem for that term `REFL tm`.

### Mathematical insight
The motivation is to represent rational numbers as elements of `Q[sqrt(5)]` in a canonical form `r1 + r2 * sqrt(5)` where `r1` and `r2` are rational constants (where `r2` may be zero). This function specifically injects a rational number `p` into `Q[sqrt(5)]` by expressing it as `p + 0 * sqrt(5)`. This is useful for performing arithmetic computations in `Q[sqrt(5)]`.

### Dependencies
- Theorem: `p = p + &0 * sqrt(&5)` (proved within the definition)
- Tactics: `REAL_ARITH_TAC`
- Conversions: `REWR_CONV`, `REFL`
- Functions: `is_ratconst`


---

## REAL_RAT_OF_RAT5_CONV

### Name of formal statement
REAL_RAT_OF_RAT5_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_RAT_OF_RAT5_CONV =
  let pth = prove
   (`p + &0 * sqrt(&5) = p`,
    REAL_ARITH_TAC) in
  GEN_REWRITE_CONV TRY_CONV [pth];;
```

### Informal statement
The theorem states that `p + &0 * sqrt(&5) = p` is true, where `p` is a real number. The `REAL_RAT_OF_RAT5_CONV` conversion simplifies expressions of the form `p + &0 * sqrt(&5)` to `p` using rewriting.

### Informal sketch
- The theorem `p + &0 * sqrt(&5) = p` is proved using `REAL_ARITH_TAC`, which is a tactic that attempts to solve goals using real arithmetic decision procedures.
- `GEN_REWRITE_CONV TRY_CONV [pth]` creates a conversion that uses the proven theorem `pth` as a rewrite rule. `TRY_CONV` ensures that the conversion doesn't fail if the rewrite rule doesn't apply. The resulting conversion then simplifies expressions matching the left-hand side of the theorem to the right-hand side.

### Mathematical insight
The mathematical insight is that multiplying any real number by zero results in zero and adding zero to any real number will result in the real number itself, so for any real number `p`, the expression `p + 0 * sqrt(5)` simplifies to just `p`.

### Dependencies
- Theorems:
    - `REAL_ARITH_TAC`
- Tactics:
    - `prove`
    - `GEN_REWRITE_CONV`
    - `TRY_CONV`


---

## REAL_RAT5_ADD_CONV

### Name of formal statement
REAL_RAT5_ADD_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_RAT5_ADD_CONV =
  let pth = prove
    (`(a1 + b1 * sqrt(&5)) + (a2 + b2 * sqrt(&5)) =
      (a1 + a2) + (b1 + b2) * sqrt(&5)`,
     REAL_ARITH_TAC) in
  REAL_RAT_ADD_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   LAND_CONV REAL_RAT_ADD_CONV THENC
   RAND_CONV(LAND_CONV REAL_RAT_ADD_CONV) THENC
   REAL_RAT_OF_RAT5_CONV);;
```

### Informal statement
The theorem states that the sum of two expressions of the form `a1 + b1 * sqrt(5)` and `a2 + b2 * sqrt(5)` is equal to `(a1 + a2) + (b1 + b2) * sqrt(5)`. This conversion theorem, namely `REAL_RAT5_ADD_CONV`, either uses `REAL_RAT_ADD_CONV` directly, or proceeds by first converting rational numbers to the form `a + b * sqrt(5)` via `REAL_RAT5_OF_RAT_CONV`, then rewriting using the proved additive property of such expressions, adding the left and right arguments using `REAL_RAT_ADD_CONV` and finally converting back to the form involving only rational numbers using `REAL_RAT_OF_RAT5_CONV`.

### Informal sketch
- The theorem aims to establish a simplification rule for the addition of two numbers in the form `a + b * sqrt(5)`, where `a` and `b` are rational numbers. The proof proceeds by case analysis, in the first case using `REAL_RAT_ADD_CONV`.
- Otherwise:
    - Convert both summands from rational numbers to the extended form `a + b * sqrt(5)` using `REAL_RAT5_OF_RAT_CONV`.
    - Prove the additive property `(a1 + b1 * sqrt(5)) + (a2 + b2 * sqrt(5)) = (a1 + a2) + (b1 + b2) * sqrt(5)` using `REAL_ARITH_TAC`.
    - Rewrite the expression using the proved additive property.
    - Apply `REAL_RAT_ADD_CONV` to add the rational parts `a1` and `a2`.
    - Apply `REAL_RAT_ADD_CONV` to add the rational parts `b1` and `b2`.
    - Convert the result back to the form `a + b * sqrt(5)` to `a + b * sqrt(5)` using `REAL_RAT_OF_RAT5_CONV`.

### Mathematical insight
This theorem provides an efficient way to simplify expressions involving the addition of numbers in the form `a + b * sqrt(5)`, where `a` and `b` are rational, which is a common operation when working with fields extensions of the rationals. It leverages a pre-proved arithmetic fact about the addition and regrouping of such expressions. The conversion to the specific form and back allows for utilizing existing rational arithmetic conversion theorems.

### Dependencies
- `REAL_ARITH_TAC`
- `REAL_RAT_ADD_CONV`
- `REAL_RAT5_OF_RAT_CONV`
- `REAL_RAT_OF_RAT5_CONV`

### Porting notes (optional)
The main challenge in porting this theorem lies in replicating the automation provided by `REAL_ARITH_TAC`. Other proof assistants might require a more manual proof of the additive property. The rewriting steps and the conversions between different representations of numbers should be straightforward to implement in most proof assistants.


---

## REAL_RAT5_SUB_CONV

### Name of formal statement
REAL_RAT5_SUB_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_RAT5_SUB_CONV =
  let pth = prove
    (`(a1 + b1 * sqrt(&5)) - (a2 + b2 * sqrt(&5)) =
      (a1 - a2) + (b1 - b2) * sqrt(&5)`,
     REAL_ARITH_TAC) in
  REAL_RAT_SUB_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   LAND_CONV REAL_RAT_SUB_CONV THENC
   RAND_CONV(LAND_CONV REAL_RAT_SUB_CONV) THENC
   REAL_RAT_OF_RAT5_CONV);;
```

### Informal statement
The difference of two numbers of the form `a1 + b1 * sqrt(5)` and `a2 + b2 * sqrt(5)` can be expressed as `(a1 - a2) + (b1 - b2) * sqrt(5)`, where `a1`, `a2`, `b1`, and `b2` are rational numbers.

### Informal sketch
The proof proceeds by the following steps:

- First, an arithmetic tactic (`REAL_ARITH_TAC`) proves the main subtraction identity: `(a1 + b1 * sqrt(5)) - (a2 + b2 * sqrt(5)) = (a1 - a2) + (b1 - b2) * sqrt(5)`. This result is stored as a theorem `pth`.
- The tactic then tries `REAL_RAT_SUB_CONV` and if that fails it proceeds to:
  - Converts both operands which are of the form `a + b * sqrt(5)`, where `a` and `b` are rational numbers, into that form using `REAL_RAT5_OF_RAT_CONV`.
  - Rewrites the subtraction using the theorem `pth` proved above.
  - Applies `REAL_RAT_SUB_CONV` to the left and right operands.
  - Finally, converts the result back from the form `a + b * sqrt(5)` to a real number using `REAL_RAT_OF_RAT5_CONV`.

### Mathematical insight
This theorem shows how subtraction interacts with numbers of the form `a + b * sqrt(5)`, where `a` and `b` are rational. It is a useful simplification rule when dealing with such numbers, as intermediate calculations can be kept in the same form.

### Dependencies
- `REAL_ARITH_TAC`
- `REAL_RAT_SUB_CONV`
- `REAL_RAT5_OF_RAT_CONV`
- `REAL_RAT_OF_RAT5_CONV`


---

## REAL_RAT5_MUL_CONV

### Name of formal statement
REAL_RAT5_MUL_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_RAT5_MUL_CONV =
  let pth = prove
    (`(a1 + b1 * sqrt(&5)) * (a2 + b2 * sqrt(&5)) =
      (a1 * a2 + &5 * b1 * b2) + (a1 * b2 + a2 * b1) * sqrt(&5)`,
     MP_TAC(ISPEC `&5` SQRT_POW_2) THEN CONV_TAC REAL_FIELD) in
  REAL_RAT_MUL_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   LAND_CONV(COMB_CONV (RAND_CONV REAL_RAT_MUL_CONV) THENC
             RAND_CONV REAL_RAT_MUL_CONV THENC
             REAL_RAT_ADD_CONV) THENC
   RAND_CONV(LAND_CONV
    (BINOP_CONV REAL_RAT_MUL_CONV THENC REAL_RAT_ADD_CONV)) THENC
   REAL_RAT_OF_RAT5_CONV);;
```
### Informal statement
The theorem `REAL_RAT5_MUL_CONV` states that the product of two numbers of the form `a1 + b1 * sqrt(5)` and `a2 + b2 * sqrt(5)` is equal to `(a1 * a2 + 5 * b1 * b2) + (a1 * b2 + a2 * b1) * sqrt(5)`, when interpreted as real numbers.
This theorem also provides a conversion tactic to simplify expressions involving such products. It either directly applies the `REAL_RAT_MUL_CONV` or expands the product using field axioms.

### Informal sketch
The proof/construction proceeds as follows:

- First, attempt to simplify using the existing `REAL_RAT_MUL_CONV`.
- If that fails, the proof proceeds by:
  - Expand the product `(a1 + b1 * sqrt(5)) * (a2 + b2 * sqrt(5))` formally using field axioms. This involves the following steps:
    - Convert rational numbers to the `REAL_RAT5` type using `REAL_RAT5_OF_RAT_CONV`.
    - Rewrite the expression using a pre-proved equation `pth` that directly expands the product. The initial proof `pth` uses `SQRT_POW_2` (the fact that `sqrt(5)^2 = 5`) and `REAL_FIELD` (real field axioms).
    - Apply `REAL_RAT_MUL_CONV` and `REAL_RAT_ADD_CONV` to simplify the expression, working from the leaves to the root of the syntax tree. The `COMB_CONV` converts a combination, while `RAND_CONV` converts the rand of a term. `LAND_CONV` applies a conversion to both sides of a boolean and expression. `BINOP_CONV` applies a conversion to a binary operation.
    - Convert the result back to `REAL_RAT5` form.

### Mathematical insight
The theorem provides a rule for multiplying numbers in the form `a + b * sqrt(5)`, where `a` and `b` are rational numbers, and expresses the result in the same form. This is important because the set of such numbers forms a field extension of the rational numbers, denoted as Q(sqrt(5)). This conversion rule is canonical for dealing with expressions in that field. The tactic automates the expansion and simplification of such expressions.

### Dependencies
- `REAL_RAT_MUL_CONV`
- `REAL_RAT5_OF_RAT_CONV`
- `SQRT_POW_2`
- `REAL_FIELD`
- `REAL_RAT_ADD_CONV`

### Porting notes (optional)
- The tactic `REAL_FIELD` encapsulates the application of field axioms. Other proof assistants may require more explicit invocation of these axioms, or have similar automated methods for algebraic expansions and normalizations.
- `ORELSEC` represents an "or else" mechanism. It attempts the first tactic; if it fails, it applies the second. This control flow needs to be replicated in the target proof assistant.


---

## REAL_RAT5_INV_CONV

### Name of formal statement
REAL_RAT5_INV_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_RAT5_INV_CONV =
  let pth = prove
   (`~(a pow 2 = &5 * b pow 2)
     ==> inv(a + b * sqrt(&5)) =
         a / (a pow 2 - &5 * b pow 2) +
         --b / (a pow 2 - &5 * b pow 2) * sqrt(&5)`,
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_SUB_0] THEN
    SUBGOAL_THEN
     `a pow 2 - &5 * b pow 2 = (a + b * sqrt(&5)) * (a - b * sqrt(&5))`
    SUBST1_TAC THENL
     [MP_TAC(SPEC `&5` SQRT_POW_2) THEN CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN CONV_TAC REAL_FIELD]) in
  fun tm ->
    try REAL_RAT_INV_CONV tm with Failure _ ->
    let th1 = PART_MATCH (lhs o rand) pth tm in
    let th2 = MP th1 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th1)))) in
    let th3 = CONV_RULE(funpow 2 RAND_CONV (funpow 2 LAND_CONV
                REAL_RAT_NEG_CONV)) th2 in
    let th4 = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV
               (RAND_CONV(LAND_CONV REAL_RAT_POW_CONV THENC
                          RAND_CONV(RAND_CONV REAL_RAT_POW_CONV THENC
                                    REAL_RAT_MUL_CONV) THENC
                          REAL_RAT_SUB_CONV) THENC
                REAL_RAT_DIV_CONV)))) th3 in
    let th5 = CONV_RULE(RAND_CONV(LAND_CONV
               (RAND_CONV(LAND_CONV REAL_RAT_POW_CONV THENC
                          RAND_CONV(RAND_CONV REAL_RAT_POW_CONV THENC
                                    REAL_RAT_MUL_CONV) THENC
                          REAL_RAT_SUB_CONV) THENC
                REAL_RAT_DIV_CONV))) th4 in
    th5;;
```

### Informal statement
If `a` and `b` are real numbers such that `a^2` is not equal to `5 * b^2`, then the inverse of `a + b * sqrt(5)` is equal to `a / (a^2 - 5 * b^2) + (-b) / (a^2 - 5 * b^2) * sqrt(5)`.

### Informal sketch
The theorem and its proof are driven by a conversion `REAL_RAT5_INV_CONV` which attempts to simplify (specifically, rationalize) expressions of the form `inv(a + b * sqrt(5))`.

- The main theorem is proved by first generalizing and rewriting with `GSYM REAL_SUB_0`.
- A subgoal is set to prove the identity `a^2 - 5 * b^2 = (a + b * sqrt(5)) * (a - b * sqrt(5))`.
- Substitution is applied using `SUBST1_TAC`.
    - For the left-hand side of the equation, the conversion `REAL_FIELD` is used, applying `MP_TAC` with `SPEC '&5' SQRT_POW_2`.
    - For the right-hand side of the equation, `REAL_ENTIRE` and `DE_MORGAN_THM` are applied followed by `REAL_FIELD`.
- The conversion `REAL_RAT5_INV_CONV` attempts to apply `REAL_RAT_INV_CONV`. If that fails, the proof proceeds.
- The theorem `pth` is matched against the input term `tm` and `REAL_RAT_REDUCE_CONV` is then applied to the left-hand side of the conclusion.
- Various conversions are applied to simplify the expression, including:
    - `funpow 2 RAND_CONV (funpow 2 LAND_CONV REAL_RAT_NEG_CONV)`
    - `RAND_CONV(RAND_CONV(LAND_CONV (RAND_CONV(LAND_CONV REAL_RAT_POW_CONV THENC RAND_CONV(RAND_CONV REAL_RAT_POW_CONV THENC REAL_RAT_MUL_CONV) THENC REAL_RAT_SUB_CONV) THENC REAL_RAT_DIV_CONV))))`
    - `RAND_CONV(LAND_CONV (RAND_CONV(LAND_CONV REAL_RAT_POW_CONV THENC RAND_CONV(RAND_CONV REAL_RAT_POW_CONV THENC REAL_RAT_MUL_CONV) THENC REAL_RAT_SUB_CONV) THENC REAL_RAT_DIV_CONV)))`

### Mathematical insight
This theorem provides a way to express the inverse of a number of the form `a + b * sqrt(5)` as a rational expression involving `a`, `b`, and `sqrt(5)`. This is a standard technique for rationalizing denominators and working with algebraic numbers. The condition `a^2 != 5*b^2` ensures that the denominator in the inverse is non-zero.

### Dependencies
- `REAL_SUB_0`
- `SQRT_POW_2`
- `REAL_FIELD`
- `REAL_ENTIRE`
- `DE_MORGAN_THM`
- `REAL_RAT_INV_CONV`
- `REAL_RAT_REDUCE_CONV`
- `REAL_RAT_NEG_CONV`
- `REAL_RAT_POW_CONV`
- `REAL_RAT_MUL_CONV`
- `REAL_RAT_SUB_CONV`
- `REAL_RAT_DIV_CONV`
### Porting notes (optional)
The main challenge in porting this theorem lies in recreating the automation provided by `REAL_FIELD` and other real number simplification tactics. You may need to manually expand the definitions and perform the algebraic manipulations in another prover. The use of conversions (e.g., `REAL_RAT_POW_CONV`, `REAL_RAT_MUL_CONV`) suggests a strategy of breaking the proof down into a series of rewrite steps based on algebraic identities. Be sure to handle exceptional cases carefully.


---

## REAL_RAT5_DIV_CONV

### Name of formal statement
REAL_RAT5_DIV_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_RAT5_DIV_CONV =
  GEN_REWRITE_CONV I [real_div] THENC
  RAND_CONV REAL_RAT5_INV_CONV THENC
  REAL_RAT5_MUL_CONV;;
```

### Informal statement
The conversion `REAL_RAT5_DIV_CONV` is a tactic that, when applied to a term of the form `x / y`, rewrites it by first applying the rewriting rule for real division (`real_div`), then applies the conversion `REAL_RAT5_INV_CONV` to the divisor `y`, and finally applies the conversion `REAL_RAT5_MUL_CONV` to the resulting term.

### Informal sketch
The theorem defines a conversion tactic to simplify division of real numbers. The key idea is to rewrite division as multiplication by the inverse.

- First, the input expression of the form `x / y` is rewritten using the definition of real division (`real_div`).
- Second, the conversion `REAL_RAT5_INV_CONV` is applied to the divisor `y`, presumably to express the inverse in a specific form (likely involving rationals).
- Third, the conversion `REAL_RAT5_MUL_CONV` is applied to the entire expression, which is now in the form `x * (1/y)`, to simplify the multiplication.

### Mathematical insight
This theorem provides a conversion tactic for simplifying real number division by converting it into multiplication by the inverse. This is a standard technique in real arithmetic, and this conversion likely aims to put the resulting expression into a canonical form, suitable for further simplification or reasoning. The tactic combines several rewrite steps to achieve this. The choice of `REAL_RAT5_INV_CONV` and `REAL_RAT5_MUL_CONV` suggests the intention to handle expressions involving rational numbers or a specific representation of real numbers with rationals.

### Dependencies
- `real_div`
- `REAL_RAT5_INV_CONV`
- `REAL_RAT5_MUL_CONV`


---

## REAL_RAT5_LE_CONV

### Name of formal statement
REAL_RAT5_LE_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_RAT5_LE_CONV =
  let lemma = prove
   (`!x y. x <= y * sqrt(&5) <=>
           x <= &0 /\ &0 <= y \/
           &0 <= x /\ &0 <= y /\ x pow 2 <= &5 * y pow 2 \/
           x <= &0 /\ y <= &0 /\ &5 * y pow 2 <= x pow 2`,
    REPEAT GEN_TAC THEN MP_TAC(ISPEC `&5` SQRT_POW_2) THEN
    REWRITE_TAC[REAL_POS] THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_LE_SQUARE_ABS] THEN
    MP_TAC(ISPECL [`sqrt(&5)`; `y:real`] (CONJUNCT1 REAL_LE_MUL_EQ)) THEN
    SIMP_TAC[SQRT_POS_LT; REAL_OF_NUM_LT; ARITH] THEN REAL_ARITH_TAC) in
  let pth = prove
   (`(a1 + b1 * sqrt(&5)) <= (a2 + b2 * sqrt(&5)) <=>
        a1 <= a2 /\ b1 <= b2 \/
        a2 <= a1 /\ b1 <= b2 /\ (a1 - a2) pow 2 <= &5 * (b2 - b1) pow 2 \/
        a1 <= a2 /\ b2 <= b1 /\ &5 * (b2 - b1) pow 2 <= (a1 - a2) pow 2`,
    REWRITE_TAC[REAL_ARITH
     `a + b * x <= a' + b' * x <=> a - a' <= (b' - b) * x`] THEN
    REWRITE_TAC[lemma] THEN REAL_ARITH_TAC) in
  REAL_RAT_LE_CONV ORELSEC
  (BINOP_CONV REAL_RAT5_OF_RAT_CONV THENC
   GEN_REWRITE_CONV I [pth] THENC
   REAL_RAT_REDUCE_CONV);;
```

### Informal statement
The theorem `REAL_RAT5_LE_CONV` provides a tactic for proving inequalities between expressions of the form `a + b * sqrt(5)`, where `a` and `b` are rational numbers. Specifically, it states that `(a1 + b1 * sqrt(5)) <= (a2 + b2 * sqrt(5))` is equivalent to one of the following three conditions:

1.  `a1 <= a2` and `b1 <= b2`
2.  `a2 <= a1` and `b1 <= b2` and `(a1 - a2)^2 <= 5 * (b2 - b1)^2`
3.  `a1 <= a2` and `b2 <= b1` and `5 * (b2 - b1)^2 <= (a1 - a2)^2`

It achieves this by leveraging a preliminary lemma that characterizes when `x <= y * sqrt(5)` for real numbers `x` and `y`.

### Informal sketch
The proof proceeds in the following stages:

-   First, the lemma `!x y. x <= y * sqrt(&5) <=> x <= &0 /\ &0 <= y \/ &0 <= x /\ &0 <= y /\ x pow 2 <= &5 * y pow 2 \/ x <= &0 /\ y <= &0 /\ &5 * y pow 2 <= x pow 2` is proved. This lemma handles the comparison of a real number `x` with a multiple of `sqrt(5)`. The proof involves rewriting using `SQRT_POW_2` and `REAL_POS`. It then uses `REAL_LE_SQUARE_ABS` and properties of square roots to arrive at the disjunctive normal form.

-   Second, having proved the lemma, it proves the main equivalence: `(a1 + b1 * sqrt(&5)) <= (a2 + b2 * sqrt(&5)) <=> a1 <= a2 /\ b1 <= b2 \/ a2 <= a1 /\ b1 <= b2 /\ (a1 - a2) pow 2 <= &5 * (b2 - b1) pow 2 \/ a1 <= a2 /\ b2 <= b1 /\ &5 * (b2 - b1) pow 2 <= (a1 - a2) pow 2`. This is done by rewriting the inequality `a1 + b1 * sqrt(5) <= a2 + b2 * sqrt(5)` as `a1 - a2 <= (b2 - b1) * sqrt(5)`, and then applying the previously proved lemma. `REAL_ARITH_TAC` is used to handle arithmetic simplification.

-   Finally, `REAL_RAT_LE_CONV` is tried which converts the real numbers to rationals. If that doesn't work, the proof tries to convert the real numbers to `REAL_RAT5` using `REAL_RAT5_OF_RAT_CONV`. It then rewrites with the proved equivalence `pth` and then `REAL_RAT_REDUCE_CONV`

### Mathematical insight
This theorem provides a decision procedure for comparing numbers in the extension field `Q[sqrt(5)]`. It transforms the inequality into a set of inequalities involving only rational numbers, which can then be efficiently decided. The main lemma deals with the relation `x <= y * sqrt(5)`, and the overall theorem uses rewriting and arithmetic tactics to simplify the initial inequality.

### Dependencies
- `SQRT_POW_2`
- `REAL_POS`
- `REAL_POW_MUL`
- `REAL_LE_SQUARE_ABS`
- `REAL_LE_MUL_EQ`
- `SQRT_POS_LT`
- `REAL_OF_NUM_LT`
- `ARITH`
- `REAL_ARITH`
- `REAL_RAT5_OF_RAT_CONV`
- `REAL_RAT_LE_CONV`
- `REAL_RAT_REDUCE_CONV`


---

## REAL_RAT5_EQ_CONV

### Name of formal statement
REAL_RAT5_EQ_CONV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REAL_RAT5_EQ_CONV =
  GEN_REWRITE_CONV I [GSYM REAL_LE_ANTISYM] THENC
  BINOP_CONV REAL_RAT5_LE_CONV THENC
  GEN_REWRITE_CONV I [AND_CLAUSES];;
```
### Informal statement
The theorem `REAL_RAT5_EQ_CONV` states that the equality of real numbers represented as pairs of natural numbers (rationals) is convertible by first applying the antisymmetry property of the less-than-or-equal-to relation (`REAL_LE_ANTISYM`), then converting the binary operation with `REAL_RAT5_LE_CONV`, and finally rewriting with the clauses of the `AND` operator.

### Informal sketch
The proof strategy unfolds as follows:

- Apply the antisymmetry of the less-than-or-equal relation (`REAL_LE_ANTISYM`). This step rewrites an equality `x = y` to `(x <= y) /\ (y <= x)`.  The GSYM tactic is used to ensure `REAL_LE_ANTISYM` is applied in the correct direction.
- Convert the resulting binary operators. `BINOP_CONV REAL_RAT5_LE_CONV` converts each of the `<=` relations into corresponding representations for real numbers represented as pairs of natural numbers and eliminates the existential quantifiers from the definition of `REAL_RAT5_LE_CONV`.
- Simplify the resulting conjunction using the associativity, commutativity, and identity properties of conjunction, represented by `AND_CLAUSES`.

### Mathematical insight
This theorem bridges the gap between the abstract notion of equality for real numbers represented as pairs of natural numbers and a more concrete, computational representation using inequalities between pairs of natural numbers. It leverages the antisymmetry property of order and the concrete definition of the less-than-or-equal-to relation for this representation. The final simplification step makes the condition more amenable to automated reasoning.

### Dependencies
- `REAL_LE_ANTISYM`
- `REAL_RAT5_LE_CONV`
- `AND_CLAUSES`


---

## VECTOR3_SUB_CONV

### Name of formal statement
VECTOR3_SUB_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VECTOR3_SUB_CONV =
  let pth = prove
   (`vector[x1;x2;x3] - vector[y1;y2;y3]:real^3 =
     vector[x1-y1; x2-y2; x3-y3]`,
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    REWRITE_TAC[VECTOR_3; VECTOR_SUB_COMPONENT]) in
  GEN_REWRITE_CONV I [pth] THENC RAND_CONV(LIST_CONV REAL_RAT5_SUB_CONV);;
```

### Informal statement
For any real numbers `x1`, `x2`, `x3`, `y1`, `y2`, and `y3`, the vector with components `x1`, `x2`, `x3` minus the vector with components `y1`, `y2`, `y3` is equal to the vector with components `x1-y1`, `x2-y2`, `x3-y3`. This equality is then converted into a conversion. Each element of the vector is converted into an element lying in `Q[sqrt(5)]`.

### Informal sketch
- Prove the main equality `vector[x1;x2;x3] - vector[y1;y2;y3] = vector[x1-y1; x2-y2; x3-y3]` using simplification and rewriting.
  - Simplify the equality using `CART_EQ`, `DIMINDEX_3`, and `FORALL_3`.
  - Rewrite using `VECTOR_3` and `VECTOR_SUB_COMPONENT`.
- Convert the proved theorem into a conversion using `GEN_REWRITE_CONV`.
- Apply `REAL_RAT5_SUB_CONV` to each component of the vector using `LIST_CONV` and `RAND_CONV`.

### Mathematical insight
This theorem provides a way to compute the difference of two 3D vectors by subtracting corresponding components. The conversion part then rewrites each component of the vector difference, from a real number into an element in `Q[sqrt(5)]`. This rewrite is performed by mapping `REAL_RAT5_SUB_CONV` into the list forming the vector.

### Dependencies
- `CART_EQ`
- `DIMINDEX_3`
- `FORALL_3`
- `VECTOR_3`
- `VECTOR_SUB_COMPONENT`
- `REAL_RAT5_SUB_CONV`


---

## VECTOR3_CROSS_CONV

### Name of formal statement
VECTOR3_CROSS_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VECTOR3_CROSS_CONV =
  let pth = prove
   (`(vector[x1;x2;x3]) cross (vector[y1;y2;y3]) =
     vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1]`,
    REWRITE_TAC[cross; VECTOR_3]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(LIST_CONV(BINOP_CONV REAL_RAT5_MUL_CONV THENC REAL_RAT5_SUB_CONV));;
```

### Informal statement
The cross product of two three-dimensional vectors, `vector[x1; x2; x3]` and `vector[y1; y2; y3]`, is equal to the vector `vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1]`.

### Informal sketch
- First, a theorem `pth` is proved. The theorem states the formula for the cross product of two 3D vectors given their components.  The proof relies on rewriting using the definition of `cross` and the definition of `VECTOR_3`.
- The theorem `pth` is then used to create a conversion using `GEN_REWRITE_CONV I [pth]`. This conversion will rewrite any expression matching the left-hand side of `pth` with the right-hand side.
- Finally, a conversion is constructed to perform arithmetic simplification on the components of the resulting vector using `RAND_CONV(LIST_CONV(BINOP_CONV REAL_RAT5_MUL_CONV THENC REAL_RAT5_SUB_CONV))`. This simplifies arithmetic expressions which will resolve expressions over rational numbers.

### Mathematical insight
This theorem provides a concrete, component-wise definition of the cross product of two 3D vectors, making it directly computable. The cross product is a fundamental operation in 3D geometry and linear algebra, with applications in physics (e.g., torque, angular momentum) and computer graphics.

### Dependencies
- Constants: `cross`
- Theorems: `VECTOR_3`

### Porting notes (optional)
- Most proof assistants have built-in support for vector operations or provide libraries for linear algebra.  The key is to ensure that the definition of the cross product is consistent with this formalization.
- The arithmetic simplification step using `REAL_RAT5_MUL_CONV` and `REAL_RAT5_SUB_CONV` might need adaptation depending on how the target proof assistant handles rational number arithmetic and rewriting. Some systems may have dedicated tactics or functions which can evaluate expressions over the rationals automatically.


---

## VECTOR3_EQ_0_CONV

### Name of formal statement
VECTOR3_EQ_0_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VECTOR3_EQ_0_CONV =
  let pth = prove
   (`vector[x1;x2;x3]:real^3 = vec 0 <=>
        x1 = &0 /\ x2 = &0 /\ x3 = &0`,
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    REWRITE_TAC[VECTOR_3; VEC_COMPONENT]) in
  GEN_REWRITE_CONV I [pth] THENC
  DEPTH_BINOP_CONV `(/\)` REAL_RAT5_EQ_CONV THENC
  REWRITE_CONV[];;
```

### Informal statement
The vector `[x1; x2; x3]` of real numbers, where the vector is in 3-dimensional real space, is equal to the zero vector `vec 0` if and only if `x1` equals `&0` and `x2` equals `&0` and `x3` equals `&0`.

### Informal sketch
- First, a theorem `pth` is proved stating that a 3D vector is equal to the zero vector if and only if each of its components is equal to zero. This proof is conducted using simplification (`SIMP_TAC`) with the following theorems: `CART_EQ` (Cartesian equality), `DIMINDEX_3` (dimension index for 3), and `FORALL_3` (universal quantifier for 3). The simplification is followed by a rewrite using the theorems `VECTOR_3` and `VEC_COMPONENT`.
- Then, a general rewrite conversion `GEN_REWRITE_CONV` is created using the theorem `pth`.
- After that, a depth-first binary operation conversion `DEPTH_BINOP_CONV` is applied to the `(/\)` operator, using the `REAL_RAT5_EQ_CONV` conversion.
- Finally, a simple rewrite conversion `REWRITE_CONV` is applied with an empty list of theorems.

### Mathematical insight
This theorem provides a fundamental characterization of vector equality with the zero vector in 3-dimensional space. It states that for a vector to be the zero vector, all of its components must be zero. This is a basic result in linear algebra. The `VECTOR3_EQ_0_CONV` theorem likely facilitates simplification of vector equations within HOL Light by providing a mechanism for reducing vector equalities to equalities of their components.

### Dependencies
- Definitions:
  - `VECTOR_3`
  - `VEC_COMPONENT`
- Theorems:
  - `CART_EQ`
  - `DIMINDEX_3`
  - `FORALL_3`
  - `REAL_RAT5_EQ_CONV`


---

## VECTOR3_DOT_CONV

### Name of formal statement
VECTOR3_DOT_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VECTOR3_DOT_CONV =
  let pth = prove
   (`(vector[x1;x2;x3]:real^3) dot (vector[y1;y2;y3]) =
        x1*y1 + x2*y2 + x3*y3`,
    REWRITE_TAC[DOT_3; VECTOR_3]) in
  GEN_REWRITE_CONV I [pth] THENC
  DEPTH_BINOP_CONV `(+):real->real->real` REAL_RAT5_MUL_CONV THENC
  RAND_CONV REAL_RAT5_ADD_CONV THENC
  REAL_RAT5_ADD_CONV;;
```

### Informal statement
The dot product of two 3-dimensional real vectors, `vector[x1; x2; x3]` and `vector[y1; y2; y3]`, is equal to `x1*y1 + x2*y2 + x3*y3`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the expression using the definitions of `DOT_3` and `VECTOR_3`.
- Then, apply a conversion that simplifies the expression by repeatedly applying `REAL_RAT5_MUL_CONV` within the scope of the addition operator `(+)`.
- Subsequently, apply `REAL_RAT5_ADD_CONV` to the right argument.
- Finally, apply `REAL_RAT5_ADD_CONV` to simplify further.

### Mathematical insight
This theorem provides a concrete, computational definition of the dot product for 3-dimensional real vectors. It is a fundamental result that allows for calculating the dot product given the vector components.

### Dependencies
- `DOT_3`
- `VECTOR_3`
- `REAL_RAT5_MUL_CONV`
- `REAL_RAT5_ADD_CONV`


---

## STD_DODECAHEDRON

### Name of formal statement
STD_DODECAHEDRON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_DODECAHEDRON = prove
 (`std_dodecahedron =
   convex hull
    { vector[&1; &1; &1],
      vector[&1; &1; -- &1],
      vector[&1; -- &1; &1],
      vector[&1; -- &1; -- &1],
      vector[-- &1; &1; &1],
      vector[-- &1; &1; -- &1],
      vector[-- &1; -- &1; &1],
      vector[-- &1; -- &1; -- &1],
      vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)]}`,
  let golden_inverse = prove
   (`inv((&1 + sqrt(&5)) / &2) = -- &1 / &2 + &1 / &2 * sqrt(&5)`,
    MP_TAC(ISPEC `&5` SQRT_POW_2) THEN CONV_TAC REAL_FIELD) in
  REWRITE_TAC[std_dodecahedron] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[golden_inverse] THEN
  REWRITE_TAC[REAL_ARITH `(&1 + s) / &2 = &1 / &2 + &1 / &2 * s`] THEN
  REWRITE_TAC[REAL_ARITH `--(a + b * sqrt(&5)) = --a + --b * sqrt(&5)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;
```

### Informal statement
The points
(1, 1, 1), (1, 1, -1), (1, -1, 1), (1, -1, -1), (-1, 1, 1), (-1, 1, -1), (-1, -1, 1), (-1, -1, -1), (0, -1/2 + 1/2 * sqrt(5), 1/2 + 1/2 * sqrt(5)), (0, -1/2 + 1/2 * sqrt(5), -1/2 + -1/2 * sqrt(5)), (0, 1/2 + -1/2 * sqrt(5), 1/2 + 1/2 * sqrt(5)), (0, 1/2 + -1/2 * sqrt(5), -1/2 + -1/2 * sqrt(5)), (-1/2 + 1/2 * sqrt(5), 1/2 + 1/2 * sqrt(5), 0), (-1/2 + 1/2 * sqrt(5), -1/2 + -1/2 * sqrt(5), 0), (1/2 + -1/2 * sqrt(5), 1/2 + 1/2 * sqrt(5), 0), (1/2 + -1/2 * sqrt(5), -1/2 + -1/2 * sqrt(5), 0), (1/2 + 1/2 * sqrt(5), 0, -1/2 + 1/2 * sqrt(5)), (-1/2 + -1/2 * sqrt(5), 0, -1/2 + 1/2 * sqrt(5)), (1/2 + 1/2 * sqrt(5), 0, 1/2 + -1/2 * sqrt(5)), (-1/2 + -1/2 * sqrt(5), 0, 1/2 + -1/2 * sqrt(5))
are the vertices of a standard dodecahedron, where a `standard dodecahedron` is defined as the `convex hull` of the mentioned vertices.

### Informal sketch
The proof establishes that the vertices listed define a standard dodecahedron by showing that the `std_dodecahedron`, which is defined as the `convex hull` of the listed vectors, is equivalent to the `convex hull` of the same vertices with irrational coordinates expressed in the `standard form`.
- First a lemma `golden_inverse` which states that `inv((&1 + sqrt(&5)) / &2) = -- &1 / &2 + &1 / &2 * sqrt(&5)` is proved using `SQRT_POW_2` and simplification with `REAL_FIELD`.
- The proof starts by rewriting the definition of `std_dodecahedron`.
- The `let` binder is expanded once.
- The `golden_inverse` lemma is applied to rewrite the inverse relation
- The expression `(&1 + s) / &2 = &1 / &2 + &1 / &2 * s` and `--(a + b * sqrt(&5)) = --a + --b * sqrt(&5)` are used to rewrite the real arithmetic.
- Finally the `REAL_RAT_REDUCE_CONV` tactic is applied to reduce rational expressions.

### Mathematical insight
This theorem provides a concrete definition of a standard dodecahedron in terms of the convex hull of its vertices, where the coordinates of the vertices are explicitly given. The vertices are chosen such that the dodecahedron is centered at the origin and has a specific orientation. This definition is fundamental when reasoning about the properties and relationships of the standard dodecahedron within the formal theory.

### Dependencies
- `convex hull`
- `SQRT_POW_2`
- `REAL_FIELD`
- `REAL_ARITH`
- `REAL_RAT_REDUCE_CONV`

### Porting notes (optional)
- The `SQRT_POW_2` is theorem which states that if `0 <= x` then `sqrt(x pow 2) = x`
- Convex hull needs to be already defined.
- The `REAL_FIELD` and `REAL_RAT_REDUCE_CONV` are tactics to automatize simplification in the real field. These tactics are essential for managing the complexities of real number arithmetic, especially when dealing with irrational numbers like `sqrt(5)`. A similar mechanism for real simplification would need to be available in the target proof assistant for a smooth port.


---

## STD_ICOSAHEDRON

### Name of formal statement
STD_ICOSAHEDRON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_ICOSAHEDRON = prove
 (`std_icosahedron =
   convex hull
    { vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)],
      vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)],
      vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0],
      vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1],
      vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1],
      vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]}`,
  REWRITE_TAC[std_icosahedron] THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REAL_ARITH `(&1 + s) / &2 = &1 / &2 + &1 / &2 * s`] THEN
  REWRITE_TAC[REAL_ARITH `--(a + b * sqrt(&5)) = --a + --b * sqrt(&5)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;
```

### Informal statement
The standard icosahedron, denoted `std_icosahedron`, is equal to the convex hull of the set containing the following twelve vectors in three-dimensional real space:
(0, 1, 1/2 + 1/2 * sqrt(5)), (0, 1, -1/2 - 1/2 * sqrt(5)), (0, -1, 1/2 + 1/2 * sqrt(5)), (0, -1, -1/2 - 1/2 * sqrt(5)), (1, 1/2 + 1/2 * sqrt(5), 0), (1, -1/2 - 1/2 * sqrt(5), 0), (-1, 1/2 + 1/2 * sqrt(5), 0), (-1, -1/2 - 1/2 * sqrt(5), 0), (1/2 + 1/2 * sqrt(5), 0, 1), (-1/2 - 1/2 * sqrt(5), 0, 1), (1/2 + 1/2 * sqrt(5), 0, -1), (-1/2 - 1/2 * sqrt(5), 0, -1).

### Informal sketch
The proof proceeds as follows:
- First, rewrite the initial goal using the definition of `std_icosahedron`.
- Expand the let bindings (likely introduced during the definition of `std_icosahedron`) using `ONCE_DEPTH_CONV let_CONV`.
- Rewrite using the arithmetic identities `(1 + s) / 2 = 1/2 + 1/2 * s` and `--(a + b * sqrt(5)) = --a + --b * sqrt(5)`.
- Reduce rational expressions appearing in the vectors using `REAL_RAT_REDUCE_CONV`.
- Apply `REWRITE_TAC[]` to simplify the expression using previously proved facts and definitions.

### Mathematical insight
This theorem provides a concrete definition of the standard icosahedron as the convex hull of a specific set of 12 vertices. These vertices are chosen to ensure certain symmetries and properties of the icosahedron. The choice of the golden ratio (related to `sqrt(5)`) in the coordinates is a key element in obtaining the icosahedral symmetry.

### Dependencies
- Definitions:
  - `std_icosahedron`
  - `convex hull`
  - `vector`
- Theorems/Lemmas:
  - `REAL_ARITH \`(&1 + s) / &2 = &1 / &2 + &1 / &2 * s\``
  - `REAL_ARITH \`--(a + b * sqrt(&5)) = --a + --b * sqrt(&5))\``

### Porting notes (optional)
- Porting this result requires that the target proof assistant have a library for convex hulls and vectors in real 3D space. The handling of real arithmetic and square roots is also essential.
- Care may be required to handle the automatic simplification of arithmetic expressions, as `REAL_RAT_REDUCE_CONV` and `REWRITE_TAC[]` can perform complex simplifications automatically in HOL Light. Other systems may require manual intervention to achieve similar results.


---

## COMPUTE_FACES_2

### Name of formal statement
COMPUTE_FACES_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPUTE_FACES_2 = prove
 (`!f s:real^3->bool.
        FINITE s
        ==> (f face_of (convex hull s) /\ aff_dim f = &2 <=>
             ?x y z. x IN s /\ y IN s /\ z IN s /\
                     let a = (z - x) cross (y - x) in
                     ~(a = vec 0) /\
                     let b = a dot x in
                     ((!w. w IN s ==> a dot w <= b) \/
                      (!w. w IN s ==> a dot w >= b)) /\
                     f = convex hull (s INTER {x | a dot x = b}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?t:real^3->bool. t SUBSET s /\ f = convex hull t`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_CONVEX_HULL_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMP_COMPACT];
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` MP_TAC)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_CONVEX_HULL]) THEN
    MP_TAC(ISPEC `t:real^3->bool` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^3->bool) HAS_SIZE 3` MP_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN MATCH_MP_TAC(INT_ARITH
       `aff_dim(u:real^3->bool) = &2 /\ aff_dim u = &(CARD u) - &1
        ==> &(CARD u):int = &3`) THEN CONJ_TAC
      THENL [ASM_MESON_TAC[AFF_DIM_AFFINE_HULL]; ASM_MESON_TAC[AFF_DIM_UNIQUE]];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC  [`x:real^3`; `y:real^3`; `z:real^3`] THEN
    REPLICATE_TAC 3 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REPEAT LET_TAC THEN
    SUBGOAL_THEN `~collinear{x:real^3,y,z}` MP_TAC THENL
     [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[SET_RULE `{x,y,z} = {z,x,y}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN ASM_REWRITE_TAC[GSYM CROSS_EQ_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^3) dot y = b /\ (a:real^3) dot z = b`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(z - x) cross (y - x) = a`; `(a:real^3) dot x = b`] THEN VEC3_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`convex hull s:real^3->bool`; `convex hull t:real^3->bool`]
        EXPOSED_FACE_OF_POLYHEDRON) THEN
    ASM_SIMP_TAC[POLYHEDRON_CONVEX_HULL; exposed_face_of] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':real^3`; `b':real`] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    SUBGOAL_THEN
     `aff_dim(t:real^3->bool)
      <= aff_dim({x:real^3 | a dot x = b} INTER {x | a' dot x = b'})`
    MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       [SYM th]) THEN
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull t:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFF_DIM_HYPERPLANE;
                 AFFINE_HYPERPLANE; DIMINDEX_3] THEN
    REPEAT(COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SUBSET_HYPERPLANES]) THEN
    ASM_REWRITE_TAC[HYPERPLANE_EQ_EMPTY] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (MP_TAC o SYM)) THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[INTER_UNIV]) THEN
      SUBGOAL_THEN `s SUBSET {x:real^3 | a dot x = b}` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull s:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `affine hull t:real^3->bool` THEN
        REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
        ASM_SIMP_TAC[real_ge; REAL_LE_REFL];
        ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`]];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; real_ge; REAL_NOT_LE] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_TAC `u:real^3`) (X_CHOOSE_TAC `v:real^3`)) THEN
      SUBGOAL_THEN `(a':real^3) dot u < b' /\ a' dot v < b'` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_LE] THEN REWRITE_TAC
         [SET_RULE `f x <= b /\ ~(f x = b) <=>
                    x IN {x | f x <= b} /\ ~(x IN {x | f x = b})`] THEN
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_NE] THEN
        SUBGOAL_THEN `(u:real^3) IN convex hull s /\ v IN convex hull s`
        MP_TAC THENL [ASM_SIMP_TAC[HULL_INC]; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `?w:real^3. w IN segment[u,v] /\ w IN {w | a' dot w = b'}`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
        MAP_EVERY EXISTS_TAC [`v:real^3`; `u:real^3`] THEN
        ASM_SIMP_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT; REAL_LT_IMP_LE];
        REWRITE_TAC[IN_SEGMENT; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
        ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
        REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
        REWRITE_TAC[UNWIND_THM2; DOT_RADD; DOT_RMUL; CONJ_ASSOC] THEN
        DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
        MATCH_MP_TAC(REAL_ARITH `a < b ==> a = b ==> F`) THEN
        MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET_INTER] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull t:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        REWRITE_TAC[SUBSET_INTER] THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
        REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE]]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
    REPEAT LET_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `convex hull (s INTER {x:real^3 | a dot x = b}) =
        (convex hull s) INTER {x | a dot x = b}`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [SIMP_TAC[SUBSET_INTER; HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
          SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
          REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE];
        ALL_TAC] THEN
      ASM_CASES_TAC `s SUBSET {x:real^3 | a dot x = b}` THENL
       [ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`] THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
       `convex hull (convex hull (s INTER {x:real^3 | a dot x = b}) UNION
                     convex hull (s DIFF {x | a dot x = b})) INTER
        {x | a dot x = b}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `s SUBSET t ==> (s INTER u) SUBSET (t INTER u)`) THEN
        MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC(SET_RULE
         `s INTER t SUBSET (P hull (s INTER t)) /\
          s DIFF t SUBSET (P hull (s DIFF t))
          ==> s SUBSET (P hull (s INTER t)) UNION (P hull (s DIFF t))`) THEN
        REWRITE_TAC[HULL_SUBSET];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CONVEX_HULL_UNION_NONEMPTY_EXPLICIT o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC[CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY] THEN ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`p:real^3`; `u:real`; `q:real^3`] THEN
      REPLICATE_TAC 4 DISCH_TAC THEN ASM_CASES_TAC `u = &0` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - &0) % p + &0 % q:real^N = p`] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x < y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * q < u * b
          ==> (&1 - u) * p + u * q < b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q < b <=> q IN {x | a dot x < b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LT] THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; REAL_LT_LE]];
        MATCH_MP_TAC(REAL_ARITH `x > y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * b < u * q
          ==> (&1 - u) * p + u * q > b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM real_gt]] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q > b <=> q IN {x | a dot x > b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GT] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; real_gt; REAL_LT_LE]]];
        ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
        MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]];
      REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_TRANS THEN
        EXISTS_TAC `aff_dim {x:real^3 | a dot x = b}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
          SET_TAC[];
          ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN INT_ARITH_TAC];
        MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim {x:real^3,y,z}` THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `~collinear{x:real^3,y,z}` MP_TAC THENL
           [ONCE_REWRITE_TAC[SET_RULE `{x,y,z} = {z,x,y}`] THEN
            ONCE_REWRITE_TAC[COLLINEAR_3] THEN
            ASM_REWRITE_TAC[GSYM CROSS_EQ_0];
            REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
            STRIP_TAC] THEN
          ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
          SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
          CONV_TAC INT_REDUCE_CONV;
          MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN
          REWRITE_TAC[EMPTY_SUBSET] THEN REPEAT CONJ_TAC THEN
          MATCH_MP_TAC HULL_INC THEN
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
          MAP_EVERY UNDISCH_TAC
           [`(z - x) cross (y - x) = a`; `(a:real^3) dot x = b`] THEN
          VEC3_TAC]]]]);;
```

### Informal statement
For all `f` of type `real^3 -> bool` and all `s` of type `real^3 -> bool`, if `s` is finite, then `f` is a face of the convex hull of `s` and the affine dimension of `f` is equal to 2 if and only if there exist points `x`, `y`, and `z` such that each of `x`, `y`, and `z` is in `s`, the cross product of `(z - x)` and `(y - x)` which is assigned to `a` is not the zero vector, letting `b` be the dot product of `a` and `x`, either for all `w`, if `w` is in `s` then the dot product of `a` and `w` is less than or equal to `b` or for all `w`, if `w` is in `s` then the dot product of `a` and `w` is greater than or equal to `b`, and `f` is equal to the convex hull of the intersection of `s` and the set of all `x` such that the dot product of `a` and `x` is equal to `b`.

### Informal sketch
The proof establishes the equivalence between a set `f` being a 2-dimensional face of the convex hull of a finite set `s` and the existence of three points in `s` that define a plane which supports the convex hull of `s` and intersects it precisely at `f`.

- It starts by assuming `f` is a face of `convex hull s` and `aff_dim f = &2`, and aims to show existence of `x`, `y`, `z` satisfying the dot product conditions.
    - A subset `t` of `s` is chosen such that `f = convex hull t` holds, leveraging `FACE_OF_CONVEX_HULL_SUBSET` and the assumption `f face_of convex hull s`.
    - Since `aff_dim f = &2`, and `f = convex hull t`, `aff_dim (convex hull t) = &2`.
    - By `AFFINE_BASIS_EXISTS`, an affine basis `u` for `t` can be found. It must contain three elements because the affine dimension of `t` is 2.
    - The set `u` `HAS_SIZE 3` is shown.
    - Points `x`, `y`, and `z` are chosen from `u`.
    - It's proven that `x`, `y`, and `z` are not collinear, meaning they are affinely independent.
    - A vector `a` is defined as the cross product of `(z - x)` and `(y - x)`, and `b` is defined as the dot product of `a` and `x`.
    - It is shown that `(a dot y = b) /\ (a dot z = b)`.
    - `EXPOSED_FACE_OF_POLYHEDRON` is used to express the face `f` in terms of a supporting hyperplane.
    - Using the `AFF_DIM_AFFINE_INTER_HYPERPLANE` theorem, it is shown that if the intersection of `t` and the hyperplane defined by `a` and `b` equals `t` then `s SUBSET {x | a dot x = b}`.
    - Using `CONNECTED_IVT_HYPERPLANE` it will follow that `s SUBSET {x | a dot x = b}` can be reduced to contradiction.
    - The contrapositive direction involves proving that if the stated conditions about `x`, `y`, `z`, `a`, and `b` hold, then `f` is a face of `convex hull s` with affine dimension 2. Utilizing the face of intersection with supporting hyperplane property.

### Mathematical insight
This theorem provides a concrete way to compute the 2-dimensional faces (facets) of the convex hull of a finite set of points in 3D space. It shows that such a face can be defined by three points from the original set, lying on a plane that supports the convex hull.

### Dependencies
- `FINITE`
- `FACE_OF_CONVEX_HULL_SUBSET`
- `FINITE_IMP_COMPACT`
- `AFF_DIM_CONVEX_HULL`
- `AFFINE_BASIS_EXISTS`
- `HAS_SIZE`
- `AFFINE_INDEPENDENT_IMP_FINITE`
- `AFF_DIM_AFFINE_HULL`
- `AFF_DIM_UNIQUE`
- `COLLINEAR_3_EQ_AFFINE_DEPENDENT`
- `COLLINEAR_3`
- `CROSS_EQ_0`
- `EXPOSED_FACE_OF_POLYHEDRON`
- `POLYHEDRON_CONVEX_HULL`
- `exposed_face_of`
- `AFF_DIM_AFFINE_INTER_HYPERPLANE`
- `AFF_DIM_HYPERPLANE`
- `AFFINE_HYPERPLANE`
- `DIMINDEX_3`
- `SUBSET_HYPERPLANES`
- `HYPERPLANE_EQ_EMPTY`
- `INTER_UNIV`
- `HULL_SUBSET`
- `CONVEX_HULL_SUBSET_AFFINE_HULL`
- `HULL_MINIMAL`
- `REAL_LE_REFL`
- `CONNECTED_IVT_HYPERPLANE`
- `ENDS_IN_SEGMENT`
- `CONNECTED_SEGMENT`
- `REAL_LT_IMP_LE`
- `UNWIND_THM2`
- `CONVEX_HULL_EQ`
- `CONVEX_HYPERPLANE`
- `CONVEX_HULL_UNION_NONEMPTY_EXPLICIT`
- `CONVEX_CONVEX_HULL`
- `CONVEX_HULL_EQ_EMPTY`
- `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE`
- `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`
- `CONVEX_HALFSPACE_LE`
- `CONVEX_HALFSPACE_GE`
- `INSERT_SUBSET`
- `AFF_DIM_AFFINE_INDEPENDENT`
- `CARD_CLAUSES`
- `FINITE_INSERT`
- `FINITE_EMPTY`

### Porting notes (optional)
- The proof relies heavily on theorems about affine dimension. Ensure the target proof assistant has similar theorems.
- The use of `REAL_ARITH` tactic suggests the need for a robust linear arithmetic solver in the target system.


---

## COMPUTE_FACES_2_STEP_1

### Name of formal statement
COMPUTE_FACES_2_STEP_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPUTE_FACES_2_STEP_1 = prove
 (`!f v s t:real^3->bool.
       (?x y z. x IN (v INSERT s) /\ y IN (v INSERT s) /\ z IN (v INSERT s) /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
       (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) \/
       (?x y z. x IN s /\ y IN s /\ z IN s /\
                let a = (z - x) cross (y - x) in
                ~(a = vec 0) /\
                let b = a dot x in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT] THEN MATCH_MP_TAC(MESON[]
       `(!x y z. Q x y z ==> Q x z y) /\
        (!x y z. Q x y z ==> Q y x z) /\
        (!x z. ~(Q x x z))
        ==> ((?x y z. (x = v \/ P x) /\ (y = v \/ P y) /\ (z = v \/ P z) /\
             Q x y z) <=>
            (?y z. P y /\ P z /\ Q v y z) \/
            (?x y z. P x /\ P y /\ P z /\ Q x y z))`) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[VECTOR_SUB_REFL; CROSS_0] THEN
  CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  MAP_EVERY (SUBST1_TAC o VEC3_RULE)
   [`(z - y) cross (x - y) = --((z - x) cross (y - x))`;
    `(y - x) cross (z - x) =  --((z - x) cross (y - x))`] THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2;
              real_ge] THEN
  REWRITE_TAC[DISJ_ACI] THEN
  REWRITE_TAC[VEC3_RULE
   `((z - x) cross (y - x)) dot y = ((z - x) cross (y - x)) dot x`]);;
```
### Informal statement
For any functions `f`, `v`, `s`, and `t` mapping 3D real vectors to booleans, the following equivalence holds:

The existence of vectors `x`, `y`, and `z` such that `x`, `y`, and `z` are elements of the set formed by inserting `v` into `s`, and, letting `a` be the cross product of `z - x` and `y - x`, `a` is not the zero vector, and, letting `b` be the dot product of `a` and `x`, either for all `w` in `t`, the dot product of `a` and `w` is less than or equal to `b`, or for all `w` in `t`, the dot product of `a` and `w` is greater than or equal to `b`, and `f` is equal to the convex hull of the intersection of `t` and the set of all `x` such that the dot product of `a` and `x` equals `b`

is equivalent to

The existence of vectors `y` and `z` such that `y` and `z` are elements of `s`, and, letting `a` be the cross product of `z - v` and `y - v`, `a` is not the zero vector, and, letting `b` be the dot product of `a` and `v`, either for all `w` in `t`, the dot product of `a` and `w` is less than or equal to `b`, or for all `w` in `t`, the dot product of `a` and `w` is greater than or equal to `b`, and `f` is equal to the convex hull of the intersection of `t` and the set of all `x` such that the dot product of `a` and `x` equals `b`,

or

The existence of vectors `x`, `y`, and `z` such that `x`, `y`, and `z` are elements of `s`, and, letting `a` be the cross product of `z - x` and `y - x`, `a` is not the zero vector, and, letting `b` be the dot product of `a` and `x`, either for all `w` in `t`, the dot product of `a` and `w` is less than or equal to `b`, or for all `w` in `t`, the dot product of `a` and `w` is greater than or equal to `b`, and `f` is equal to the convex hull of the intersection of `t` and the set of all `x` such that the dot product of `a` and `x` equals `b`.

### Informal sketch
The theorem relates the existence of a certain planar configuration involving vectors in `v INSERT s` and the set `t` to the existence of similar configurations where the vectors are restricted to `s`, in the context of convex hulls. The proof proceeds by:

- Expanding the `IN_INSERT` predicate to separate cases.
- Applying a MESON tactic with resolution of first-order logic axioms related to symmetry and irreflexivity.
- Simplifying the resulting terms by substituting definitions introduced by `let_CONV` for vector subtraction and cross product involving zero vectors.
- Rewriting using properties of vector addition and cross products such as `(z - y) cross (x - y) = --((z - x) cross (y - x))` and `(y - x) cross (z - x) = --((z - x) cross (y - x))`.
- Using identities regarding negations, dot products, and real number inequalities (`VECTOR_NEG_EQ_0`, `DOT_LNEG`, `REAL_EQ_NEG2`, `REAL_LE_NEG2`, `real_ge`).
- Applying `DISJ_ACI`, which likely rearranges disjunctions using associativity, commutativity, and idempotence.
- Rewriting using `VEC3_RULE ((z - x) cross (y - x)) dot y = ((z - x) cross (y - x)) dot x`.

### Mathematical insight
The theorem decomposes a problem about finding a face (defined via a convex hull lying on a plane) using a set of points that includes `v` into cases where `v` is explicitly used, or not used at all. The key idea is to analyze the possible arrangements of points that define the plane when one of the points may or may not be `v`. This kind of decomposition of cases where "something is in `v INSERT s`" is common in geometry proofs involving sets.

### Dependencies
- `IN_INSERT`
- `VECTOR_SUB_REFL`
- `CROSS_0`
- `VECTOR_NEG_EQ_0`
- `DOT_LNEG`
- `REAL_EQ_NEG2`
- `REAL_LE_NEG2`
- `real_ge`
- `DISJ_ACI`
- `VEC3_RULE`

### Porting notes (optional)
The reliance on MESON suggests that a significant part of the proof relies on automation for first-order logic reasoning. A similar level of automation may be needed in other proof assistants. The `VEC3_RULE` might require defining corresponding vector algebraic identities in other systems. Tactics like `ONCE_DEPTH_CONV` and `MAP_EVERY` are specific to HOL Light, so one should look into corresponding mechanisms in different proof assistants to apply conversions (i.e., simplification rules) at specific locations/depths within a term. The use of `let_CONV` for substitution should translate directly.


---

## COMPUTE_FACES_2_STEP_2

### Name of formal statement
COMPUTE_FACES_2_STEP_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPUTE_FACES_2_STEP_2 = prove
 (`!f u v s:real^3->bool.
         (?y z. y IN (u INSERT s) /\ z IN (u INSERT s) /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b})) <=>
         (?z. z IN s /\
              let a = (z - v) cross (u - v) in
              ~(a = vec 0) /\
              let b = a dot v in
              ((!w. w IN t ==> a dot w <= b) \/
               (!w. w IN t ==> a dot w >= b)) /\
              f = convex hull (t INTER {x | a dot x = b})) \/
         (?y z. y IN s /\ z IN s /\
                let a = (z - v) cross (y - v) in
                ~(a = vec 0) /\
                let b = a dot v in
                ((!w. w IN t ==> a dot w <= b) \/
                 (!w. w IN t ==> a dot w >= b)) /\
                f = convex hull (t INTER {x | a dot x = b}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT] THEN MATCH_MP_TAC(MESON[]
       `(!x y. Q x y ==> Q y x) /\
        (!x. ~(Q x x))
        ==> ((?y z. (y = u \/ P y) /\ (z = u \/ P z) /\
             Q y z) <=>
            (?z. P z /\ Q u z) \/
            (?y z. P y /\ P z /\ Q y z))`) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[CROSS_REFL] THEN REPEAT GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN SUBST1_TAC
   (VEC3_RULE `(x - v) cross (y - v) = --((y - v) cross (x - v))`) THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0; DOT_LNEG; REAL_EQ_NEG2; REAL_LE_NEG2;
              real_ge] THEN REWRITE_TAC[DISJ_ACI]);;
```
### Informal statement
For any functions `f` and `t` from `real^3` to booleans, and any points `u` and `v` in `real^3`, the following equivalence holds:

There exist points `y` and `z` such that `y` is in the set formed by inserting `u` into `s`, `z` is in the set formed by inserting `u` into `s`, the cross product of `(z - v)` and `(y - v)` is not the zero vector (denoted `vec 0`), and if `a` is defined as this cross product and `b` is the dot product of `a` and `v`, then either for all `w` in `t`, the dot product of `a` and `w` is less than or equal to `b`, or for all `w` in `t`, the dot product of `a` and `w` is greater than or equal to `b`, and `f` is the convex hull of the intersection of `t` and the set of points `x` such that the dot product of `a` and `x` equals `b`;

if and only if

There exists a point `z` such that `z` is in `s`, the cross product of `(z - v)` and `(u - v)` is not the zero vector, and if `a` is defined as this cross product and `b` is the dot product of `a` and `v`, then either for all `w` in `t`, the dot product of `a` and `w` is less than or equal to `b`, or for all `w` in `t`, the dot product of `a` and `w` is greater than or equal to `b`, and `f` is the convex hull of the intersection of `t` and the set of points `x` such that the dot product of `a` and `x` equals `b`;

or

There exist points `y` and `z` such that `y` is in `s`, `z` is in `s`, the cross product of `(z - v)` and `(y - v)` is not the zero vector, and if `a` is defined as this cross product and `b` is the dot product of `a` and `v`, then either for all `w` in `t`, the dot product of `a` and `w` is less than or equal to `b`, or for all `w` in `t`, the dot product of `a` and `w` is greater than or equal to `b`, and `f` is the convex hull of the intersection of `t` and the set of points `x` such that the dot product of `a` and `x` equals `b`.

### Informal sketch
The proof proceeds as follows:
- Apply the tactic `REPEAT GEN_TAC` to discharge the universally bound variables `f`, `u`, `v`, and `s`.
- Rewrite using the definition `IN_INSERT` to expand `y IN (u INSERT s)` and `z IN (u INSERT s)` into disjunctions.
- Apply a resolution step using `MATCH_MP_TAC` and the MESON-discharged lemma which essentially says that `(?y z. (y = u \/ P y) /\ (z = u \/ P z) /\ Q y z)` is equivalent to `(?z. P z /\ Q u z) \/ (?y z. P y /\ P z /\ Q y z)` under certain conditions of `Q`. The conditions are `Q x y ==> Q y x` and `~(Q x x)`
- Apply a conversion tactic (`CONV_TAC`) with `ONCE_DEPTH_CONV let_CONV` to expand the `let` expressions.
- Rewrite using `CROSS_REFL` to simplify `(u - v) cross (u - v)` to `vec 0`. We only rewrite at one level of depth.
- Apply `REPEAT GEN_TAC` to introduce generic quantifiers.
- Apply `CONV_TAC` with `ONCE_DEPTH_CONV let_CONV` to expand the `let` expressions again.
- Perform substitution using `SUBST1_TAC` with `(x - v) cross (y - v) = --((y - v) cross (x - v))` (namely, `VEC3_RULE`).
- Rewrite using `VECTOR_NEG_EQ_0`, `DOT_LNEG`, `REAL_EQ_NEG2`, `REAL_LE_NEG2`, and `real_ge` rewrite rules.
- Rewrite using the associativity, commutativity, and idempotence rules for disjunction (`DISJ_ACI`).

### Mathematical insight
This theorem provides an equivalence that likely helps in the computation or characterization of faces of a convex hull. It explores how the condition of `y` and `z` belonging to `u INSERT s` relates to conditions where either one of them belongs to `s` or both of them belong to `s`. It leverages the cross product and dot product to define a plane, and then considers the convex hull of the intersection of a set `t` with that plane. The theorem probably reduces a computation involving the insertion into `s` to a computation involving only elements of `s`.

### Dependencies

#### Theorems
- `IN_INSERT`
- `VECTOR_NEG_EQ_0`
- `DOT_LNEG`
- `REAL_EQ_NEG2`
- `REAL_LE_NEG2`
- `real_ge`
- `CROSS_REFL`
- `DISJ_ACI`
- `VEC3_RULE`

#### Automation
- MESON

### Porting notes (optional)
- HOL Light's Meson is used to discharge the initial assumption about `Q`, one can use SMT solvers or other automated reasoning tools in other systems.
- The `let_CONV` tactic might have direct counterparts in other systems for expanding `let` expressions.
- Vector arithmetic rules might require specific library imports or definitions in other proof assistants.
- The tactics `REPEAT GEN_TAC` and `REWRITE_TAC` have direct analogies in many proof assistants.


---

## COMPUTE_FACES_TAC

### Name of formal statement
COMPUTE_FACES_TAC

### Type of the formal statement
Tactical

### Formal Content
```ocaml
let COMPUTE_FACES_TAC =
  let lemma = prove
   (`(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}`,
    COND_CASES_TAC THEN ASM SET_TAC[]) in
  SIMP_TAC[COMPUTE_FACES_2; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[COMPUTE_FACES_2_STEP_1] THEN
  REWRITE_TAC[COMPUTE_FACES_2_STEP_2] THEN
  REWRITE_TAC[NOT_IN_EMPTY] THEN
  REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_CROSS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
  REWRITE_TAC[real_ge] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_LE_CONV) THEN
  REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI] THEN
  REPEAT(CHANGED_TAC
   (ONCE_REWRITE_TAC[lemma] THEN
    CONV_TAC(ONCE_DEPTH_CONV
     (LAND_CONV VECTOR3_DOT_CONV THENC REAL_RAT5_EQ_CONV))) THEN
    REWRITE_TAC[]) THEN
  REWRITE_TAC[INTER_EMPTY] THEN
  REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI];;
```

### Informal statement
`COMPUTE_FACES_TAC` is a tactic in HOL Light that aims to compute the faces of a convex polyhedron. It simplifies the goal by applying a series of simplification, rewriting and conversion tactics. It leverages a lemma about intersecting an insertion set with a set defined by a predicate.

### Informal sketch
The tactic `COMPUTE_FACES_TAC` performs a sequence of proof transformations, with the ultimate goal of computing the faces in a geometric construction. The main steps are:

*   **Initial Simplifications:** Start by applying simplification rules related to computing faces (`COMPUTE_FACES_2`), finite sets (`FINITE_INSERT`, `FINITE_EMPTY`).
*   **Rewriting:** Rewrite using results from `COMPUTE_FACES_2_STEP_1` and `COMPUTE_FACES_2_STEP_2`. Rewrite also using basic set theory facts like `NOT_IN_EMPTY`, `EXISTS_IN_INSERT`, `FORALL_IN_INSERT`.
*   **Vector Computations:** Perform conversions to sub-expressions involving vector subtraction (`VECTOR3_SUB_CONV`), cross product (`VECTOR3_CROSS_CONV`), eliminate `let` bindings (`let_CONV`), and check vector equality to zero (`VECTOR3_EQ_0_CONV`).
*   **Real Number Ordering:** Perform conversions based on `real_ge`.
*   **Dot Product:** Perform conversions involving vector dot product `VECTOR3_DOT_CONV` and related operations.
*   **Real Number comparison** Use conversions based on `REAL_RAT5_LE_CONV`
*   **Set Manipulations:** Apply associativity and commutativity laws (`INSERT_AC`, `DISJ_ACI`).
*   **Iterative Refinement:** Repeatedly apply a `CHANGED_TAC` tactic which rewrites the goal with the initial `lemma` (`(x INSERT s) INTER {x | P x} = if P x then x INSERT (s INTER {x | P x}) else s INTER {x | P x}`) and performs some vector dot product reasoning.
*   **Final Simplifications:** Perform final rewrites to remove empty intersections (`INTER_EMPTY`) and cleanup sets (`INSERT_AC`, `DISJ_ACI`).

### Mathematical insight
The tactic implements an algorithm to determine the faces of some geometric object, likely a convex polyhedron. The tactic relies on set-theoretic reasoning (intersections, insertions) combined with vector algebra (subtraction, cross product, dot product) and inequalities. The core lemma suggests manipulating intersections of sets defined by predicates and inserting the elements in the set on if the predicate holds true.

### Dependencies
*   Theorems: `COMPUTE_FACES_2`, `FINITE_INSERT`, `FINITE_EMPTY`, `COMPUTE_FACES_2_STEP_1`, `COMPUTE_FACES_2_STEP_2`, `NOT_IN_EMPTY`, `EXISTS_IN_INSERT`, `FORALL_IN_INSERT`, `real_ge`, `INSERT_AC`, `DISJ_ACI`, `INTER_EMPTY`
*   Conversions: `VECTOR3_SUB_CONV`, `VECTOR3_CROSS_CONV`, `let_CONV`, `VECTOR3_EQ_0_CONV`, `VECTOR3_DOT_CONV`, `REAL_RAT5_LE_CONV`, `LAND_CONV`, `REAL_RAT5_EQ_CONV`

### Porting notes (optional)
*   The tactic relies heavily on rewriting and simplification. Efficient rewriting capabilities are crucial in the target proof assistant.
*   The use of `ONCE_DEPTH_CONV` suggests a need for careful control over the application of conversions.
*   The `CHANGED_TAC` combined with `REPEAT` indicates an iterative application of a tactic until no further change occurs.
*   The lemma proved at the start is crucial and may need to be proved separately in other systems.


---

## TETRAHEDRON_FACETS

### Name of formal statement
TETRAHEDRON_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TETRAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_tetrahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_tetrahedron] THEN COMPUTE_FACES_TAC);;
```

### Informal statement
For all sets `f` of points in 3-dimensional real space, `f` is a face of the standard tetrahedron and the affine dimension of `f` is equal to 2 if and only if `f` is equal to one of the following four convex hulls: the convex hull of the points `(-1, -1, 1)`, `(-1, 1, -1)`, `(1, -1, -1)`; or the convex hull of `(-1, -1, 1)`, `(-1, 1, -1)`, `(1, 1, 1)`; or the convex hull of `(-1, -1, 1)`, `(1, -1, -1)`, `(1, 1, 1)`; or the convex hull of `(-1, 1, -1)`, `(1, -1, -1)`, `(1, 1, 1)`.

### Informal sketch
The proof proceeds by:
- First, rewriting using the definition of `std_tetrahedron`.
- Then, using `COMPUTE_FACES_TAC` which is a tactic to automatically compute the faces of a polyhedron.
The theorem characterises the 2-dimensional faces (facets) of the standard tetrahedron as the convex hulls of the triples of the four vertices of the standard tetrahedron.

### Mathematical insight
This theorem provides a concrete description of the facets (2-dimensional faces) of a standard tetrahedron. It is important for geometric reasoning and can be used to derive properties of tetrahedra and other related structures.

### Dependencies
- `std_tetrahedron`
- `convex hull`
- `aff_dim`
- `face_of`

### Porting notes (optional)
The main challenge is the tactic `COMPUTE_FACES_TAC`. In other proof assistants, this would involve a computational step, possibly requiring some external tool or library. The definition of the standard tetrahedron and convex hulls should be straightforward to translate into most proof assistants. The tactic performs a computation that other provers could perform via external tools. Handling of real numbers and affine dimension may require specific libraries or encodings depending on the target proof assistant.


---

## CUBE_FACETS

### Name of formal statement
CUBE_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBE_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_cube /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1], vector[&1; &1; -- &1], vector[&1; &1; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_cube] THEN COMPUTE_FACES_TAC);;
```
### Informal statement
For all functions `f` from real 3D space to booleans, `f` is a face of the standard cube and the affine dimension of `f` is equal to 2 if and only if `f` is equal to one of the following convex hulls:
1. The convex hull of the vectors `(-1, -1, -1)`, `(-1, -1, 1)`, `(-1, 1, -1)`, `(-1, 1, 1)`.
2. The convex hull of the vectors `(-1, -1, -1)`, `(-1, -1, 1)`, `(1, -1, -1)`, `(1, -1, 1)`.
3. The convex hull of the vectors `(-1, -1, -1)`, `(-1, 1, -1)`, `(1, -1, -1)`, `(1, 1, -1)`.
4. The convex hull of the vectors `(-1, -1, 1)`, `(-1, 1, 1)`, `(1, -1, 1)`, `(1, 1, 1)`.
5. The convex hull of the vectors `(-1, 1, -1)`, `(-1, 1, 1)`, `(1, 1, -1)`, `(1, 1, 1)`.
6. The convex hull of the vectors `(1, -1, -1)`, `(1, -1, 1)`, `(1, 1, -1)`, `(1, 1, 1)`.

### Informal sketch
The proof proceeds as follows:
- It starts with the goal statement.
- It uses `REWRITE_TAC[std_cube]` to expand the definition of the `std_cube`.
- It uses `COMPUTE_FACES_TAC`, an automation tactic, to compute the faces of the standard cube.

### Mathematical insight
This theorem characterizes the 2-dimensional faces (facets) of the standard cube in 3D space. The standard cube is defined as the set of points whose coordinates are all between -1 and 1. The theorem lists all six faces of this cube by specifying the convex hull of their vertices. This is important for geometric reasoning and can be used in algorithms related to 3D modeling or collision detection.

### Dependencies
- Definitions:
    - `std_cube`
- Theorems:
    - (Implicit dependencies within `COMPUTE_FACES_TAC`, relating to convex hulls, affine dimension, and faces of polyhedra.)

### Porting notes (optional)
The main challenge in porting this theorem lies in recreating effect of the `COMPUTE_FACES_TAC`. This tactic likely relies on a combination of geometric reasoning and convex hull computation algorithms. In other proof assistants, one would need to either implement a similar tactic or manually expand the faces and prove the equivalence. Also `vector` is likely defined using real numbers so if another proof assistant lacks this datatype then there will need to be a definition of real numbers and corresponding implementation for it.


---

## OCTAHEDRON_FACETS

### Name of formal statement
OCTAHEDRON_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OCTAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_octahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
        f = convex hull {vector[&1; &0; &0], vector[&0; &1; &0], vector[&0; &0; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_octahedron] THEN COMPUTE_FACES_TAC);;
```
### Informal statement
For all `f` of type real^3 -> bool, `f` is a face of the standard octahedron and the affine dimension of `f` is equal to 2 if and only if
`f` is the convex hull of `{(--1, 0, 0), (0, --1, 0), (0, 0, --1)}` or
`f` is the convex hull of `{(--1, 0, 0), (0, --1, 0), (0, 0, 1)}` or
`f` is the convex hull of `{(--1, 0, 0), (0, 1, 0), (0, 0, --1)}` or
`f` is the convex hull of `{(--1, 0, 0), (0, 1, 0), (0, 0, 1)}` or
`f` is the convex hull of `{(1, 0, 0), (0, --1, 0), (0, 0, --1)}` or
`f` is the convex hull of `{(1, 0, 0), (0, --1, 0), (0, 0, 1)}` or
`f` is the convex hull of `{(1, 0, 0), (0, 1, 0), (0, 0, --1)}` or
`f` is the convex hull of `{(1, 0, 0), (0, 1, 0), (0, 0, 1)}`.

### Informal sketch
The proof proceeds as follows:
- The first step is to rewrite using the definition of `std_octahedron`.
- Then, a tactic called `COMPUTE_FACES_TAC` is applied, which presumably automates the computation of the faces of the octahedron. This step expands the definition of `face_of` and uses properties of `convex hull` to derive the result.

### Mathematical insight
This theorem characterizes the faces of the standard octahedron in 3-dimensional space. It states that a set `f` is a face of the standard octahedron with affine dimension 2 (i.e. a facet) if and only if it is one of the eight triangular faces formed by taking the convex hull of three vertices of the octahedron. The vertices are located at (+/-1, 0, 0), (0, +/-1, 0), and (0, 0, +/-1).

### Dependencies
- Definition: `std_octahedron`
- Definition: `face_of`
- Definition: `convex hull`
- Theorem: `aff_dim`

### Porting notes (optional)
The main challenge in porting this theorem to another proof assistant would likely be recreating the functionality of the `COMPUTE_FACES_TAC` tactic. This tactic seems to automate the computation of the faces of the octahedron, and a similar level of automation may not be available in other systems. The porter might need to expand the definition of `face_of` and use properties of `convex hull` to derive the result manually.


---

## ICOSAHEDRON_FACETS

### Name of formal statement
ICOSAHEDRON_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ICOSAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_icosahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]}`,
  GEN_TAC THEN REWRITE_TAC[STD_ICOSAHEDRON] THEN COMPUTE_FACES_TAC);;
```
### Informal statement
For all `f` which is a function from `real^3` to `bool`, `f` is a face of the standard icosahedron and the affine dimension of `f` equals 2 if and only if `f` equals one of the following convex hulls:
(1) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]`, `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1]`, `[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`;
(2) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]`, `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1]`, `[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`;
(3) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]`, `[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(4) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]`, `[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(5) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1]`, `[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`, `[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(6) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1]`, `[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]`;
(7) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1]`, `[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]`;
(8) the convex hull of the vectors `[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1]`, `[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]`, `[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]`;
(9) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1]`, `[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1]`, `[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`;
(10) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1]`, `[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1]`, `[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`;
(11) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1]`, `[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(12) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1]`, `[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(13) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1]`, `[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`, `[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(14) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1]`, `[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]`;
(15) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1]`, `[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]`;
(16) the convex hull of the vectors `[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1]`, `[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]`, `[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]`;
(17) the convex hull of the vectors `[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(18) the convex hull of the vectors `[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&1; -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0]`, `[&0; -- &1; &1 / &2 + &1 / &2 * sqrt(&5)]`;
(19) the convex hull of the vectors `[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt(&5)]`;
(20) the convex hull of the vectors `[-- &1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&1; &1 / &2 + &1 / &2 * sqrt(&5); &0]`, `[&0; &1; &1 / &2 + &1 / &2 * sqrt(&5)]`.

### Informal sketch
The proof proceeds as follows:
- Using the definition of `STD_ICOSAHEDRON` expands the definition of standard icosahedron in terms of its vertices.
- Applies `COMPUTE_FACES_TAC` which uses computational geometry (specifically, computing convex hulls and their properties) to prove that the enumerated sets of vectors describe all faces of the `std_icosahedron`
- `GEN_TAC` performs general simplification. `REWRITE_TAC` rewrites using the definition of `STD_ICOSAHEDRON`.

### Mathematical insight
The theorem provides a concrete description of the faces of the standard icosahedron. The icosahedron is defined by its vertices and then this theorem identifies all sets of vertices that define each of the 20 faces. This is a key step, showing the faces are exactly as expected from the construction.

### Dependencies
Definitions:
- `STD_ICOSAHEDRON`

Theorems:
- None

Tactics:
- `GEN_TAC`
- `REWRITE_TAC`
- `COMPUTE_FACES_TAC`


---

## DODECAHEDRON_FACETS

### Name of formal statement
DODECAHEDRON_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DODECAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_dodecahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; &1], vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1; -- &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]} \/
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`,
  GEN_TAC THEN REWRITE_TAC[STD_DODECAHEDRON] THEN COMPUTE_FACES_TAC);;
```
### Informal statement
For any `f` which is a subset of real 3D space, `f` is a face of the standard dodecahedron and the affine dimension of `f` is equal to 2 if and only if `f` is equal to one of the 12 convex hulls constructed from the following sets of 5 vectors respectively:
1. `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]}`
2. `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]}`
3. `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; &1], vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]}`
4. `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`
5. `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`
6. `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[-- &1; -- &1; &1], vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]}`
7. `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]}`
8. `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`
9. `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[-- &1; &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]}`
10. `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5); &0], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; &1; -- &1], vector[&1; &1; &1]}`
11. `convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; -- &1 / &2 + &1 / &2 * sqrt(&5)], vector[&1; -- &1; &1], vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); &1 / &2 + &1 / &2 * sqrt(&5)]}`
12. `convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`

### Informal sketch
The proof proceeds by:
- Starting with the goal of characterizing faces of the standard dodecahedron (`std_dodecahedron`) with affine dimension 2.
- Rewriting using the definition of `STD_DODECAHEDRON` to expand the term.
- Applying `COMPUTE_FACES_TAC`. This tactic likely enumerates all possible faces based on the rewritten definition and verifies that they match the stated conditions based on a definition of `face_of`.

### Mathematical insight
The theorem provides a concrete characterization of the faces of the standard dodecahedron in 3D space. Each face is a pentagon, and the theorem gives the vertices for each of the 12 faces. This is a fundamental geometric property of the dodecahedron, essential for reasoning about its structure and properties.

### Dependencies
- `STD_DODECAHEDRON`

### Porting notes (optional)
- The tactic `COMPUTE_FACES_TAC` would need to be reimplemented or an equivalent tactic for computing faces must be employed.
- Ensure the definition of `face_of` is consistent between the source and target proof assistant.


---

## COPLANAR_HYPERPLANE_RULE

### Name of formal statement
COPLANAR_HYPERPLANE_RULE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COPLANAR_HYPERPLANE_RULE =
  let rec allsets m l =
    if m = 0 then [[]] else
    match l with
      [] -> []
    | h::t -> map (fun g -> h::g) (allsets (m - 1) t) @ allsets m t in
  let mk_sub = mk_binop `(-):real^3->real^3->real^3`
  and mk_cross = mk_binop `cross`
  and mk_dot = mk_binop `(dot):real^3->real^3->real`
  and zerovec_tm = `vector[&0;&0;&0]:real^3`
  and template = `(!x:real^3. x IN s ==> n dot x = d)`
  and s_tm = `s:real^3->bool`
  and n_tm = `n:real^3`
  and d_tm = `d:real` in
  let mk_normal [x;y;z] = mk_cross (mk_sub y x) (mk_sub z x) in
  let eval_normal t =
    (BINOP_CONV VECTOR3_SUB_CONV THENC VECTOR3_CROSS_CONV) (mk_normal t) in
  let check_normal t =
    let th = eval_normal t in
    let n = rand(concl th) in
    if n = zerovec_tm then failwith "check_normal" else n in
  fun tm ->
    let s = dest_setenum tm in
    if length s < 3 then failwith "COPLANAR_HYPERPLANE_RULE: trivial" else
    let n = tryfind check_normal (allsets 3 s) in
    let d = rand(concl(VECTOR3_DOT_CONV(mk_dot n (hd s)))) in
    let ptm = vsubst [tm,s_tm; n,n_tm; d,d_tm] template in
    EQT_ELIM
    ((REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY] THENC
      DEPTH_BINOP_CONV `/\`
       (LAND_CONV VECTOR3_DOT_CONV THENC REAL_RAT5_EQ_CONV) THENC
      GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES]) ptm);;
```

### Informal statement
Given a finite set `s` of three-dimensional real vectors, where the cardinality of `s` is greater or equal to 3, the theorem constructs a normal vector `n` and a real number `d` such that for all vectors `x`, if `x` is an element of `s`, then the dot product of `n` and `x` equals `d`. Formally:  `∀x:real^3. x ∈ s ==> n · x = d`.

### Informal sketch
The proof constructs a hyperplane containing the coplanar set `s`.
- The function `allsets m l` generates all subsets of size `m` from the list `l`.
- It constructs a normal vector `n` by iterating through all triples of points in `s`. For each triple `[x;y;z]`, it computes `(y - x) cross (z - x)`. If that vector is not the zero vector, it will keep it as the normal vector for the plane.
- Compute `n` by picking possible triples from the set `s` until a non-zero result is obtained by cross product.
- The value `d` is computed as `n dot x` for any x in `s`.
- Finally, it proves `∀x. x ∈ s ==> n · x = d` by rewriting using the set membership (expands `x IN {x1, ..., xn}` to `x = x1 \/ ... \/ x = xn`), vector subtraction, vector cross product, vector dot product properties and arithmetic simplification to obtain the desired equality.

### Mathematical insight
The theorem formalizes the idea that a set of coplanar points in 3D space lies on a hyperplane, and it provides a way to algorithmically compute the equation of that hyperplane, given the points. By selecting a triple of points, and computing the cross product of two difference vectors, finds a normal to a candidate plane. Then verifies that all points lie on this plane.

### Dependencies
- `FORALL_IN_INSERT`
- `NOT_IN_EMPTY`
- `VECTOR3_SUB_CONV`
- `VECTOR3_CROSS_CONV`
- `VECTOR3_DOT_CONV`
- `REAL_RAT5_EQ_CONV`
- `AND_CLAUSES`


---

## COMPUTE_FACES_1

### Name of formal statement
COMPUTE_FACES_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPUTE_FACES_1 = prove
 (`!s:real^3->bool n d.
        (!x. x IN s ==> n dot x = d)
        ==> FINITE s /\ ~(n = vec 0)
            ==> !f. f face_of (convex hull s) /\ aff_dim f = &1 <=>
                    ?x y. x IN s /\ y IN s /\
                          let a = n cross (y - x) in
                          ~(a = vec 0) /\
                          let b = a dot x in
                          ((!w. w IN s ==> a dot w <= b) \/
                           (!w. w IN s ==> a dot w >= b)) /\
                          f = convex hull (s INTER {x | a dot x = b})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?t:real^3->bool. t SUBSET s /\ f = convex hull t`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_CONVEX_HULL_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMP_COMPACT];
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` MP_TAC)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_CONVEX_HULL]) THEN
    MP_TAC(ISPEC `t:real^3->bool` AFFINE_BASIS_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:real^3->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN MATCH_MP_TAC(INT_ARITH
       `aff_dim(u:real^3->bool) = &1 /\ aff_dim u = &(CARD u) - &1
        ==> &(CARD u):int = &2`) THEN CONJ_TAC
      THENL [ASM_MESON_TAC[AFF_DIM_AFFINE_HULL]; ASM_MESON_TAC[AFF_DIM_UNIQUE]];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC  [`x:real^3`; `y:real^3`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    SUBGOAL_THEN `(x:real^3) IN s /\ y IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT LET_TAC THEN
    MP_TAC(ISPECL [`n:real^3`; `y - x:real^3`] NORM_AND_CROSS_EQ_0) THEN
    ASM_SIMP_TAC[DOT_RSUB; VECTOR_SUB_EQ; REAL_SUB_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:real^3) dot y = b` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`n cross (y - x) = a`; `(a:real^3) dot x = b`] THEN VEC3_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`convex hull s:real^3->bool`; `convex hull t:real^3->bool`]
        EXPOSED_FACE_OF_POLYHEDRON) THEN
    ASM_SIMP_TAC[POLYHEDRON_CONVEX_HULL; EXPOSED_FACE_OF_PARALLEL] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':real^3`; `b':real`] THEN
    SUBGOAL_THEN `~(convex hull t:real^3->bool = {})` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^3` THEN
      MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[]] THEN
    ASM_CASES_TAC `convex hull t:real^3->bool = convex hull s` THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE RAND_CONV
        [GSYM AFFINE_HULL_CONVEX_HULL]) THEN
      UNDISCH_THEN `convex hull t:real^3->bool = convex hull s`
       (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[AFFINE_HULL_CONVEX_HULL]) THEN
      REWRITE_TAC[SET_RULE `s = s INTER t <=> s SUBSET t`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `s SUBSET {x:real^3 | a dot x = b}` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `affine hull s:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        ASM SET_TAC[];
        CONJ_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
          ASM_SIMP_TAC[real_ge; REAL_LE_REFL];
          AP_TERM_TAC THEN ASM SET_TAC[]]];
      STRIP_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFFINE_HULL_CONVEX_HULL]) THEN
    SUBGOAL_THEN
     `aff_dim(t:real^3->bool)
      <= aff_dim(({x:real^3 | a dot x = b} INTER {x:real^3 | a' dot x = b'})
                 INTER {x | n dot x = d})`
    MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM AFF_DIM_AFFINE_HULL] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
       [SYM th]) THEN
      REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
      REWRITE_TAC[SUBSET_INTER; INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN convex hull t /\ y IN convex hull t`
      MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFF_DIM_HYPERPLANE;
                 AFFINE_HYPERPLANE; DIMINDEX_3; AFFINE_INTER] THEN
    ASM_CASES_TAC `{x:real^3 | a dot x = b} SUBSET {v | a' dot v = b'}` THEN
    ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      REPEAT(COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `s INTER t SUBSET u ==> !x. x IN s /\ x IN t ==> x IN u`)) THEN
      DISCH_THEN(MP_TAC o SPEC `x + n:real^3`) THEN
      MATCH_MP_TAC(TAUT `p /\ q /\ ~r ==> (p /\ q ==> r) ==> s`) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; DOT_RADD] THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "a" THEN VEC3_TAC;
        ALL_TAC;
        ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL_0; DOT_EQ_0]] THEN
      SUBGOAL_THEN `a' dot (x:real^3) = b'` SUBST1_TAC THENL
       [SUBGOAL_THEN `(x:real^3) IN convex hull t` MP_TAC THENL
         [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(n:real^3) dot (x + a') = n dot x` MP_TAC THENL
       [ALL_TAC;
        SIMP_TAC[DOT_RADD] THEN REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x:real = d /\ y = d ==> x = y`) THEN
      SUBGOAL_THEN
       `affine hull s SUBSET {x:real^3 | n dot x = d}`
      MP_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_SIMP_TAC[HULL_INC]]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_HYPERPLANES]) THEN
    ASM_REWRITE_TAC[HYPERPLANE_EQ_EMPTY; HYPERPLANE_EQ_UNIV] THEN
    DISCH_THEN(fun th -> DISCH_THEN(K ALL_TAC) THEN MP_TAC(SYM th)) THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; real_ge; REAL_NOT_LE] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_TAC `u:real^3`) (X_CHOOSE_TAC `v:real^3`)) THEN
      SUBGOAL_THEN `(a':real^3) dot u < b' /\ a' dot v < b'` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_LT_LE] THEN REWRITE_TAC
         [SET_RULE `f x <= b /\ ~(f x = b) <=>
                    x IN {x | f x <= b} /\ ~(x IN {x | f x = b})`] THEN
        ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_NE] THEN
        SUBGOAL_THEN `(u:real^3) IN convex hull s /\ v IN convex hull s`
        MP_TAC THENL [ASM_SIMP_TAC[HULL_INC]; ASM SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `?w:real^3. w IN segment[u,v] /\ w IN {w | a' dot w = b'}`
      MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
        MAP_EVERY EXISTS_TAC [`v:real^3`; `u:real^3`] THEN
        ASM_SIMP_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT; REAL_LT_IMP_LE];
        REWRITE_TAC[IN_SEGMENT; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
        ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
        REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
        REWRITE_TAC[UNWIND_THM2; DOT_RADD; DOT_RMUL; CONJ_ASSOC] THEN
        DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
        MATCH_MP_TAC(REAL_ARITH `a < b ==> a = b ==> F`) THEN
        MATCH_MP_TAC REAL_CONVEX_BOUND_LT THEN ASM_REAL_ARITH_TAC];
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET_INTER] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull t:real^3->bool` THEN
        REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[SUBSET_INTER] THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
        SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
        MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
        REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE]]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    REPEAT LET_TAC THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `convex hull (s INTER {x:real^3 | a dot x = b}) =
        (convex hull s) INTER {x | a dot x = b}`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [SIMP_TAC[SUBSET_INTER; HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `convex hull {x:real^3 | a dot x = b}` THEN
          SIMP_TAC[HULL_MONO; INTER_SUBSET] THEN
          MATCH_MP_TAC(SET_RULE `s = t ==> s SUBSET t`) THEN
          REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE];
          ALL_TAC] THEN
      ASM_CASES_TAC `s SUBSET {x:real^3 | a dot x = b}` THENL
       [ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`] THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
       `convex hull (convex hull (s INTER {x:real^3 | a dot x = b}) UNION
                     convex hull (s DIFF {x | a dot x = b})) INTER
        {x | a dot x = b}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `s SUBSET t ==> (s INTER u) SUBSET (t INTER u)`) THEN
        MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC(SET_RULE
         `s INTER t SUBSET (P hull (s INTER t)) /\
          s DIFF t SUBSET (P hull (s DIFF t))
          ==> s SUBSET (P hull (s INTER t)) UNION (P hull (s DIFF t))`) THEN
        REWRITE_TAC[HULL_SUBSET];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) CONVEX_HULL_UNION_NONEMPTY_EXPLICIT o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL
       [SIMP_TAC[CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY] THEN ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER; IMP_CONJ; FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`p:real^3`; `u:real`; `q:real^3`] THEN
      REPLICATE_TAC 4 DISCH_TAC THEN ASM_CASES_TAC `u = &0` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - &0) % p + &0 % q:real^N = p`] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x < y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * q < u * b
          ==> (&1 - u) * p + u * q < b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q < b <=> q IN {x | a dot x < b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LT] THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; REAL_LT_LE]];
        MATCH_MP_TAC(REAL_ARITH `x > y ==> ~(x = y)`) THEN
        MATCH_MP_TAC(REAL_ARITH
         `(&1 - u) * p = (&1 - u) * b /\ u * b < u * q
          ==> (&1 - u) * p + u * q > b`) THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `p IN {x:real^3 | a dot x = b}` MP_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
             `x IN s ==> s SUBSET t ==> x IN t`)) THEN
            MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
            SET_TAC[];
            SIMP_TAC[IN_ELIM_THM]];
          MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; REWRITE_TAC[GSYM real_gt]] THEN
          ONCE_REWRITE_TAC[SET_RULE
           `(a:real^3) dot q > b <=> q IN {x | a dot x > b}`] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GT] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; real_gt; REAL_LT_LE]]];
        ALL_TAC] THEN
      FIRST_X_ASSUM DISJ_CASES_TAC THENL
       [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_LE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
        MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE THEN
        REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
        SIMP_TAC[SET_RULE `(!x. x IN s ==> P x) <=> s SUBSET {x | P x}`] THEN
        MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GE] THEN
        ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]];
      ASM_REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim{x:real^3,y}` THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[AFF_DIM_2] THEN
          ASM_MESON_TAC[CROSS_0; VECTOR_SUB_REFL; INT_LE_REFL];
          MATCH_MP_TAC AFF_DIM_SUBSET THEN
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN
          ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
          MAP_EVERY UNDISCH_TAC
           [`n cross (y - x) = a`; `(a:real^3) dot x = b`] THEN
          VEC3_TAC]] THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC
       `aff_dim({x:real^3 | a dot x = b} INTER {x | n dot x = d})` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INTER_HYPERPLANE; AFFINE_HYPERPLANE;
                   AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN
      REPEAT(COND_CASES_TAC THEN CONV_TAC INT_REDUCE_CONV) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x + n:real^3` o
        GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; DOT_RADD; REAL_EQ_ADD_LCANCEL_0; DOT_EQ_0] THEN
      EXPAND_TAC "a" THEN VEC3_TAC]]);;
```

### Informal statement
For any set `s` of points in 3D real space, a normal vector `n`, and a real number `d`, if every point `x` in `s` satisfies the equation `n dot x = d`, then `s` is finite and `n` is not the zero vector. Moreover, a set `f` is a 1-dimensional face of the convex hull of `s` if and only if there exist points `x` and `y` in `s` such that:
1. The vector `a` defined as the cross product of `n` and `y - x` is not the zero vector.
2. Let `b` be the dot product of `a` and `x`.
3. Either for all `w` in `s`, `a dot w <= b`, or for all `w` in `s`, `a dot w >= b`.
4. `f` is the convex hull of the intersection of `s` with the hyperplane defined by `a dot x = b`.

### Informal sketch
The proof proceeds by showing that if `s` lies in the hyperplane defined by `n dot x = d`, then a 1-dimensional face `f` of the convex hull of `s` is equivalent to the conditions listed in the theorem.

- First, assume that `f` is a 1-dimensional face of `convex hull s`. Then there exists a subset `t` of `s` such that `f = convex hull t`.
- Show that `t` has size 2 using `AFF_DIM_CONVEX_HULL` and `AFFINE_BASIS_EXISTS`. Then `t = {x, y}` for some `x, y` in `s`.
- Define `a = n cross (y - x)` and `b = a dot x`. Show that `a` is non-zero, and either `a dot w <= b` for all `w` in `s` or `a dot w >= b` for all `w` in `s`. Also show that `f = convex hull (s INTER {x | a dot x = b})`.
- The proof uses `EXPOSED_FACE_OF_POLYHEDRON` and shows that the convex hull of `t` is an exposed face (intersection with a supporting hyperplane). It considers the case where the `convex hull t` is equal to the `convex hull s`, derives the required hyperplane properties, and finds suitable `u` and `v` using the intermediate value theorem `CONNECTED_IVT_HYPERPLANE`.
- Conversely, assume the existence of such `x`, `y`, `a`, and `b`. Show that `f = convex hull (s INTER {x | a dot x = b})` is a 1-dimensional face of the convex hull of `s`. This uses `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE` and `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`. The condition on the affine dimension is shown using `AFF_DIM_AFFINE_INTER_HYPERPLANE`.

### Mathematical insight
The theorem provides an explicit characterization of the 1-dimensional faces (edges) of the convex hull of a set of points lying in a hyperplane. The theorem states that an edge exists if we can find a normal vector `a` such that the set is contained in a half-space defined by `a`, with the edge lying on the boundary hyperplane `a dot x = b`.

### Dependencies
- `FACE_OF_CONVEX_HULL_SUBSET`
- `FINITE_IMP_COMPACT`
- `AFF_DIM_CONVEX_HULL`
- `AFFINE_BASIS_EXISTS`
- `HAS_SIZE`
- `AFFINE_INDEPENDENT_IMP_FINITE`
- `NORM_AND_CROSS_EQ_0`
- `EXPOSED_FACE_OF_POLYHEDRON`
- `POLYHEDRON_CONVEX_HULL`
- `EXPOSED_FACE_OF_PARALLEL`
- `AFFINE_HULL_CONVEX_HULL`
- `SUBSET_HYPERPLANES`
- `CONNECTED_IVT_HYPERPLANE`
- `ENDS_IN_SEGMENT`
- `CONNECTED_SEGMENT`
- `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE`
- `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`
- `CONVEX_CONVEX_HULL`
- `CROSS_0`
- `VECTOR_SUB_REFL`
- `AFF_DIM_AFFINE_INTER_HYPERPLANE`
- `AFFINE_HYPERPLANE`
- `AFF_DIM_HYPERPLANE`
- `DIMINDEX_3`
- `CONVEX_HULL_UNION_NONEMPTY_EXPLICIT`

### Porting notes (optional)
- The proof involves extensive manipulation of convex hulls, affine dimensions, and geometric properties in 3D space.
- Ensure that the target proof assistant has comparable libraries for real vector spaces, convex sets, and affine geometry.
- Special attention should be paid to tactics that perform arithmetic reasoning (`REAL_ARITH_TAC`, `INT_ARITH`) since the automation may differ in other systems. Especially, ensure that tactics related to inequalities are present e.g., `REAL_LT_LE`.
- The use of `ASM_CASES_TAC` suggests a proof by cases, which may need to be replicated manually in systems that lack similar automation.
- `VEC3_TAC` performs vector expansion and simplification, which may have to be done explicitly.


---

## COMPUTE_EDGES_CONV

### Name of formal statement
COMPUTE_EDGES_CONV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COMPUTE_EDGES_CONV =
  let lemma = prove
   (`(x INSERT s) INTER {x | P x} =
                        if P x then x INSERT (s INTER {x | P x})
                        else s INTER {x | P x}`,
    COND_CASES_TAC THEN ASM SET_TAC[]) in
  fun tm ->
    let th1 = MATCH_MP COMPUTE_FACES_1 (COPLANAR_HYPERPLANE_RULE tm) in
    let th2 = MP (CONV_RULE(LAND_CONV
     (COMB2_CONV (RAND_CONV(PURE_REWRITE_CONV[FINITE_INSERT; FINITE_EMPTY]))
                 (RAND_CONV VECTOR3_EQ_0_CONV THENC
                  GEN_REWRITE_CONV I [NOT_CLAUSES]) THENC
      GEN_REWRITE_CONV I [AND_CLAUSES])) th1) TRUTH in
    CONV_RULE
     (BINDER_CONV(RAND_CONV
        (REWRITE_CONV[RIGHT_EXISTS_AND_THM] THENC
         REWRITE_CONV[EXISTS_IN_INSERT; NOT_IN_EMPTY] THENC
         REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY] THENC
         ONCE_DEPTH_CONV VECTOR3_SUB_CONV THENC
         ONCE_DEPTH_CONV VECTOR3_CROSS_CONV THENC
         ONCE_DEPTH_CONV let_CONV THENC
         ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV THENC
         REWRITE_CONV[real_ge] THENC
         ONCE_DEPTH_CONV VECTOR3_DOT_CONV THENC
         ONCE_DEPTH_CONV let_CONV THENC
         ONCE_DEPTH_CONV REAL_RAT5_LE_CONV THENC
         REWRITE_CONV[INSERT_AC] THENC REWRITE_CONV[DISJ_ACI] THENC
         REPEATC(CHANGED_CONV
          (ONCE_REWRITE_CONV[lemma] THENC
           ONCE_DEPTH_CONV(LAND_CONV VECTOR3_DOT_CONV THENC
                           REAL_RAT5_EQ_CONV) THENC
           REWRITE_CONV[])) THENC
         REWRITE_CONV[INTER_EMPTY] THENC
         REWRITE_CONV[INSERT_AC] THENC REWRITE_CONV[DISJ_ACI]
        ))) th2;;
```
### Informal statement
Given a term `tm` representing a coplanar set of points, this conversion returns a theorem that exhaustively characterizes the edge cases of that coplanar set.

### Informal sketch
The conversion `COMPUTE_EDGES_CONV` operates as follows:
- First, it proves the lemma: `(x INSERT s) INTER {x | P x} = if P x then x INSERT (s INTER {x | P x}) else s INTER {x | P x}` using `COND_CASES_TAC` and `ASM SET_TAC[]`.
- It applies the theorem `COMPUTE_FACES_1` to a result of `COPLANAR_HYPERPLANE_RULE` applied to the term `tm` to obtain `th1`.
- It transforms `th1` by applying a series of conversions related to logical conjunction (`LAND_CONV`) and vector equality (`VECTOR3_EQ_0_CONV`) to get `th2`. This involves rewriting with theorems concerning finiteness (`FINITE_INSERT`, `FINITE_EMPTY`), vector equality, and logical connectives (`NOT_CLAUSES`, `AND_CLAUSES`).
- Finally, it constructs the main conversion using `BINDER_CONV` composed with a series of rewriting and simplification steps on `th2`. This involves:
  - Rewriting using theorems about existential quantifiers (`RIGHT_EXISTS_AND_THM`, `EXISTS_IN_INSERT`, `NOT_IN_EMPTY`) and universal quantifiers (`FORALL_IN_INSERT`, `NOT_IN_EMPTY`).
  - Simplifying vector expressions using `VECTOR3_SUB_CONV`, `VECTOR3_CROSS_CONV`, `VECTOR3_EQ_0_CONV`, and `VECTOR3_DOT_CONV`.
  - Applying the `let_CONV` conversion.
  - Simplifying real number expressions (`real_ge`, `REAL_RAT5_LE_CONV`, `REAL_RAT5_EQ_CONV`).
  - Manipulating sets using theorems like `INSERT_AC`, `DISJ_ACI`, and `INTER_EMPTY`.
  - Repeatedly applying a conversion involving the initial lemma and vector dot product conversions until no changes occur.

### Mathematical insight
This conversion aims to derive a theorem describing coplanar edge cases by systematically simplifying and rewriting an initial theorem (`COMPUTE_FACES_1`) based on coplanarity conditions. It uses a combination of logical, set-theoretic, and algebraic simplification steps, particularly focusing on vector operations, to arrive at a final exhaustive characterization. The core idea relies on breaking down the coplanarity conditions into manageable boolean expressions that can be simplified using rewriting and equational reasoning.

### Dependencies
- Theorems:
  - `COMPUTE_FACES_1`
  - `RIGHT_EXISTS_AND_THM`
  - `EXISTS_IN_INSERT`
  - `NOT_IN_EMPTY`
  - `FORALL_IN_INSERT`
  - `NOT_IN_EMPTY`
  - `real_ge`
  - `INSERT_AC`
  - `DISJ_ACI`
  - `INTER_EMPTY`
  - `FINITE_INSERT`
  - `FINITE_EMPTY`
- Conversions:
  - `COPLANAR_HYPERPLANE_RULE`
  - `LAND_CONV`
  - `VECTOR3_EQ_0_CONV`
  - `PURE_REWRITE_CONV`
  - `GEN_REWRITE_CONV`
  - `VECTOR3_SUB_CONV`
  - `VECTOR3_CROSS_CONV`
  - `let_CONV`
  - `VECTOR3_DOT_CONV`
  - `REAL_RAT5_LE_CONV`
  - `REAL_RAT5_EQ_CONV`
  - `BINDER_CONV`
  - `REWRITE_CONV`
  - `ONCE_DEPTH_CONV`
  - `CHANGED_CONV`
- Tactics:
  - `COND_CASES_TAC`
  - `ASM SET_TAC`

### Porting notes (optional)
- The heavy reliance on rewriting and simplification suggests that a proof assistant with strong automation in these areas (e.g., Isabelle with its simplifier, or Lean with `simp`) would be beneficial.
- The use of `BINDER_CONV` might require special attention, as different proof assistants handle binder conversions in varying ways.
- The `REPEATC` tactic can be emulated within other proof assistants using similar looping constructs or `try` blocks with appropriate change checking to ensure termination.


---

## CARD_EQ_LEMMA

### Name of formal statement
`CARD_EQ_LEMMA`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_EQ_LEMMA = prove
 (`!x s n. 0 < n /\ ~(x IN s) /\ s HAS_SIZE (n - 1)
           ==> (x INSERT s) HAS_SIZE n`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT] THEN ASM_ARITH_TAC);;
```

### Informal statement
For all `x`, `s`, and `n`, if `0 < n` and `x` is not in `s` and the cardinality of `s` is `n - 1`, then the cardinality of `x INSERT s` is `n`.

### Informal sketch
The theorem states that adding an element to a finite set increases its cardinality by one, provided the element was not already in the set and the cardinality assumptions for `s` hold. The proof proceeds as follows:
- The starting point involves rewriting using the definition of `HAS_SIZE`.
- The goal is then simplified by stripping away the assumptions.
- We then use `CARD_CLAUSES` and `FINITE_INSERT` to further simplify the goal using basic facts about cardinality and finiteness of insertion.
- Finally, the arithmetic is handled using `ASM_ARITH_TAC`, which resolves the goal based on the arithmetic relationships.

### Mathematical insight
This theorem formalizes a basic intuition about set cardinality. It's a key stepping stone for proving more complex results about finite sets and their sizes. The lemma is specifically used when reasoning about the number of edges per face for Platonic solids, suggesting its importance in geometric or combinatorial arguments.

### Dependencies
- Definitions: `HAS_SIZE`
- Theorems: `CARD_CLAUSES`, `FINITE_INSERT`
- Tactics: `ASM_ARITH_TAC`


---

## EDGES_PER_FACE_TAC

### Name of formal statement
EDGES_PER_FACE_TAC

### Type of the formal statement
Tactic

### Formal Content
```ocaml
let EDGES_PER_FACE_TAC th =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD  {e:real^3->bool | e face_of f /\ aff_dim(e) = &1}` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_TRANS; FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^3->bool` th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  W(fun (_,w) -> REWRITE_TAC[COMPUTE_EDGES_CONV(find_term is_setenum w)]) THEN
  REWRITE_TAC[SET_RULE `x = a \/ x = b <=> x IN {a,b}`] THEN
  REWRITE_TAC[GSYM IN_INSERT; SET_RULE `{x | x IN s} = s`] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC
   (MESON[HAS_SIZE] `s HAS_SIZE n ==> CARD s = n`) THEN
  REPEAT
  (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SEGMENT_EQ; DE_MORGAN_THM] THEN
     REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})`) THEN
     PURE_ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
     REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES];;
```

### Informal statement
Given a theorem `th` stating that a face `f` of a polyhedron has a set enumeration `s`, this tactic proves that the number of edges of `f` is equal to the cardinality of the set of all `e` such that `e` is a face of `f` and the affine dimension of `e` is 1.

### Informal sketch
The tactic performs the following steps:

*   Repeatedly strips quantifiers and implications.
*   Matches the current goal with the given theorem `EQ_TRANS`.
*   Applies an existential quantifier introduction for `CARD {e:real^3->bool | e face_of f /\ aff_dim(e) = &1}`.
*   Splits the goal into two subgoals using `CONJ_TAC`.
*   The first subgoal is handled with:
    *   Applies the term.
    *   Rewrites using `EXTENSION`.
    *   Rewrites using `IN_ELIM_THM`.
    *   Applies `ASM_MESON_TAC` with assumptions `FACE_OF_FACE`, `FACE_OF_TRANS`, and `FACE_OF_IMP_SUBSET`.
*   The second subgoal is trivially solved by `ALL_TAC.`
*   Applies the theorem `th` to the goal (after specializing it with the face `f`) using `MP_TAC` and performs rewriting with assumptions in the assumption list using `ASM_REWRITE_TAC.`
*   Discharges the assumption.
*   Applies `SUBST1_TAC`.
*   Rewrites using a conversion `COMPUTE_EDGES_CONV` given the set enumeration which is found using `find_term is_setenum w`.
*   Rewrites sets.
*   Matches the current goal with `s HAS_SIZE n ==> CARD s = n` using `MESON` and `HAS_SIZE`.
*   Repeatedly breaks down the goal using `CARD_EQ_LEMMA`, `CONJ_TAC`. It then proceeds with three tactics:
    *   Tries to evaluate the goal using `NUM_REDUCE_CONV.`
    *   Rewrites using set theory lemmas and vector related lemmas.
    *   Trivially solves the goal.
*   Finally evaluates the goal and rewrites it.

### Mathematical insight
This tactic automates the proof that the number of edges of a face `f` is equal to the number of elements in the set of edges from `f`. It makes substantial use of rewriting using set and vector rules.

### Dependencies

*   **Theorems:** `EXTENSION`, `IN_ELIM_THM`, `FACE_OF_FACE`, `FACE_OF_TRANS`, `FACE_OF_IMP_SUBSET`, `HAS_SIZE`, `CARD_EQ_LEMMA`, `IN_INSERT`, `NOT_IN_EMPTY`, `SEGMENT_EQ`, `DE_MORGAN_THM`, `VECTOR_SUB_EQ`, `CONJUNCT1`, `HAS_SIZE_CLAUSES`.
*   **Definitions:** `face_of`, `aff_dim`, `HAS_SIZE`.
*   **Conversions:** `COMPUTE_EDGES_CONV`, `NUM_REDUCE_CONV`, `VECTOR3_SUB_CONV`, `VECTOR3_EQ_0_CONV`.

### Porting notes (optional)
*   The tactic relies heavily on rewriting, so a robust rewriting engine is crucial.
*   The conversions might need to be adapted or reimplemented in the target proof assistant.
*   The `MESON` calls indicate reliance on a first-order automated theorem prover to discharge some subgoals.


---

## TETRAHEDRON_EDGES_PER_FACE

### Name of formal statement
TETRAHEDRON_EDGES_PER_FACE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TETRAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_tetrahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC TETRAHEDRON_FACETS);;
```
### Informal statement
For all `f`, if `f` is a face of the standard tetrahedron `std_tetrahedron` and the affine dimension of `f` is equal to 2, then the cardinality of the set of `e` such that `e` is a face of `std_tetrahedron`, the affine dimension of `e` is equal to 1, and `e` is a subset of `f`, is equal to 3.

### Informal sketch
- The theorem states that each 2-dimensional face (facet) of the standard tetrahedron has exactly 3 edges.
- The proof uses `EDGES_PER_FACE_TAC` which, given a set of facets of a polyhedron, proves that each facet has the correct number of edges.
- `TETRAHEDRON_FACETS` is assumed to be a previously established fact that provides the facets of the standard tetrahedron to `EDGES_PER_FACE_TAC`.

### Mathematical insight
This theorem is a basic geometric fact about tetrahedra. It confirms that each triangular face of the standard tetrahedron has three edges, consistent with the definition of a triangle.

### Dependencies
- Theorems: `EDGES_PER_FACE_TAC`
- Definitions: `face_of`, `std_tetrahedron`, `aff_dim`, `SUBSET`, `CARD`
- Facts: `TETRAHEDRON_FACETS`


---

## CUBE_EDGES_PER_FACE

### Name of formal statement
CUBE_EDGES_PER_FACE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBE_EDGES_PER_FACE = prove
 (`!f. f face_of std_cube /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 4`,
  EDGES_PER_FACE_TAC CUBE_FACETS);;
```

### Informal statement
For all `f`, if `f` is a face of the standard cube `std_cube` and the affine dimension of `f` is 2, then the cardinality of the set of `e` such that `e` is a face of the standard cube `std_cube`, the affine dimension of `e` is 1, and `e` is a subset of `f`, is equal to 4.

### Informal sketch
- The theorem states that each two-dimensional face of the standard cube has exactly 4 edges.
- The proof uses `EDGES_PER_FACE_TAC` which expects a list of the faces. The faces are provided by `CUBE_FACETS` which is presumably already defined.
- `EDGES_PER_FACE_TAC` then reasons about the faces of the cube to calculate the number of edges per face, automatically discharging assumptions about the cube faces.

### Mathematical insight
This theorem captures a basic geometric property of a cube: each square face has four edges. It connects the topological notion of a face with the geometric concept of dimension.  The fact that HOL Light can formally prove such a geometric fact is a testament to its ability to formalize geometric reasoning.

### Dependencies
- Definition: `face_of`
- Definition: `std_cube`
- Definition: `aff_dim`
- Definition: `SUBSET`
- Theorem: `CUBE_FACETS`
- Tactic: `EDGES_PER_FACE_TAC`


---

## OCTAHEDRON_EDGES_PER_FACE

### Name of formal statement
OCTAHEDRON_EDGES_PER_FACE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OCTAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_octahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC OCTAHEDRON_FACETS);;
```

### Informal statement
For all `f`, if `f` is a face of the standard octahedron (`std_octahedron`) and the affine dimension of `f` is equal to 2, then the cardinality of the set of `e` such that `e` is a face of the standard octahedron, the affine dimension of `e` is equal to 1, and `e` is a subset of `f`, is equal to 3.

### Informal sketch
The theorem states that each 2-dimensional face of the standard octahedron has exactly three 1-dimensional faces (edges) as subsets.
- The proof proceeds by using `EDGES_PER_FACE_TAC`, which is a tactic designed to prove properties about the number of edges per face of a polyhedron.
- The tactic is applied to the faces of the standard octahedron by providing `OCTAHEDRON_FACETS`.

### Mathematical insight
This theorem formalizes the geometric property that a triangular face of an octahedron is bounded by three edges. This is a fundamental property of the octahedron's structure and its relationship to Euclidean geometry.

### Dependencies
- Theorems:
  - `OCTAHEDRON_FACETS`
- Tactics:
  - `EDGES_PER_FACE_TAC`


---

## DODECAHEDRON_EDGES_PER_FACE

### Name of formal statement
DODECAHEDRON_EDGES_PER_FACE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DODECAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_dodecahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 5`,
  EDGES_PER_FACE_TAC DODECAHEDRON_FACETS);;
```
### Informal statement
For every `f`, if `f` is a face of the standard dodecahedron and the affine dimension of `f` is equal to 2, then the cardinality of the set of `e` such that `e` is a face of the standard dodecahedron and the affine dimension of `e` is equal to 1 and `e` is a subset of `f`, is equal to 5.

### Informal sketch
- Main goal: Prove that each face of the standard dodecahedron (which is a 2-dimensional affine space) has exactly 5 edges (1-dimensional affine spaces) as its subsets, where `e` and `f` are faces of the standard dodecahedron.
- Apply tactic `EDGES_PER_FACE_TAC` to the term `DODECAHEDRON_FACETS`. This tactic likely automates the proof by using properties of the standard dodecahedron and its faces, possibly involving:
    - Definitions of `face_of`, `aff_dim`, `SUBSET`, and `CARD`.
    - Properties of the standard dodecahedron (`std_dodecahedron`) and its facets (2-dimensional faces/`DODECAHEDRON_FACETS`).
    - Theorem(s) stating the number of vertices/edges of a face.

### Mathematical insight
This theorem captures the geometric property of a dodecahedron that each of its faces, being a pentagon, has exactly five edges. It connects the combinatorial structure of the dodecahedron (faces and edges) with the affine dimension, giving a formal statement of a well-known geometric fact.

### Dependencies
- Definitions: `face_of`, `std_dodecahedron`, `aff_dim`, `SUBSET`, `CARD`
- Theorems: `DODECAHEDRON_FACETS`

### Porting notes (optional)
- The tactic `EDGES_PER_FACE_TAC` is HOL Light specific, and its functionality will need to be replicated manually or via a similar automated tactic in other proof assistants. The main idea is to use properties of the dodecahedron's faces to prove this claim, so understanding the definition of dodecahedron faces is crucial.


---

## ICOSAHEDRON_EDGES_PER_FACE

### Name of formal statement
ICOSAHEDRON_EDGES_PER_FACE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ICOSAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_icosahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC ICOSAHEDRON_FACETS);;
```
### Informal statement
For every `f`, if `f` is a face of the standard icosahedron and the affine dimension of `f` is equal to 2, then the cardinality of the set of `e` such that `e` is a face of the standard icosahedron, the affine dimension of `e` is equal to 1, and `e` is a subset of `f`, is equal to 3.

### Informal sketch
The theorem states that each face (2-dimensional facet) of the standard icosahedron is bounded by exactly 3 edges (1-dimensional facets). The proof proceeds by:
- Applying the tactic `EDGES_PER_FACE_TAC`.
- This tactic likely uses the precomputed list of faces of the standard icosahedron, `ICOSAEDRON_FACETS`, and then reasons about the dimension and subset relationships to deduce the cardinality of edges per face.

### Mathematical insight
The statement formalizes a fundamental property of the icosahedron: each of its faces is a triangle, and therefore has three edges. This theorem is a basic geometric invariant of the icosahedron.

### Dependencies
- Definition: `face_of`
- Definition: `std_icosahedron`
- Definition: `aff_dim`
- Definition: `SUBSET`
- Theorem: `ICOSAEDRON_FACETS`

### Porting notes (optional)
- The main challenge for porting lies in representing the standard icosahedron and its faces. Other systems may have different ways of representing polyhedra.
- The `EDGES_PER_FACE_TAC` is a specialized tactic; porting this would require reimplementing the reasoning about faces, edges, dimension, and subset relations. Instead, one would likely re-prove the theorem directly by appealing to the list of faces and their properties.


---

## POLYTOPE_3D_LEMMA

### Name of formal statement
POLYTOPE_3D_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYTOPE_3D_LEMMA = prove
 (`(let a = (z - x) cross (y - x) in
    ~(a = vec 0) /\ ?w. w IN s /\ ~(a dot w = a dot x))
   ==> aff_dim(convex hull (x INSERT y INSERT z INSERT s:real^3->bool)) = &3`,
  REPEAT GEN_TAC THEN LET_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM DIMINDEX_3; AFF_DIM_LE_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `aff_dim {w:real^3,x,y,z}` THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]] THEN
  ONCE_REWRITE_TAC[AFF_DIM_INSERT] THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `w IN {w:real^3 | a dot w = a dot x}` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `x IN s ==> s SUBSET t ==> x IN t`)) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      UNDISCH_TAC `~(a:real^3 = vec 0)` THEN EXPAND_TAC "a" THEN VEC3_TAC;
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    UNDISCH_TAC `~(a:real^3 = vec 0)` THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[CROSS_EQ_0; GSYM COLLINEAR_3] THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; INSERT_AC; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN INT_ARITH_TAC]);;
```

### Informal statement
If `a` is the cross product of `(z - x)` and `(y - x)`, and `a` is not the zero vector, and there exists a vector `w` in the set `s` such that `a` dot `w` is not equal to `a` dot `x`, then the affine dimension of the convex hull of the set formed by inserting `x`, `y`, `z`, and `s` is 3.

### Informal sketch
The proof shows that under the given conditions, the affine dimension of the convex hull of `{x, y, z}` and `s` is 3.

- Assume that `a = (z - x) cross (y - x)`, `~(a = vec 0)`, and `?w. w IN s /\ ~(a dot w = a dot x)`.

- Show that the affine dimension of the convex hull of `{x, y, z, s}` is 3.  The goal is `aff_dim(convex hull (x INSERT y INSERT z INSERT s)) = &3`.

- Using `AFF_DIM_CONVEX_HULL` and properties of insertion, the problem reduces to showing that the affine dimension of `{x, y, z, w}` is 3 where `w` is the element of `s` whose dot product with `a` is not equal to `a` dot `x`.

- One branch of the proof considers the case where we assume `w` is in the affine hyperplane defined by `{w | a dot w = a dot x}`.
    - It's shown that because `s` is a subset of the affine hyperplane, `w IN s` from our assumptions implies that `aff_dim {x,y,z,w}` is not &3.

- The main branch considers the case where `w` is not in the affine hyperplane.
    - We have `~(a = vec 0)` and `~(a dot w = a dot x)`.
    - The assumption `a = (z - x) cross (y - x)` is used to show that x, y, and z are not collinear.
    - Therefore, we know that `x`, `y`, and `z` are affinely independent and since `w` satisfies the condition of not lying on the plane, it follows that the set `{x, y, z, w}` is affinely independent, meaning that the affine dimension of the set `{x, y, z, w}` is 3.

### Mathematical insight
This theorem states that if you have three points `x`, `y`, and `z` in 3D space that are not collinear (since their cross product `a` is not zero), and you have a fourth point `w` in the set `s` that does not lie in the plane defined by `x`, `y`, and `z` (since `a dot w != a dot x`), then the convex hull of these four points has an affine dimension of 3, which means the convex hull is a 3-dimensional object (a tetrahedron or some other 3D volume). This theorem is relevant to showing that certain geometric shapes are full-dimensional.

### Dependencies
- `AFF_DIM_LE_UNIV`
- `DIMINDEX_3`
- `INT_LE_ANTISYM`
- `AFF_DIM_CONVEX_HULL`
- `INT_LE_TRANS`
- `AFF_DIM_SUBSET`
- `AFF_DIM_INSERT`
- `HULL_MINIMAL`
- `AFFINE_HYPERPLANE`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `IN_ELIM_THM`
- `CROSS_EQ_0`
- `COLLINEAR_3`
- `COLLINEAR_3_EQ_AFFINE_DEPENDENT`
- `INSERT_AC`
- `DE_MORGAN_THM`
- `AFF_DIM_AFFINE_INDEPENDENT`
- `CARD_CLAUSES`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `IN_INSERT`
- `NOT_IN_EMPTY`


---

## POLYTOPE_FULLDIM_TAC

### Name of formal statement
POLYTOPE_FULLDIM_TAC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let POLYTOPE_FULLDIM_TAC =
  MATCH_MP_TAC POLYTOPE_3D_LEMMA THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_CROSS_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN CONJ_TAC THENL
   [CONV_TAC(RAND_CONV VECTOR3_EQ_0_CONV) THEN REWRITE_TAC[];
    CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
    REWRITE_TAC[]];;
```
### Informal statement
`POLYTOPE_FULLDIM_TAC` is a tactic that, when applied to a goal, attempts to prove that a polytope in 3D space is full-dimensional

### Informal sketch
The tactic `POLYTOPE_FULLDIM_TAC` proceeds as follows:

- First, apply `MATCH_MP_TAC` with `POLYTOPE_3D_LEMMA`. This lemma likely establishes some condition for a polytope in 3D space to be full-dimensional.
- Perform some conversions to simplify vector subtraction using `VECTOR3_SUB_CONV` inside `CONV_TAC`.
- Perform conversions to simplify vector cross products via `VECTOR3_CROSS_CONV` inside `CONV_TAC`.
- Apply the `let_CONV` conversion with `CONV_TAC`. This likely simplifies `let` bindings introduced in earlier steps.
- Split the goal into two subgoals using `CONJ_TAC`.
- The first subgoal proceeds with `CONV_TAC(RAND_CONV VECTOR3_EQ_0_CONV)` followed by `REWRITE_TAC[]`. This likely aims to show some vector is not equal to 0.
- The second subgoal begins by simplifying vector dot products with `VECTOR3_DOT_CONV` inside `CONV_TAC`. It rewrites using `EXISTS_IN_INSERT` and `NOT_IN_EMPTY`. It then reapplies simplifications for `VECTOR3_DOT_CONV` followed by simplifications for `REAL_RAT5_EQ_CONV`, and applies `REWRITE_TAC[]`.

### Mathematical insight
The tactic implements a proof strategy to establish that a 3D polytope is full-dimensional. This probably involves showing linear independence of some vectors constructed from vertices of the polytope, potentially by proving that a certain volume (related to scalar triple product) is non-zero. The core idea is to algorithmically discharge the proof that polytope has dimension 3.

### Dependencies
- `POLYTOPE_3D_LEMMA`
- `VECTOR3_SUB_CONV`
- `VECTOR3_CROSS_CONV`
- `let_CONV`
- `VECTOR3_EQ_0_CONV`
- `VECTOR3_DOT_CONV`
- `EXISTS_IN_INSERT`
- `NOT_IN_EMPTY`
- `REAL_RAT5_EQ_CONV`

### Porting notes (optional)
The extensive use of conversions suggests that equational reasoning and simplification are crucial. In other proof assistants, these steps might be achieved by rewriting with suitable equational lemmas or using dedicated simplification tactics with appropriate configurations. The `MATCH_MP_TAC` relies on higher-order matching, so ensure that the target proof assistant supports a similar form of matching or that `POLYTOPE_3D_LEMMA` can be applied by name in the target environment. Pay attention to field names inside records of vectors.


---

## STD_TETRAHEDRON_FULLDIM

### Name of formal statement
STD_TETRAHEDRON_FULLDIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_TETRAHEDRON_FULLDIM = prove
 (`aff_dim std_tetrahedron = &3`,
  REWRITE_TAC[std_tetrahedron] THEN POLYTOPE_FULLDIM_TAC);;
```
### Informal statement
The affine dimension of the standard tetrahedron is equal to 3.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definition of `std_tetrahedron` to expand the term.
- Then `POLYTOPE_FULLDIM_TAC` is applied. This tactic likely uses properties of polytopes and affine dimension to deduce that the affine dimension of `std_tetrahedron` is 3.

### Mathematical insight
This theorem states a basic geometrical fact about the standard tetrahedron. The affine dimension of a set of points is the dimension of the smallest affine space containing that set. Since the standard tetrahedron is defined by four affinely independent points in 3-dimensional space, its affine dimension is 3.

### Dependencies
- Definitions: `std_tetrahedron`
- Theorems: properties used by `POLYTOPE_FULLDIM_TAC`

### Porting notes (optional)
The tactic `POLYTOPE_FULLDIM_TAC` encapsulates significant automation. When porting, it will be necessary to either reimplement a similar tactic or expand the proof by hand, applying the necessary lemmas regarding affine dimension and polytopes. The definition of `std_tetrahedron` must be ported first.


---

## STD_CUBE_FULLDIM

### Name of formal statement
STD_CUBE_FULLDIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_CUBE_FULLDIM = prove
 (`aff_dim std_cube = &3`,
  REWRITE_TAC[std_cube] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
Prove that the affine dimension of the standard cube `std_cube` is equal to 3.

### Informal sketch
The proof proceeds as follows:

- First, rewrite using the definition of `std_cube`.
- Then, apply `POLYTOPE_FULLDIM_TAC` which automatically proves the goal.  This tactic likely leverages properties of affine dimension and the specific structure exposed by the definition of `std_cube` to conclude that its affine dimension is 3.

### Mathematical insight
This theorem states a basic geometric property of the standard cube in 3-dimensional space. The standard cube `std_cube` is specified as a polytope and its affine dimension is exactly 3, reflecting the fact that it spans a 3-dimensional affine subspace. This is a sanity check to ensure that the definition of the standard cube and the notion of affine dimension align with geometric intuition.

### Dependencies
- Definition: `std_cube`
- Tactic: `POLYTOPE_FULLDIM_TAC`


---

## STD_OCTAHEDRON_FULLDIM

### Name of formal statement
STD_OCTAHEDRON_FULLDIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_OCTAHEDRON_FULLDIM = prove
 (`aff_dim std_octahedron = &3`,
  REWRITE_TAC[std_octahedron] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
The affine dimension of the standard octahedron is equal to 3.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the goal using the definition of `std_octahedron`.
- Then, apply `POLYTOPE_FULLDIM_TAC` to prove the goal. This tactic likely uses properties of polytopes and their affine dimension to establish the result.

### Mathematical insight
This theorem states that the standard octahedron, embedded in 3-dimensional Euclidean space, is a full-dimensional object within that space. This means it spans the entire 3-dimensional space and is not contained within a lower-dimensional affine subspace.

### Dependencies
- Definition: `std_octahedron`
- Tactic: `POLYTOPE_FULLDIM_TAC`


---

## STD_DODECAHEDRON_FULLDIM

### Name of formal statement
STD_DODECAHEDRON_FULLDIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_DODECAHEDRON_FULLDIM = prove
 (`aff_dim std_dodecahedron = &3`,
  REWRITE_TAC[STD_DODECAHEDRON] THEN POLYTOPE_FULLDIM_TAC);;
```
### Informal statement
The affine dimension of the standard dodecahedron is equal to 3.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definition of `STD_DODECAHEDRON`.
- Then, apply the general theorem `POLYTOPE_FULLDIM_TAC` which determines the affine dimension of polytopes given their vertices.

### Mathematical insight
This theorem states that the standard dodecahedron, as defined in HOL Light, spans a 3-dimensional affine space. This is expected, as the standard dodecahedron is a 3-dimensional object. The theorem confirms that the formal definition captures this fundamental property.

### Dependencies
- Definitions: `STD_DODECAHEDRON`
- Theorems: `POLYTOPE_FULLDIM_TAC`


---

## STD_ICOSAHEDRON_FULLDIM

### Name of formal statement
STD_ICOSAHEDRON_FULLDIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_ICOSAHEDRON_FULLDIM = prove
 (`aff_dim std_icosahedron = &3`,
  REWRITE_TAC[STD_ICOSAHEDRON] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
Prove that the affine dimension of the standard icosahedron is equal to 3.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the term `aff_dim std_icosahedron` using the definition of `STD_ICOSAHEDRON`.
- Then, apply `POLYTOPE_FULLDIM_TAC` to prove that the affine dimension is 3.

### Mathematical insight
This theorem establishes that the standard icosahedron is a full-dimensional object in 3-dimensional space. This is an important property for geometric reasoning and ensures that the icosahedron spans the entire 3D space in which it is embedded.

### Dependencies
Definitions:
- `STD_ICOSAHEDRON`

Theorems:
- `POLYTOPE_FULLDIM_TAC`


---

## COMPUTE_EDGES_TAC

### Name of formal statement
COMPUTE_EDGES_TAC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COMPUTE_EDGES_TAC defn fulldim facets =
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
      `?f:real^3->bool. (f face_of p /\ aff_dim f = &2) /\
                        (e face_of f /\ aff_dim e = &1)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [STRIP_TAC; MESON_TAC[FACE_OF_TRANS]] THEN
    MP_TAC(ISPECL [lhs(concl defn); `e:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        CONJ_TAC THEN
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[facet_of] THEN
      REWRITE_TAC[fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_MESON_TAC[FACE_OF_FACE]];
    REWRITE_TAC[facets] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    CONV_TAC(LAND_CONV(DEPTH_BINOP_CONV `\/`
     (fun tm -> REWR_CONV (COMPUTE_EDGES_CONV(rand(rand(lhand tm)))) tm))) THEN
    REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI]];;
```

### Informal statement
The tactic `COMPUTE_EDGES_TAC` takes as input a definition `defn`, a fact `fulldim` about the full dimension of a polyhedron, and a fact `facets` specifying the facets of the polyhedron. The tactic proves the existence of a function `f` from 3D real space to booleans, representing a face, and a function `e` from 3D real space to booleans, representing an edge, such that `f` is a face of `p` and has affine dimension 2, and `e` is a face of `f` and has affine dimension 1.

It uses `FACE_OF_POLYHEDRON_SUBSET_FACET`, `FACE_OF_TRANS`, `POLYHEDRON_CONVEX_HULL`, `FINITE_INSERT`, `FINITE_EMPTY`, `AFF_DIM_EMPTY`, `MONO_EXISTS`, `facet_of`, `FACE_OF_FACE`, `EXISTS_OR_THM`, `UNWIND_THM2`, `INSERT_AC`, and `DISJ_ACI`.

### Informal sketch
The tactic `COMPUTE_EDGES_TAC` aims to compute the edges of a polyhedron. The proof proceeds as follows:
- Start by introducing the existential statement that there exists a face `f` of dimension 2 and an edge `e` of dimension 1 that are faces of the polyhedron `p`.
- The proof then splits into subgoals to prove that such an `f` and `e` exist and satisfy the required conditions.
- The first main subgoal shows that if `e` is a face of the polyhedron, then it is also a subset of a facet of the polyhedron, using `FACE_OF_POLYHEDRON_SUBSET_FACET`. This part also involves rewriting with the initial definition `defn` of the polyhedron, expanding the convex hull representation, and computing the affine dimension using `AFF_DIM_EMPTY`.
- The second main subgoal handles the existence of a face `f` by using `MONO_EXISTS` and rewriting rules about `facet_of`, and `FACE_OF_FACE`.
- The tactic then rewrites with the given `facets` and applies simplification rules like the distributivity of conjunction over disjunction. It unfolds the existential and simplifies the resulting terms by evaluating the `COMPUTE_EDGES_CONV`. The remaining goals are solved by using associativity, commutativity, and idempotence laws for `INSERT`. `TAUT` is used to solve some tautological goals.

### Mathematical insight
This tactic automates the process of finding the edges of a polyhedron given its facets and the fact that it is full-dimensional. The key idea is to express the polyhedron as a convex hull and then systematically identify faces of decreasing dimension, using properties of `face_of` and affine dimension.

### Dependencies
- `FACE_OF_POLYHEDRON_SUBSET_FACET`
- `FACE_OF_TRANS`
- `POLYHEDRON_CONVEX_HULL`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `AFF_DIM_EMPTY`
- `MONO_EXISTS`
- `facet_of`
- `FACE_OF_FACE`
- `EXISTS_OR_THM`
- `UNWIND_THM2`
- `INSERT_AC`
- `DISJ_ACI`

### Porting notes (optional)
The tactic relies heavily on rewriting and simplification. When porting to another proof assistant, ensure that the rewriting engine is powerful enough to handle the required simplifications. The use of `CONV_TAC` with `INT_REDUCE_CONV` indicates that arithmetic simplification is important. The handling of sets as Boolean functions will have to be managed in the target proof assistant.


---

## TETRAHEDRON_EDGES

### Name of formal statement
TETRAHEDRON_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TETRAHEDRON_EDGES = prove
 (`!e. e face_of std_tetrahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`,
  COMPUTE_EDGES_TAC
    std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_FACETS);;
```
### Informal statement
For all sets `e`, `e` is a face of the standard tetrahedron (`std_tetrahedron`) and the affine dimension of `e` is equal to 1 if and only if `e` is equal to one of the following convex hulls:
  - The convex hull of the set containing the vectors `(-- &1; -- &1; &1)` and `(-- &1; &1; -- &1)`.
  - The convex hull of the set containing the vectors `(-- &1; -- &1; &1)` and `(&1; -- &1; -- &1)`.
  - The convex hull of the set containing the vectors `(-- &1; -- &1; &1)` and `(&1; &1; &1)`.
  - The convex hull of the set containing the vectors `(-- &1; &1; -- &1)` and `(&1; -- &1; -- &1)`.
  - The convex hull of the set containing the vectors `(-- &1; &1; -- &1)` and `(&1; &1; &1)`.
  - The convex hull of the set containing the vectors `(&1; -- &1; -- &1)` and `(&1; &1; &1)`.

### Informal sketch
The proof proceeds by:
- Using `COMPUTE_EDGES_TAC` which automatically derives the result based on:
  - The definition of `std_tetrahedron`.
  - The fact that `std_tetrahedron` is full dimensional (`STD_TETRAHEDRON_FULLDIM`).
  - A theorem characterizing the faces of the `std_tetrahedron` (`TETRAHEDRON_FACETS`).

### Mathematical insight
This theorem provides a complete characterization of the edges of the standard tetrahedron. An edge is a face of affine dimension 1. The theorem confirms that the edges are the line segments connecting the vertices of the `std_tetrahedron`. This is a key component to proving more general geometric theorems related to convexity and polyhedra.

### Dependencies
- Definitions:
  - `std_tetrahedron`
- Theorems:
  - `STD_TETRAHEDRON_FULLDIM`
  - `TETRAHEDRON_FACETS`
- Tactics:
  - `COMPUTE_EDGES_TAC`


---

## CUBE_EDGES

### Name of formal statement
CUBE_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBE_EDGES = prove
 (`!e. e face_of std_cube /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&1; &1; &1]}`,
  COMPUTE_EDGES_TAC
    std_cube STD_CUBE_FULLDIM CUBE_FACETS);;
```

### Informal statement
For all sets `e`, `e` is a face of the standard cube and the affine dimension of `e` is equal to 1 if and only if `e` is equal to one of the following twelve convex hulls:
- The convex hull of `{vector[--1; --1; --1], vector[--1; --1; 1]}`
- The convex hull of `{vector[--1; --1; --1], vector[--1; 1; --1]}`
- The convex hull of `{vector[--1; --1; --1], vector[1; --1; --1]}`
- The convex hull of `{vector[--1; --1; 1], vector[--1; 1; 1]}`
- The convex hull of `{vector[--1; --1; 1], vector[1; --1; 1]}`
- The convex hull of `{vector[--1; 1; --1], vector[--1; 1; 1]}`
- The convex hull of `{vector[--1; 1; --1], vector[1; 1; --1]}`
- The convex hull of `{vector[--1; 1; 1], vector[1; 1; 1]}`
- The convex hull of `{vector[1; --1; --1], vector[1; --1; 1]}`
- The convex hull of `{vector[1; --1; --1], vector[1; 1; --1]}`
- The convex hull of `{vector[1; --1; 1], vector[1; 1; 1]}`
- The convex hull of `{vector[1; 1; --1], vector[1; 1; 1]}`

### Informal sketch
- This theorem proves that the edges of the standard cube are exactly the twelve line segments connecting adjacent vertices.
- The proof uses `COMPUTE_EDGES_TAC`, which likely automates the reasoning based on:
    - `std_cube`: definition of the standard cube.
    - `STD_CUBE_FULLDIM`: The standard cube has full dimension.
    - `CUBE_FACETS`: a theorem characterizing the facets (faces) of the standard cube, probably in terms of convex hulls of vertices. Specifically, `COMPUTE_EDGES_TAC` likely:
        - Enumerates all possible sets `e` that are convex hulls of two vertices of the cube.
        - Checks if each such `e` is a face of the cube using `CUBE_FACETS`.
        - Verifies that the affine dimension of `e` is 1 in each case.
        - Shows that any face `e` of dimension 1 must be one of these convex hulls.

### Mathematical insight
This theorem provides a concrete characterization of the edges of the standard cube. It is a fundamental geometric property that is crucial for reasoning about the cube's structure and its relationship to other geometric objects. It connects the abstract notion of "face" and "affine dimension" with a concrete geometric representation as line segments between specific points.

### Dependencies
- `std_cube`
- `STD_CUBE_FULLDIM`
- `CUBE_FACETS`


---

## OCTAHEDRON_EDGES

### Name of formal statement
OCTAHEDRON_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OCTAHEDRON_EDGES = prove
 (`!e. e face_of std_octahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[-- &1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; -- &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &1; &0]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&1; &0; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; -- &1; &0], vector[&0; &0; &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; -- &1]} \/
       e = convex hull {vector[&0; &1; &0], vector[&0; &0; &1]}`,
   COMPUTE_EDGES_TAC
     std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_FACETS);;
```

### Informal statement
For all `e`, `e` is a face of the standard octahedron and the affine dimension of `e` is equal to 1 if and only if `e` is equal to one of the following convex hulls:
- The convex hull of the vectors `[-1; 0; 0]` and `[0; -1; 0]`
- The convex hull of the vectors `[-1; 0; 0]` and `[0; 1; 0]`
- The convex hull of the vectors `[-1; 0; 0]` and `[0; 0; -1]`
- The convex hull of the vectors `[-1; 0; 0]` and `[0; 0; 1]`
- The convex hull of the vectors `[1; 0; 0]` and `[0; -1; 0]`
- The convex hull of the vectors `[1; 0; 0]` and `[0; 1; 0]`
- The convex hull of the vectors `[1; 0; 0]` and `[0; 0; -1]`
- The convex hull of the vectors `[1; 0; 0]` and `[0; 0; 1]`
- The convex hull of the vectors `[0; -1; 0]` and `[0; 0; -1]`
- The convex hull of the vectors `[0; -1; 0]` and `[0; 0; 1]`
- The convex hull of the vectors `[0; 1; 0]` and `[0; 0; -1]`
- The convex hull of the vectors `[0; 1; 0]` and `[0; 0; 1]`

### Informal sketch
This theorem identifies the edges of the standard octahedron. The proof likely proceeds as follows:
- The tactic `COMPUTE_EDGES_TAC` is invoked which likely automates the verification of the edges.
- `std_octahedron` is passed to the tactic, providing the definition of the object.
- `STD_OCTAHEDRON_FULLDIM` certifies that octahedron is of full dimension `3`.
- `OCTAHEDRON_FACETS` provides the facets (faces) of the octahedron, which are then used to compute the edges.

### Mathematical insight
The theorem provides a concrete description of the edges of the standard octahedron, which are line segments connecting the vertices of the octahedron's faces. These edges correspond to the 1-dimensional faces of the octahedron. The octahedron is defined as the convex hull of the six points (+/- 1, 0, 0), (0, +/- 1, 0), and (0, 0, +/- 1).

### Dependencies
- Definitions: `std_octahedron`
- Theorems: `STD_OCTAHEDRON_FULLDIM`, `OCTAHEDRON_FACETS`


---

## DODECAHEDRON_EDGES

### Name of formal statement
DODECAHEDRON_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DODECAHEDRON_EDGES = prove
 (`!e. e face_of std_dodecahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; -- &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; &1; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; -- &1; -- &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; &1; -- &1]} \/
       e = convex hull {vector[-- &1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_EDGES_TAC
    STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_FACETS);;
```
### Informal statement
For all `e`, `e` is a face of the standard dodecahedron and the affine dimension of `e` is equal to 1 if and only if `e` is equal to one of the 30 convex hulls formed by pairs of vertices of the standard dodecahedron. The vertices used to form the convex hulls are:

- `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; &1]}`
- `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[-- &1; &1; &1]}`
- `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; -- &1; -- &1]}`
- `convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[-- &1; &1; -- &1]}`
- `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`
- `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; -- &1]}`
- `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1; &1]}`
- `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]}`
- `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; -- &1]}`
- `convex hull {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1; &1]}`
- `convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; -- &1]}`
- `convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[-- &1; -- &1; &1]}`
- `convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; -- &1]}`
- `convex hull {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[-- &1; &1; &1]}`
- `convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; -- &1; &1]}`
- `convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)], vector[&1; &1; &1]}`
- `convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; -- &1; -- &1]}`
- `convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&1; &1; -- &1]}`
- `convex hull {vector[-- &1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[-- &1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[-- &1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[-- &1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[&1; -- &1; -- &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[&1; -- &1; &1], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[&1; &1; &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
- `convex hull {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`

### Informal sketch
The theorem `DODECAHEDRON_EDGES` asserts that the edges of the standard dodecahedron are precisely the convex hulls of specified pairs of vertices.

The proof likely proceeds as follows:
- Start with the definition of the `std_dodecahedron` and its faces (`face_of`).
- Establish that the affine dimension (`aff_dim`) of an edge is 1.
- Show that each of the 30 specified convex hulls is indeed an edge of the `std_dodecahedron`.
- Show that any edge of the `std_dodecahedron` must be one of the 30 specified convex hulls.
The tactics `COMPUTE_EDGES_TAC`, `STD_DODECAHEDRON`, `STD_DODECAHEDRON_FULLDIM`, and `DODECAHEDRON_FACETS` are used in the proof.

### Mathematical insight
This theorem provides a concrete characterization of the edges of the standard dodecahedron in terms of the convex hulls of its vertices. It explicitly lists all 30 edges by specifying their endpoints. This characterization is useful for reasoning about the geometric and topological properties of the dodecahedron.

### Dependencies
- Definitions:
  - `STD_DODECAHEDRON`
- Theorems:
  - `STD_DODECAHEDRON_FULLDIM`
  - `DODECAHEDRON_FACETS`


---

## ICOSAHEDRON_EDGES

### Name of formal statement
ICOSAHEDRON_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ICOSAHEDRON_EDGES = prove
 (`!e. e face_of std_icosahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_EDGES_TAC
    STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_FACETS);;
```
### Informal statement
For all sets `e`, `e` is a face of the standard icosahedron and the affine dimension of `e` is equal to 1 if and only if `e` is equal to one of the 30 convex hulls formed by pairs of vertices chosen from the following list:
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]}`
`convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&1; &1 / &2 + &1 / &2 * sqrt (&5); &0], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)], vector[&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`
`convex hull {vector[&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)], vector[&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`

### Informal sketch
The theorem states that a set `e` is an edge of the standard icosahedron if and only if it is one of the 30 line segments connecting pairs of vertices of the icosahedron. The proof, using `COMPUTE_EDGES_TAC`, likely proceeds by:

- Showing that each of the 30 listed convex hulls is indeed a face of `std_icosahedron` with affine dimension 1.
- Showing that there are no other faces of `std_icosahedron` with affine dimension 1. This likely involves considering all possible pairs of vertices and demonstrating that the convex hull formed by each such pair coincides with one of the 30 listed edges.

The tactic `COMPUTE_EDGES_TAC`, together with lemmas like `STD_ICOSAHEDRON`, `STD_ICOSAHEDRON_FULLDIM`, and `ICOSAHEDRON_FACETS`, automates this process, ensuring that all necessary geometric and algebraic calculations are performed rigorously.

### Mathematical insight
This theorem provides a precise characterization of the edges of the standard icosahedron. It explicitly identifies each edge as the convex hull of a pair of vertices, providing a concrete representation of the icosahedron's structure.  The result is important for reasoning about the combinatorial and geometric properties of the icosahedron in a formalized setting. It links the abstract notion of a "face" to specific geometric objects (convex hulls of vertex pairs).

### Dependencies
- `STD_ICOSAHEDRON`
- `STD_ICOSAHEDRON_FULLDIM`
- `ICOSAHEDRON_FACETS`

### Porting notes (optional)
- The representations of real numbers and vectors could be different in other proof assistants.
- The definition of `convex hull` and the tactic `COMPUTE_EDGES_TAC` may need to be reimplemented or adapted in the target proof assistant.


---

## COMPUTE_VERTICES_TAC

### Name of formal statement
COMPUTE_VERTICES_TAC

### Type of the formal statement
Tactical

### Formal Content
```ocaml
let COMPUTE_VERTICES_TAC defn fulldim edges =
  GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
      `?e:real^3->bool. (e face_of p /\ aff_dim e = &1) /\
                        (v face_of e /\ aff_dim v = &0)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THENL [STRIP_TAC; MESON_TAC[FACE_OF_TRANS]] THEN
    MP_TAC(ISPECL [lhs(concl defn); `v:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        CONJ_TAC THEN
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      REWRITE_TAC[facet_of] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`f:real^3->bool`; `v:real^3->bool`]
        FACE_OF_POLYHEDRON_SUBSET_FACET) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_POLYHEDRON_POLYHEDRON THEN
        FIRST_ASSUM(fun th ->
          EXISTS_TAC (rand(concl th)) THEN
          CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]) THEN
        REWRITE_TAC[defn] THEN
        MATCH_MP_TAC POLYHEDRON_CONVEX_HULL THEN
        REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
        ASM_MESON_TAC[FACE_OF_FACE];
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV;
        DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^3->bool)->int`) THEN
        ASM_REWRITE_TAC[fulldim; AFF_DIM_EMPTY] THEN
        CONV_TAC INT_REDUCE_CONV];
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[facet_of] THEN
      ASM_REWRITE_TAC[fulldim] THEN CONV_TAC INT_REDUCE_CONV THEN
      ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_TRANS]];
    REWRITE_TAC[edges] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    REWRITE_TAC[AFF_DIM_EQ_0; RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[MESON[]
     `v face_of s /\ v = {a} <=> {a} face_of s /\ v = {a}`] THEN
    REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; FACE_OF_SING] THEN
    REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
    REWRITE_TAC[TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`] THEN
    REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
    REWRITE_TAC[DISJ_ACI]];;
```

### Informal statement
The tactic `COMPUTE_VERTICES_TAC` takes as input a definition `defn` (presumably defining a polyhedron `p`), a hypothesis `fulldim` stating that the affine dimension of `p` is 3, and a theorem `edges` characterizing the edges of `p`. The goal is to prove that for every polyhedron `p`, there exists an edge `e` which is a face of `p` and has affine dimension 1, and a vertex `v` which is a face of `e` and has affine dimension 0. The tactic proceeds by discharging a series of subgoals related to the properties of faces, affine dimensions and convex hulls, culminating in a complete enumeration of the vertices of the polyhedron `p` and proving that each such vertex is an extreme point of `p`.

### Informal sketch
The tactic `COMPUTE_VERTICES_TAC` is structured as follows:

- Start with a general tactic (`GEN_TAC`).
- Use `MATCH_MP_TAC EQ_TRANS` to apply transitivity of equality.
- Introduce an existential quantifier using `EXISTS_TAC` for the existence of an edge `e` and a vertex `v` satisfying the face and dimension conditions. The `vsubst` part substitutes the left-hand side of the definition `defn` into the goal.
- Split the conjunction (`CONJ_TAC`) to handle the existence of the edge and vertex separately.

Then two main subgoals are targeted in parallel using `CONJ_TAC THENL`:
- The first branch proves that any vertex identified via the edges is indeed a face of the polyhedron:
    - Simplify and apply transitivity of the `face_of` relationship using `FACE_OF_TRANS`.
    - Apply `FACE_OF_POLYHEDRON_SUBSET_FACET`.
    - Apply simplification and rewriting using the definition `defn` along with theorems about convex hulls, finite sets, and affine dimensions.
    - Use `facet_of` and `X_CHOOSE_THEN` to extract a specific facet satisfying the condition.
- The second branch proves that any such vertex identified directly is indeed a face of the polyhedron:
    - Repeatedly split conjunctions for each edge.
    - Apply `FACE_OF_POLYHEDRON_POLYHEDRON` introducing an existence.
    - Apply simplification and rewriting using the definition `defn` along with theorems about convex hulls, finite sets, and affine dimensions.
    - Apply transitivity of the `face_of` relation to prove that certain faces are included.
    - Handle monotone existence using `MONO_EXISTS`.
    - Simplify using `facet_of`.
    - Use `FACE_OF_FACE` and `FACE_OF_TRANS`.
- The third branch makes deductions from the edge structure (`edges`) provided. This involves multiple steps of rewriting, simplification using tautologies, and theorems about existence and affine dimensions.

### Mathematical insight
The tactic aims to automatically enumerate the vertices of a polyhedron in 3D space, given a definition of the polyhedron, a statement that it has full dimension, and some properties of its edges. It seems to rely on the fact that vertices can be found by iteratively finding faces of lower dimension until a 0-dimensional face (a vertex) is reached. The tactic combines general proof strategies with specialized knowledge about polyhedra, faces, and affine dimensions.

### Dependencies
- Definitions: `face_of`, `aff_dim`, `facet_of`
- Theorems: `FACE_OF_TRANS`, `FACE_OF_POLYHEDRON_SUBSET_FACET`, `POLYHEDRON_CONVEX_HULL`, `FINITE_INSERT`, `FINITE_EMPTY`, `FACE_OF_POLYHEDRON_POLYHEDRON`, `FACE_OF_FACE`, `MONO_EXISTS`, `AFF_DIM_EMPTY`, `EXISTS_OR_THM`, `UNWIND_THM2`, `AFF_DIM_EQ_0`, `RIGHT_AND_EXISTS_THM`, `SEGMENT_CONVEX_HULL`, `FACE_OF_SING`, `EXTREME_POINT_OF_SEGMENT`, `DISJ_ACI`
- Tactic: `MESON_TAC`, `ASM_MESON_TAC`


---

## TETRAHEDRON_VERTICES

### Name of formal statement
TETRAHEDRON_VERTICES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TETRAHEDRON_VERTICES = prove
 (`!v. v face_of std_tetrahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; &1; &1]}`,
  COMPUTE_VERTICES_TAC
    std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_EDGES);;
```

### Informal statement
For all `v`, `v` is a face of the standard tetrahedron and the affine dimension of `v` is 0 if and only if `v` is equal to the set containing the vector `[-1, -1, 1]` or `v` is equal to the set containing the vector `[-1, 1, -1]` or `v` is equal to the set containing the vector `[1, -1, -1]` or `v` is equal to the set containing the vector `[1, 1, 1]`.

### Informal sketch
The theorem demonstrates that the vertices of the `std_tetrahedron` are exactly the singleton sets containing the vectors `[-1, -1, 1]`, `[-1, 1, -1]`, `[1, -1, -1]`, and `[1, 1, 1]`.

- The proof uses `COMPUTE_VERTICES_TAC` tactic, which simplifies the goal by considering the geometric properties of the `std_tetrahedron`.
- The tactic relies on the fact that `std_tetrahedron` is full-dimensional (specified by `STD_TETRAHEDRON_FULLDIM`) and utilizes the precomputed `TETRAHEDRON_EDGES`.
- The tactic computes the vertices by analyzing the faces of the tetrahedron and their affine dimensions.
- The condition `v face_of std_tetrahedron` means `v` is a face of the tetrahedron.
- The condition `aff_dim v = &0` signifies that the affine dimension of `v` is 0, implying that `v` is a vertex.

### Mathematical insight
This theorem provides a precise characterization of the vertices of the standard tetrahedron. It explicitly lists the coordinates of the vertices, which are essential for various geometric computations and reasoning about the tetrahedron's properties. The result connects the geometric notion of a vertex with its formal representation as a singleton set containing a specific vector.

### Dependencies
- Definitions:
  - `std_tetrahedron`
  - `face_of`
  - `aff_dim`
- Theorems:
  - `STD_TETRAHEDRON_FULLDIM`
  - `TETRAHEDRON_EDGES`
- Tactics:
  - `COMPUTE_VERTICES_TAC`


---

## CUBE_VERTICES

### Name of formal statement
CUBE_VERTICES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBE_VERTICES = prove
 (`!v. v face_of std_cube /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; -- &1]} \/
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [-- &1; &1; &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; -- &1; &1]} \/
       v = {vector [&1; &1; -- &1]} \/
       v = {vector [&1; &1; &1]}`,
  COMPUTE_VERTICES_TAC
    std_cube STD_CUBE_FULLDIM CUBE_EDGES);;
```
### Informal statement
For all `v`, `v` is a face of `std_cube` and the affine dimension of `v` is equal to 0 if and only if
       `v` is equal to the set containing the vector `[-- &1; -- &1; -- &1]` or
       `v` is equal to the set containing the vector `[-- &1; -- &1; &1]` or
       `v` is equal to the set containing the vector `[-- &1; &1; -- &1]` or
       `v` is equal to the set containing the vector `[-- &1; &1; &1]` or
       `v` is equal to the set containing the vector `[&1; -- &1; -- &1]` or
       `v` is equal to the set containing the vector `[&1; -- &1; &1]` or
       `v` is equal to the set containing the vector `[&1; &1; -- &1]` or
       `v` is equal to the set containing the vector `[&1; &1; &1]`.

### Informal sketch
The theorem is proved by the tactic `COMPUTE_VERTICES_TAC` applied to `std_cube`, `STD_CUBE_FULLDIM` and `CUBE_EDGES`. The tactic presumably automatically computes the vertices of the standard cube given that the standard cube is full dimensional and the definition of cube edges. It likely proceeds by:
- Using the definition of `face_of` and `aff_dim`.
- Enumerating all possible sets of vectors that could be vertices of the cube.
- Proving that the given sets are indeed the only ones satisfying the conditions.

### Mathematical insight
This theorem characterizes the vertices of the standard cube (`std_cube`) in 3-dimensional space. Specifically, it states that a vector set `v` is a vertex of the standard cube (i.e., a 0-dimensional face) if and only if `v` is one of the eight corners of the cube, whose coordinates are either -1 or 1 in each dimension. This characterization is fundamental in geometric reasoning and is used in various applications involving cubes and their properties.

### Dependencies
- Definitions: `face_of`, `std_cube`, `aff_dim`
- Theorems: `STD_CUBE_FULLDIM`, `CUBE_EDGES`
- Tactic: `COMPUTE_VERTICES_TAC`

### Porting notes (optional)
- The main challenge is replicating the automation provided by  `COMPUTE_VERTICES_TAC`. In other proof assistants, one might need to manually expand the definitions and perform the case analysis, or develop a similar automated tactic.
- Ensure that the definitions of `face_of`, `std_cube`, and `aff_dim` are correctly translated and that the required properties (`STD_CUBE_FULLDIM` and `CUBE_EDGES`) are established.


---

## OCTAHEDRON_VERTICES

### Name of formal statement
OCTAHEDRON_VERTICES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OCTAHEDRON_VERTICES = prove
 (`!v. v face_of std_octahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; &0; &0]} \/
       v = {vector [&1; &0; &0]} \/
       v = {vector [&0; -- &1; &0]} \/
       v = {vector [&0; &1; &0]} \/
       v = {vector [&0; &0; -- &1]} \/
       v = {vector [&0; &0; &1]}`,
   COMPUTE_VERTICES_TAC
     std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_EDGES);;
```
### Informal statement
For all `v`, `v` is a face of the standard octahedron and the affine dimension of `v` is equal to 0 if and only if `v` is equal to the set containing the vector with components -1, 0, and 0, or `v` is equal to the set containing the vector with components 1, 0, and 0, or `v` is equal to the set containing the vector with components 0, -1, and 0, or `v` is equal to the set containing the vector with components 0, 1, and 0, or `v` is equal to the set containing the vector with components 0, 0, and -1, or `v` is equal to the set containing the vector with components 0, 0, and 1.

### Informal sketch
The theorem states that the vertices of the standard octahedron are precisely the six points (±1, 0, 0), (0, ±1, 0), and (0, 0, ±1). The proof proceeds using `COMPUTE_VERTICES_TAC`, which, based on the provided octahedron (`std_octahedron`), its full dimension (`STD_OCTAHEDRON_FULLDIM`), and its edges (`OCTAHEDRON_EDGES`), computes the vertices.

### Mathematical insight
This theorem provides a concrete characterization of the vertices of the standard octahedron in terms of their Cartesian coordinates. It links the geometric notion of a vertex as a 0-dimensional face to specific vector values. The octahedron is defined as the convex hull of these vertices.

### Dependencies
- Definitions:
  - `face_of`
  - `std_octahedron`
  - `aff_dim`
  - `vector`

- Theorems:
  - `STD_OCTAHEDRON_FULLDIM`
  - `OCTAHEDRON_EDGES`

- Tactics:
  - `COMPUTE_VERTICES_TAC`


---

## DODECAHEDRON_VERTICES

### Name of formal statement
DODECAHEDRON_VERTICES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DODECAHEDRON_VERTICES = prove
 (`!v. v face_of std_dodecahedron /\ aff_dim v = &0 <=>
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[-- &1; -- &1; -- &1]} \/
       v = {vector[-- &1; -- &1; &1]} \/
       v = {vector[-- &1; &1; -- &1]} \/
       v = {vector[-- &1; &1; &1]} \/
       v = {vector[&1; -- &1; -- &1]} \/
       v = {vector[&1; -- &1; &1]} \/
       v = {vector[&1; &1; -- &1]} \/
       v = {vector[&1; &1; &1]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_VERTICES_TAC
    STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_EDGES);;
```
### Informal statement
For all `v`, `v` is a face of the standard dodecahedron and the affine dimension of `v` is 0 if and only if `v` is equal to one of the following 20 vectors:
`{vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]}`,
`{vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]}`,
`{vector[-- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`,
`{vector[-- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]}`,
`{vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]}`,
`{vector[&1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5); &0]}`,
`{vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]}`,
`{vector[&1 / &2 + &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]}`,
`{vector[-- &1; -- &1; -- &1]}`,
`{vector[-- &1; -- &1; &1]}`,
`{vector[-- &1; &1; -- &1]}`,
`{vector[-- &1; &1; &1]}`,
`{vector[&1; -- &1; -- &1]}`,
`{vector[&1; -- &1; &1]}`,
`{vector[&1; &1; -- &1]}`,
`{vector[&1; &1; &1]}`,
`{vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`,
`{vector[&0; -- &1 / &2 + &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`,
`{vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5)]}`,
`{vector[&0; &1 / &2 + -- &1 / &2 * sqrt (&5); &1 / &2 + &1 / &2 * sqrt (&5)]}`.

### Informal sketch
The theorem statement is proved using the tactic `COMPUTE_VERTICES_TAC` and requires the theorems `STD_DODECAHEDRON`, `STD_DODECAHEDRON_FULLDIM`, and `DODECAHEDRON_EDGES`. The tactic likely involves:
- Using `STD_DODECAHEDRON` to unfold the definition of the standard dodecahedron.
- Applying `STD_DODECAHEDRON_FULLDIM` to establish that the standard dodecahedron has full dimension.
- Applying `DODECAHEDRON_EDGES` which likely defines the edges of the dodecahedron
- Verifying that the 20 listed vectors are indeed vertices of the dodecahedron by checking that they are faces with affine dimension 0.

### Mathematical insight
This theorem provides a concrete description of the vertices of the standard dodecahedron. The standard dodecahedron is centered at the origin. This theorem explicitly lists all 20 vertices as vectors in 3D space, which can be useful for geometric computations or visualizations.

### Dependencies
- `STD_DODECAHEDRON`
- `STD_DODECAHEDRON_FULLDIM`
- `DODECAHEDRON_EDGES`


---

## ICOSAHEDRON_VERTICES

### Name of formal statement
ICOSAHEDRON_VERTICES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ICOSAHEDRON_VERTICES = prove
 (`!v. v face_of std_icosahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1]} \/
       v = {vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]} \/
       v = {vector [-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]} \/
       v = {vector [&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       v = {vector [&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}`,
  COMPUTE_VERTICES_TAC
    STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_EDGES);;
```

### Informal statement
For all `v`, `v` is a vertex of the standard icosahedron, and the affine dimension of `v` is 0, if and only if `v` is equal to one of the following vectors:
{vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1]},
{vector [-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1]},
{vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; -- &1]},
{vector [&1 / &2 + &1 / &2 * sqrt (&5); &0; &1]},
{vector [-- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]},
{vector [-- &1; &1 / &2 + &1 / &2 * sqrt (&5); &0]},
{vector [&1; -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]},
{vector [&1; &1 / &2 + &1 / &2 * sqrt (&5); &0]},
{vector [&0; -- &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]},
{vector [&0; -- &1; &1 / &2 + &1 / &2 * sqrt (&5)]},
{vector [&0; &1; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]},
{vector [&0; &1; &1 / &2 + &1 / &2 * sqrt (&5)]}.

### Informal sketch
The theorem asserts that the vertices of the standard icosahedron are exactly a specific set of twelve 3D vectors.

The proof uses `COMPUTE_VERTICES_TAC`, which presumably automates the determination of the vertices, given:
- `STD_ICOSAHEDRON`: a definition of the standard icosahedron.
- `STD_ICOSAHEDRON_FULLDIM`: a theorem stating the icosahedron is full dimensional.
- `ICOSAHEDRON_EDGES`: a reference to related definitions or properties of the icosahedron edges.

The core strategy appears to involve computing the vertices of the icosahedron based on its definition and then verifying that they match the given set of twelve vectors which probably uses the properties of the edges of the icosahedron to determine vertices.

### Mathematical insight
This theorem provides an explicit and concrete description of the vertices of the standard icosahedron. This is useful for calculations and further geometric reasoning about the icosahedron. The vertices are expressed in terms of the golden ratio (represented by the square root of 5), reflecting the icosahedron's symmetry.

### Dependencies
- `STD_ICOSAHEDRON`
- `STD_ICOSAHEDRON_FULLDIM`
- `ICOSAHEDRON_EDGES`


---

## EDGES_PER_VERTEX_TAC

### Name of formal statement
EDGES_PER_VERTEX_TAC

### Type of the formal statement
Tactic

### Formal Content
```ocaml
let EDGES_PER_VERTEX_TAC defn edges verts =
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   (vsubst[lhs(concl defn),`p:real^3->bool`]
     `CARD {e | (e face_of p /\ aff_dim(e) = &1) /\
                (v:real^3->bool) face_of e}`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[FACE_OF_FACE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v:real^3->bool` verts) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[edges] THEN
  REWRITE_TAC[SET_RULE
   `{e | (P e \/ Q e) /\ R e} =
    {e | P e /\ R e} UNION {e | Q e /\ R e}`] THEN
  REWRITE_TAC[MESON[FACE_OF_SING]
   `e = a /\ {x} face_of e <=> e = a /\ x extreme_point_of a`] THEN
  REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
  REWRITE_TAC[EMPTY_GSPEC; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
  REWRITE_TAC[SET_RULE `{x} UNION s = x INSERT s`] THEN MATCH_MP_TAC
   (MESON[HAS_SIZE] `s HAS_SIZE n ==> CARD s = n`) THEN
  REPEAT
  (MATCH_MP_TAC CARD_EQ_LEMMA THEN REPEAT CONJ_TAC THENL
    [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
     REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM; SEGMENT_EQ] THEN
     REPEAT CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
      `~(a = c /\ b = d) /\ ~(a = d /\ b = c) /\ ~(a = b /\ c = d)
       ==> ~({a,b} = {c,d})`) THEN
     PURE_ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
     CONV_TAC(ONCE_DEPTH_CONV VECTOR3_EQ_0_CONV) THEN
     REWRITE_TAC[] THEN NO_TAC;
     ALL_TAC]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES];;
```
### Informal statement
The tactic `EDGES_PER_VERTEX_TAC` takes as input a definition `defn` (presumably defining the polyhedron `p`), a theorem `edges` (characterizing the set of edges), and a theorem `verts` (characterizing the set of vertices of `p`). It then proves a theorem about the number of edges meeting at each vertex.

### Informal sketch
The tactic `EDGES_PER_VERTEX_TAC` proceeds as follows:

- It simplifies the goal using `REPEAT STRIP_TAC` and `MATCH_MP_TAC EQ_TRANS`.
- It introduces an existential quantifier over a predicate `v:real^3->bool` representing a vertex using `EXISTS_TAC`, substituting the left-hand side of the conclusion of `defn` for `p`. The existential statement to be proved states that the cardinality of the set of edges `e` that are faces of `p` with dimension 1, and for which `v` is a face of `e`, is a certain value (presumably corresponding to the number of edges meeting at a vertex).
- It splits the goal into two subgoals using `CONJ_TAC`.
  - The first subgoal is solved by applying `AP_TERM_TAC`, rewriting with `EXTENSION` and `IN_ELIM_THM`, and applying `ASM_MESON_TAC` with hypothesis `FACE_OF_FACE`.
  - The second subgoal is solved by `ALL_TAC`.
- It applies the theorem `verts` to the goal using `MP_TAC` and `ISPEC`.
- It simplifies the goal using `ASM_REWRITE_TAC`.
- It discharges the assumption using `DISCH_THEN` and applies `REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC`.
- It rewrites with theorems `edges` and `SET_RULE ...` to manipulate set expressions.
- It rewrites using theorems `MESON[FACE_OF_SING] ...`, `GSYM SEGMENT_CONVEX_HULL`, and `EXTREME_POINT_OF_SEGMENT`.
- It rewrites using `GSYM VECTOR_SUB_EQ` and applies conversions to simplify vector expressions with `VECTOR3_SUB_CONV` and `VECTOR3_EQ_0_CONV`.
- It rewrites using `EMPTY_GSPEC` and `UNION_EMPTY`.
- It rewrites using `SET_RULE` theorems to simplify sets.
- It applies `MATCH_MP_TAC` with `MESON[HAS_SIZE] ...` to relate set size to cardinality.
- It repeatedly applies a tactic that uses `CARD_EQ_LEMMA`, splits the goals, and applies conversions to reduce numerical expressions. Inside this tactic, it also rewrites using theorems like `IN_INSERT`, `NOT_IN_EMPTY`, `DE_MORGAN_THM`, and `SEGMENT_EQ`. It manipulates vector expressions by rewriting with `GSYM VECTOR_SUB_EQ` and applying conversions `VECTOR3_SUB_CONV` and `VECTOR3_EQ_0_CONV`.
- Finally, simplifies the goal using `NUM_REDUCE_CONV` and `CONJUNCT1 HAS_SIZE_CLAUSES`.

### Mathematical insight
The tactic aims to prove that the number of edges meeting at each vertex of a polyhedron is a fixed number. It uses a combination of set-theoretic manipulations, rewriting with geometric definitions, and arithmetic simplification to arrive at the desired result. The tactic leverages theorems characterizing faces, edges, and vertices, as well as properties of convex hulls and vector arithmetic.

### Dependencies
- Theorems: `EXTENSION`, `IN_ELIM_THM`, `FACE_OF_FACE`, `FACE_OF_SING`, `SEGMENT_CONVEX_HULL`, `EXTREME_POINT_OF_SEGMENT`, `VECTOR_SUB_EQ`, `EMPTY_GSPEC`, `UNION_EMPTY`, `HAS_SIZE`, `CARD_EQ_LEMMA`, `IN_INSERT`, `NOT_IN_EMPTY`, `DE_MORGAN_THM`, `SEGMENT_EQ`, `CONJUNCT1 HAS_SIZE_CLAUSES`
- Definitions: `FACE_OF`, `aff_dim`, `extreme_point_of`, `HAS_SIZE`
- Tactics: `REPEAT STRIP_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, `CONJ_TAC`, `AP_TERM_TAC`, `REWRITE_TAC`, `ASM_MESON_TAC`, `MP_TAC`, `ISPEC`, `ASM_REWRITE_TAC`, `DISCH_THEN`, `REPEAT_TCL`, `DISJ_CASES_THEN`, `SUBST1_TAC`, `ONCE_REWRITE_TAC`, `CONV_TAC`, `ONCE_DEPTH_CONV`, `NUM_REDUCE_CONV`, `ALL_TAC`,`PURE_ONCE_REWRITE_TAC`, `NO_TAC`
- Set Rules: `SET_RULE`

### Porting notes (optional)
- The tactic relies heavily on rewriting and conversion. Proof assistants with strong rewriting capabilities will be beneficial.
- The use of `MESON` suggests that substantial first-order reasoning is involved. The efficiency of the automated theorem prover will be important.
- The tactic makes intensive transformations that could be achieved with different tactics.


---

## TETRAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
TETRAHEDRON_EDGES_PER_VERTEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TETRAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_tetrahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`,
  EDGES_PER_VERTEX_TAC
    std_tetrahedron TETRAHEDRON_EDGES TETRAHEDRON_VERTICES);;
```
### Informal statement
For all sets `v`, if `v` is a face of the standard tetrahedron (`std_tetrahedron`) and the affine dimension of `v` is 0, then the cardinality of the set of edges `e` such that `e` is a face of the standard tetrahedron, the affine dimension of `e` is 1, and `v` is a subset of `e`, is equal to 3.

### Informal sketch
The proof establishes that each vertex of the standard tetrahedron has three edges connected to it.
- The theorem quantifies over all sets `v`. The assumption `v face_of std_tetrahedron /\ aff_dim(v) = &0` ensures that `v` is a vertex of the standard tetrahedron. The goal is, for such `v`, to show that exactly three edges of the tetrahedron contain `v`.
- The theorem is proved by applying the tactic `EDGES_PER_VERTEX_TAC` with the arguments `std_tetrahedron`, `TETRAHEDRON_EDGES`, and `TETRAHEDRON_VERTICES`. This tactic likely uses the definitions of `std_tetrahedron`, `TETRAHEDRON_EDGES` (which should define the edges of a tetrahedron), and `TETRAHEDRON_VERTICES` (which should define the vertices of tetrahedron) to enumerate the edges and vertices and directly verify the property for the standard tetrahedron.

### Mathematical insight
This theorem formalizes a basic geometric property of a tetrahedron: each vertex is connected to three edges. It's a foundational result in discrete geometry and topology. The result is important when reasoning about the structure of tetrahedra and simplicial complexes.

### Dependencies
- `std_tetrahedron` (definition of the standard tetrahedron)
- `TETRAHEDRON_EDGES` (definition of the edges of the tetrahedron)
- `TETRAHEDRON_VERTICES` (definition of the vertices of the tetrahedron)
- `EDGES_PER_VERTEX_TAC` (a tactic to prove the result)
- `face_of` (definition of a face)
- `aff_dim` (affine dimension)
- `CARD` (cardinality of a set)
- `SUBSET` (subset relation)


---

## CUBE_EDGES_PER_VERTEX

### Name of formal statement
CUBE_EDGES_PER_VERTEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBE_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_cube /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`,
  EDGES_PER_VERTEX_TAC
    std_cube CUBE_EDGES CUBE_VERTICES);;
```

### Informal statement
For all `v`, if `v` is a face of `std_cube` and the affine dimension of `v` is 0, then the cardinality of the set of `e` such that `e` is a face of `std_cube`, the affine dimension of `e` is 1, and `v` is a subset of `e`, is equal to 3.

### Informal sketch
The theorem states that each vertex of the standard cube is contained in exactly 3 edges of the standard cube. The proof proceeds by:
- Applying `EDGES_PER_VERTEX_TAC` which is a tactic specifically designed to prove this kind of statement.
- `EDGES_PER_VERTEX_TAC` takes the standard cube (`std_cube`), the set of edges (`CUBE_EDGES`) and the set of vertices (`CUBE_VERTICES`) as arguments. The tactic uses properties of the standard cube and its faces to deduce that each vertex lies on three edges.

### Mathematical insight
This theorem captures the geometric property that each vertex in a cube is an endpoint of three edges. This is a fundamental characteristic of a cube's structure. The statement is important for reasoning about the topology and combinatorics of cubes.

### Dependencies
- Theorem: `EDGES_PER_VERTEX_TAC`
- Definition: `std_cube`
- Definition: `CUBE_EDGES`
- Definition: `CUBE_VERTICES`


---

## OCTAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
OCTAHEDRON_EDGES_PER_VERTEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OCTAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_octahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 4`,
  EDGES_PER_VERTEX_TAC
    std_octahedron OCTAHEDRON_EDGES OCTAHEDRON_VERTICES);;
```
### Informal statement
For all sets `v`, if `v` is a face of the standard octahedron (`std_octahedron`) and the affine dimension of `v` is 0, then the cardinality of the set of sets `e` such that `e` is a face of the standard octahedron, the affine dimension of `e` is 1, and `v` is a subset of `e`, is equal to 4.

### Informal sketch
The theorem states that each vertex of the standard octahedron is adjacent to exactly 4 edges. The proof, using `EDGES_PER_VERTEX_TAC`, appears to rely on:
- Facts about `std_octahedron`, `OCTAHEDRON_EDGES`, and `OCTAHEDRON_VERTICES`, presumably pre-established definitions or theorems characterizing the vertices and edges of the standard octahedron.
- Specifically, the tactic `EDGES_PER_VERTEX_TAC` likely expands the definition of `std_octahedron`, enumerates the vertices given `OCTAHEDRON_VERTICES` and edges `OCTAHEDRON_EDGES`, filters for faces `e` of dimension 1 (edges) containing the vertex `v`, and computes the cardinality.
- The step involves verifying that each vertex, which has affine dimension 0, is contained within exactly four edges, which have affine dimension 1.

### Mathematical insight
This theorem confirms a basic geometric property of the standard octahedron: each vertex is contained in exactly four edges.  This is a fundamental property that distinguishes the octahedron's structure.

### Dependencies
- Definition: `std_octahedron`
- Definition: `OCTAHEDRON_EDGES`
- Definition: `OCTAHEDRON_VERTICES`
- Tactic: `EDGES_PER_VERTEX_TAC`


---

## DODECAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
DODECAHEDRON_EDGES_PER_VERTEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DODECAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_dodecahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 3`,
  EDGES_PER_VERTEX_TAC
    STD_DODECAHEDRON DODECAHEDRON_EDGES DODECAHEDRON_VERTICES);;
```
### Informal statement
For all `v`, if `v` is a face of the standard dodecahedron and the affine dimension of `v` is equal to 0, then the cardinality of the set of `e` such that `e` is a face of the standard dodecahedron, the affine dimension of `e` is equal to 1, and `v` is a subset of `e`, is equal to 3.

### Informal sketch
The theorem states that each vertex of the standard dodecahedron is contained in exactly 3 edges of the dodecahedron. The proof likely involves the following steps:

- First, it uses theorem `EDGES_PER_VERTEX_TAC` which is specialized for proving properties about the number of edges incident to vertices in polyhedra
- The proof relies on the previously established definitions: `STD_DODECAHEDRON` (definition of the standard dodecahedron), `DODECAHEDRON_EDGES` (definition of the edges of the dodecahedron), and `DODECAHEDRON_VERTICES` (definition of the vertices of the dodecahedron).

### Mathematical insight
This theorem formalizes the geometric property that each vertex of a dodecahedron is the intersection point of three edges. This fact is fundamental to the structure and symmetry of the dodecahedron, and it is used in various geometric arguments and calculations involving this polyhedron.

### Dependencies
- Definitions: `STD_DODECAHEDRON`, `DODECAHEDRON_EDGES`, `DODECAHEDRON_VERTICES`
- Theorems: `EDGES_PER_VERTEX_TAC`


---

## ICOSAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
ICOSAHEADRON_EDGES_PER_VERTEX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ICOSAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_icosahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 5`,
  EDGES_PER_VERTEX_TAC
    STD_ICOSAHEDRON ICOSAHEDRON_EDGES ICOSAHEDRON_VERTICES);;
```
### Informal statement
For all `v`, if `v` is a face of the standard icosahedron and the affine dimension of `v` is 0, then the cardinality of the set of `e` such that `e` is a face of the standard icosahedron, the affine dimension of `e` is 1, and `v` is a subset of `e`, is 5.

### Informal sketch
The proof proceeds by:
- Applying `EDGES_PER_VERTEX_TAC`.
- This tactic likely unfolds the definitions of `std_icosahedron`, `ICOSAHEADRON_EDGES`, and `ICOSAHEADRON_VERTICES`.
- It then uses theorems or lemmas about the structure of the icosahedron to establish that each vertex of the icosahedron is contained in exactly 5 edges.

### Mathematical insight
This theorem establishes a fundamental property of the standard icosahedron: each vertex is contained in exactly five edges. This is a key characteristic of the icosahedron's geometry and topology.

### Dependencies
- Definitions:
    - `std_icosahedron`
    - `ICOSAHEADRON_EDGES`
    - `ICOSAHEADRON_VERTICES`

- Tactics:
    - `EDGES_PER_VERTEX_TAC`


---

## MULTIPLE_COUNTING_LEMMA

### Name of formal statement
MULTIPLE_COUNTING_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULTIPLE_COUNTING_LEMMA = prove
 (`!R:A->B->bool s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> CARD {y | y IN t /\ R x y} = m) /\
        (!y. y IN t ==> CARD {x | x IN s /\ R x y} = n)
        ==> m * CARD s = n * CARD t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:A->B->bool`; `\x:A y:B. 1`; `s:A->bool`; `t:B->bool`]
        NSUM_NSUM_RESTRICT) THEN
  ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT] THEN ARITH_TAC);;
```
### Informal statement
For any relation `R` between types `A` and `B`, and any sets `s` of type `A` and `t` of type `B`, if `s` and `t` are finite, and for all `x` in `s`, the cardinality of the set of `y` in `t` such that `R x y` holds is `m`, and for all `y` in `t`, the cardinality of the set of `x` in `s` such that `R x y` holds is `n`, then `m` times the cardinality of `s` is equal to `n` times the cardinality of `t`.

### Informal sketch
The proof proceeds by:
- Stripping the initial goal.
- Instantiating the theorem `NSUM_NSUM_RESTRICT` with `R`, the constant function `\x y. 1`, `s` and `t`, to rewrite both sides of the equation into double summations over the the sets `s` and `t` of the constant function 1 restricted by the relation `R`.
- Simplifying using `NSUM_CONST` and `FINITE_RESTRICT` to evaluate the summations using cardinality.
- Concluding the proof by appealing to an arithmetic tactic (`ARITH_TAC`).

### Mathematical insight
This theorem embodies a fundamental counting principle: if we count the number of pairs `(x, y)` in a relation `R` in two different ways (once summing over `x` and then over `y`, and once summing over `y` and then over `x`), the results must be equal. This is often called "double counting" or "counting in two ways". In combinatorics, it is a powerful technique. This particular formulation uses cardinalities to make the principle precise, particularly in the case where one element `x` is related to `m` elements `y` and each element `y` is related to `n` elements `x`.

### Dependencies
- `FINITE`
- `CARD`
- `NSUM_NSUM_RESTRICT`
- `NSUM_CONST`
- `FINITE_RESTRICT`


---

## SIZE_ZERO_DIMENSIONAL_FACES

### Name of formal statement
SIZE_ZERO_DIMENSIONAL_FACES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIZE_ZERO_DIMENSIONAL_FACES = prove
 (`!s:real^N->bool.
        polyhedron s
        ==> CARD {f | f face_of s /\ aff_dim f = &0} =
            CARD {v | v extreme_point_of s} /\
            (FINITE {f | f face_of s /\ aff_dim f = &0} <=>
             FINITE {v | v extreme_point_of s}) /\
            (!n. {f | f face_of s /\ aff_dim f = &0} HAS_SIZE n <=>
                 {v | v extreme_point_of s} HAS_SIZE n)`,
  REWRITE_TAC[RIGHT_AND_FORALL_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `{f | f face_of s /\ aff_dim f = &0} =
                IMAGE (\v:real^N. {v}) {v | v extreme_point_of s}`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[AFF_DIM_SING; FACE_OF_SING; IN_ELIM_THM] THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN MESON_TAC[];
    REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ;
      MATCH_MP_TAC FINITE_IMAGE_INJ_EQ;
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ] THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_EXTREME_POINTS] THEN SET_TAC[]]);;
```
### Informal statement
For any set `s` in `real^N` (N-dimensional real vector space), if `s` is a polyhedron, then the cardinality of the set of faces `f` of `s` with affine dimension equal to 0 is equal to the cardinality of the set of extreme points `v` of `s`. Furthermore, the set of faces `f` of `s` with affine dimension equal to 0 is finite if and only if the set of extreme points `v` of `s` is finite. Finally, for any number `n`, the set of faces `f` of `s` with affine dimension equal to 0 has size `n` if and only if the set of extreme points `v` of `s` has size `n`.

### Informal sketch
The proof proceeds as follows:
- First, the goal is reduced to showing that the set of zero-dimensional faces of `s` is equal to the image of the set of extreme points of `s` under the mapping that sends a point `v` to the singleton set containing `v`. In other words, `{f | f face_of s /\ aff_dim f = &0} = IMAGE (\v:real^N. {v}) {v | v extreme_point_of s}`.
- It is then shown that extreme points `v` of `s` are mapped to singleton faces `{v}` of `s` and that the affine dimension `aff_dim` of such singleton set is 0 (using `AFF_DIM_SING`, `FACE_OF_SING`, `IN_ELIM_THM`, `AFF_DIM_EQ_0`). This establishes the equality of the two sets.
- Then, using the fact that the image of a set under an injective mapping preserves cardinality, finiteness, and size (using theorems `CARD_IMAGE_INJ`, `FINITE_IMAGE_INJ_EQ`, `HAS_SIZE_IMAGE_INJ_EQ`), and that a polyhedron has finitely many extreme points if it is finite (`FINITE_POLYHEDRON_EXTREME_POINTS`), the result follows.

### Mathematical insight
The theorem establishes a direct correspondence between the zero-dimensional faces of a polyhedron (its vertices) and its extreme points. Essentially, it formalizes the intuition that in a polyhedron, the extreme points are precisely the zero-dimensional faces. The theorem leverages properties of set cardinality, finiteness and the injectivity of the mapping $v \mapsto \{v\}$ to relate the extreme points and 0-dimensional faces, and uses the fundamental fact that a polyhedron has a finite number of extreme points if the polyhedron itself is finite.

### Dependencies
- `AFF_DIM_SING`
- `FACE_OF_SING`
- `IN_ELIM_THM`
- `AFF_DIM_EQ_0`
- `CARD_IMAGE_INJ`
- `FINITE_IMAGE_INJ_EQ`
- `HAS_SIZE_IMAGE_INJ_EQ`
- `FINITE_POLYHEDRON_EXTREME_POINTS`

### Porting notes (optional)
The theorem relies heavily on set theory and cardinality arguments. Ensure that the target proof assistant has adequate support for these concepts. The mapping from a point to a singleton set might require explicit definition in some proof assistants. The `IMAGE` operator is frequently used in HOL Light to build sets using functions; other provers may have other conventions you will need to adjust the expressions to.


---

## PLATONIC_SOLIDS_LIMITS

### Name of formal statement
PLATONIC_SOLIDS_LIMITS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PLATONIC_SOLIDS_LIMITS = prove
 (`!p:real^3->bool m n.
    polytope p /\ aff_dim p = &3 /\
    (!f. f face_of p /\ aff_dim(f) = &2
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
    (!v. v face_of p /\ aff_dim(v) = &0
         ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)
    ==> m = 3 /\ n = 3 \/       // Tetrahedron
        m = 4 /\ n = 3 \/       // Cube
        m = 3 /\ n = 4 \/       // Octahedron
        m = 5 /\ n = 3 \/       // Dodecahedron
        m = 3 /\ n = 5          // Icosahedron`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^3->bool` EULER_RELATION) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `m * CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1} /\
    n * CARD {v | v face_of p /\ aff_dim v = &0} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1}`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MULTIPLE_COUNTING_LEMMA THENL
     [EXISTS_TAC `\(f:real^3->bool) (e:real^3->bool). e SUBSET f`;
      EXISTS_TAC `\(v:real^3->bool) (e:real^3->bool). v SUBSET e`] THEN
    ONCE_REWRITE_TAC[SET_RULE `f face_of s <=> f IN {f | f face_of s}`] THEN
    ASM_SIMP_TAC[FINITE_POLYTOPE_FACES; FINITE_RESTRICT] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`p:real^3->bool`; `e:real^3->bool`]
          POLYHEDRON_RIDGE_TWO_FACETS) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON] THEN ANTS_TAC THENL
       [CONV_TAC INT_REDUCE_CONV THEN DISCH_THEN SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC;
        CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`f1:real^3->bool`; `f2:real^3->bool`] THEN
        STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `CARD {f1:real^3->bool,f2}` THEN CONJ_TAC THENL
         [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
          REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
          ASM_MESON_TAC[];
          ASM_SIMP_TAC[CARD_CLAUSES; IN_INSERT; FINITE_RULES;
                       NOT_IN_EMPTY; ARITH]]];
      SUBGOAL_THEN `?a b:real^3. e = segment[a,b]` STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN
        REPEAT CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC;
          MATCH_MP_TAC FACE_OF_IMP_COMPACT THEN
          EXISTS_TAC `p:real^3->bool` THEN
          ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT];
          ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
          MP_TAC(ISPEC `e:real^3->bool` AFF_DIM) THEN
          DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` MP_TAC) THEN
          ASM_REWRITE_TAC[INT_ARITH `&1:int = b - &1 <=> b = &2`] THEN
          DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
          ASM_CASES_TAC `FINITE(b:real^3->bool)` THENL
           [ALL_TAC; ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]] THEN
          REWRITE_TAC[INT_OF_NUM_EQ] THEN STRIP_TAC THEN
          SUBGOAL_THEN `(b:real^3->bool) HAS_SIZE 2` MP_TAC THENL
           [ASM_REWRITE_TAC[HAS_SIZE]; CONV_TAC(LAND_CONV HAS_SIZE_CONV)] THEN
          REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
          REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
          ASM_MESON_TAC[HULL_SUBSET]];
        ASM_CASES_TAC `a:real^3 = b` THENL
         [UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN
          ASM_REWRITE_TAC[SEGMENT_REFL; AFF_DIM_SING; INT_OF_NUM_EQ; ARITH_EQ];
          ALL_TAC] THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `CARD {v:real^3 | v extreme_point_of segment[a,b]}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
          EXISTS_TAC `\v:real^3. {v}` THEN
          REWRITE_TAC[IN_ELIM_THM; FACE_OF_SING; AFF_DIM_SING] THEN
          REPEAT CONJ_TAC THENL
           [ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
            REWRITE_TAC[SET_RULE `{x | x = a \/ x = b} = {a,b}`] THEN
            REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
            X_GEN_TAC `v:real^3` THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
            ASM_MESON_TAC[FACE_OF_TRANS; FACE_OF_IMP_SUBSET];
            X_GEN_TAC `s:real^3->bool` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
            DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
            DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
            DISCH_THEN(X_CHOOSE_THEN `v:real^3` SUBST_ALL_TAC) THEN
            REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `v:real^3` THEN
            ASM_REWRITE_TAC[GSYM FACE_OF_SING] THEN CONJ_TAC THENL
             [ASM_MESON_TAC[FACE_OF_FACE]; SET_TAC[]]];
          ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
          REWRITE_TAC[SET_RULE `{x | x = a \/ x = b} = {a,b}`] THEN
          ASM_SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY] THEN
          ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; ARITH]]]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `(a + b) - c = 2 ==> a + b = c + 2`)) THEN
  SUBGOAL_THEN `4 <= CARD {v:real^3->bool | v face_of p /\ aff_dim v = &0}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIZE_ZERO_DIMENSIONAL_FACES; POLYTOPE_IMP_POLYHEDRON] THEN
    MP_TAC(ISPEC `p:real^3->bool` POLYTOPE_VERTEX_LOWER_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `4 <= CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2}`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `p:real^3->bool` POLYTOPE_FACET_LOWER_BOUND) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE; facet_of] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV THEN GEN_TAC THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[INT_ARITH `~(&2:int = -- &1)`; AFF_DIM_EMPTY];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `v + f = e + 2 ==> 4 <= v /\ 4 <= f ==> 6 <= e`)) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC
   `CARD {e:real^3->bool | e face_of p /\ aff_dim e = &1} = 0` THEN
  ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  SUBGOAL_THEN `3 <= m` ASSUME_TAC THENL
   [ASM_CASES_TAC `{f:real^3->bool | f face_of p /\ aff_dim f = &2} = {}` THENL
     [UNDISCH_TAC
       `4 <= CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2}` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` MP_TAC) THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
     FIRST_X_ASSUM(SUBST1_TAC o SYM o C MATCH_MP th)) THEN
    MP_TAC(ISPEC `f:real^3->bool` POLYTOPE_FACET_LOWER_BOUND) THEN
    ASM_REWRITE_TAC[facet_of] THEN CONV_TAC INT_REDUCE_CONV THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE]; ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONV_TAC INT_REDUCE_CONV THEN X_GEN_TAC `e:real^3->bool` THEN
    EQ_TAC THEN ASM_CASES_TAC `e:real^3->bool = {}` THEN
    ASM_SIMP_TAC[AFF_DIM_EMPTY] THEN CONV_TAC INT_REDUCE_CONV THENL
     [ASM_MESON_TAC[FACE_OF_TRANS; FACE_OF_IMP_SUBSET];
      ASM_MESON_TAC[FACE_OF_FACE]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `3 <= m ==> ~(m = 0)`)) THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_THEN `n = 0` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `0 * x = 2 * e ==> e = 0`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (NUM_RING
    `v + f = e + 2 ==> !m n. m * n * v + n * m * f = m * n * (e + 2)`)) THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `m * 2 * e + n * 2 * e = m * n * (e + 2) <=>
                          e * 2 * (m + n) = m * n * (e + 2)`] THEN
  ABBREV_TAC `E = CARD {e:real^3->bool | e face_of p /\ aff_dim e = &1}` THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ARITH_RULE
     `E * 2 * (n + 1) = n * (E + 2) <=> E * (n + 2) = 2 * n`] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
    MATCH_MP_TAC(ARITH_RULE `n:num < m ==> ~(m = n)`) THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 * (m + 2)` THEN
    CONJ_TAC THENL [ARITH_TAC; MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 2` THENL
   [ASM_REWRITE_TAC[ARITH_RULE `E * 2 * (n + 2) = n * 2 * (E + 2) <=>
                                E = n`] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (NUM_RING
     `E * c = 2 * E ==> E = 0 \/ c = 2`)) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `3 <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `m * n < 2 * (m + n)` THENL
   [DISCH_TAC;
    DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    SUBGOAL_THEN `E * 2 * (m + n) <= E * m * n` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `m * n * (E + 2) <= E * m * n <=>
                                  2 * m * n = 0`] THEN
      MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN
      REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC]] THEN
  SUBGOAL_THEN `&m - &2:real < &4 /\ &n - &2 < &4` MP_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `&n - &2`;
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&m - &2`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_OF_NUM_LT;
                 ARITH_RULE `2 < n <=> 3 <= n`] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&4` THEN
    REWRITE_TAC[REAL_ARITH `(m - &2) * (n - &2) < &4 <=>
                            m * n < &2 * (m + n)`] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB; REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_SUB_RADD; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
  REWRITE_TAC[ARITH_RULE `m < 4 + 2 <=> m <= 5`] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `3 <= m ==> (m <= 5 <=> m = 3 \/ m = 4 \/ m = 5)`] THEN
  STRIP_TAC THEN UNDISCH_TAC `E * 2 * (m + n) = m * n * (E + 2)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC);;
```

### Informal statement
For any subset `p` of three-dimensional real space, if `p` is a polytope, the affine dimension of `p` is 3, and for every face `f` of `p` such that the affine dimension of `f` is 2, the cardinality of the set of faces `e` of `p` such that the affine dimension of `e` is 1 and `e` is a subset of `f` is `m`, and for every face `v` of `p` such that the affine dimension of `v` is 0, the cardinality of the set of faces `e` of `p` such that the affine dimension of `e` is 1 and `v` is a subset of `e` is `n`, then one of the following holds: `m` is 3 and `n` is 3, or `m` is 4 and `n` is 3, or `m` is 3 and `n` is 4, or `m` is 5 and `n` is 3, or `m` is 3 and `n` is 5.

### Informal sketch
The proof proceeds by:
- Starting with the assumption that `p` is a polytope in 3D space.
- Applying `EULER_RELATION` which states that `V - E + F = 2`, where `V` is the number of vertices (0-dimensional faces), `E` is the number of edges (1-dimensional faces), and `F` is the number of facets (2-dimensional faces).
- Using lemmas to rewrite `V` as cardinality of the set of zero dimensional faces, `E` as cardinality of set of one dimensional faces, and `F` as cardinality of set of two dimensional faces.
- A subgoal is introduced:
`m * CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1} /\
    n * CARD {v | v face_of p /\ aff_dim v = &0} =
    2 * CARD {e | e face_of p /\ aff_dim e = &1}`.
- Using `MULTIPLE_COUNTING_LEMMA` which is used to express the number of edges in terms of faces and vertices, i.e., the number of face-edge incidences is the number of edges times 2 and this is equal to the sum over all faces of the number of edges in a face. The same is done for vertex-edge incidences based on the number of edges meeting at each vertex. Specifically, each edge is shared by two faces, and each edge connects two vertices.
- Simplifying using lemmas about finiteness of faces (`FINITE_POLYTOPE_FACES`, `FINITE_RESTRICT`), subset inclusion (`IN_ELIM_THM`), and associativity of conjunction (`GSYM CONJ_ASSOC`).
- Proving that each edge is the intersection of exactly two faces (`POLYHEDRON_RIDGE_TWO_FACETS`), combined with `POLYTOPE_IMP_POLYHEDRON`. Also showing that each edge can be represented as a segment using `COMPACT_CONVEX_COLLINEAR_SEGMENT`.
- Simplifying to show the relation `v + f = e + 2`, where `v` is the number of vertices, `e` is the number of edges, and `f` is the number of faces.
- Establishing lower bounds for the number of faces and vertices using `POLYTOPE_VERTEX_LOWER_BOUND` and `POLYTOPE_FACET_LOWER_BOUND` respectively. This gives `4 <= v` and `4 <= f`.
- Then proving that `4 <= CARD {v:real^3->bool | v face_of p /\ aff_dim v = &0}` and `4 <= CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2}`.
- Using arithmetic reasoning on `v + f = e + 2` and the bounds `4 <= v` and `4 <= f` which gives `6 <= e`.
- Then simplifying the relation `m * CARD {f:real^3->bool | f face_of p /\ aff_dim f = &2} = 2 * CARD {e | e face_of p /\ aff_dim e = &1} /\ n * CARD {v | v face_of p /\ aff_dim v = &0} = 2 * CARD {e | e face_of p /\ aff_dim e = &1}` to eventually deduce one of the platonic solids cases.
- Proof manages cases where `n = 1` and `n = 2`.

### Mathematical insight
This theorem classifies the possible combinations of number of edges per face (`m`) and number of edges per vertex (`n`) for Platonic solids. It leverages Euler's formula and combinatorial arguments to constrain the possible values of `m` and `n`, resulting in the five known Platonic solids.

### Dependencies
- `EULER_RELATION`
- `MULTIPLE_COUNTING_LEMMA`
- `FINITE_POLYTOPE_FACES`
- `FINITE_RESTRICT`
- `IN_ELIM_THM`
- `CONJ_ASSOC`
- `POLYHEDRON_RIDGE_TWO_FACETS`
- `POLYTOPE_IMP_POLYHEDRON`
- `COMPACT_CONVEX_COLLINEAR_SEGMENT`
- `FACE_OF_IMP_COMPACT`
- `AFF_DIM`
- `AFFINE_INDEPENDENT_IMP_FINITE`
- `HULL_SUBSET`
- `FACE_OF_IMP_CONVEX`
- `EXTREME_POINT_OF_SEGMENT`
- `FACE_OF_SING`
- `FACE_OF_TRANS`
- `FACE_OF_IMP_SUBSET`
- `FACE_OF_FACE`
- `SIZE_ZERO_DIMENSIONAL_FACES`
- `POLYTOPE_IMP_POLYHEDRON`
- `POLYTOPE_VERTEX_LOWER_BOUND`
- `POLYTOPE_FACET_LOWER_BOUND`
- `facet_of`

### Porting notes (optional)
- The theorem involves reasoning about sets, cardinalities, affine dimensions, and polytopes in 3D real space. Ensure that the target proof assistant has adequate libraries or support for these concepts.
- The proof uses a combination of algebraic manipulation, combinatorial arguments, and case splitting. Recreating this proof in another proof assistant might require a similar strategy.
- The use of `ASM_CASES_TAC` to split the proof into cases may need to be adapted depending on the case-splitting capabilities of the target proof assistant.
- The dependency on `EULER_RELATION` will need to be addressed. Some proof assistants may already have this formalized.


---

## PLATONIC_SOLIDS

### Name of formal statement
PLATONIC_SOLIDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PLATONIC_SOLIDS = prove
 (`!m n.
   (?p:real^3->bool.
     polytope p /\ aff_dim p = &3 /\
     (!f. f face_of p /\ aff_dim(f) = &2
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ e SUBSET f} = m) /\
     (!v. v face_of p /\ aff_dim(v) = &0
          ==> CARD {e | e face_of p /\ aff_dim(e) = &1 /\ v SUBSET e} = n)) <=>
     m = 3 /\ n = 3 \/       // Tetrahedron
     m = 4 /\ n = 3 \/       // Cube
     m = 3 /\ n = 4 \/       // Octahedron
     m = 5 /\ n = 3 \/       // Dodecahedron
     m = 3 /\ n = 5          // Icosahedron`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; PLATONIC_SOLIDS_LIMITS] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `std_tetrahedron` THEN
    ASM_REWRITE_TAC[TETRAHEDRON_EDGES_PER_VERTEX; TETRAHEDRON_EDGES_PER_FACE;
                    STD_TETRAHEDRON_FULLDIM] THEN
    REWRITE_TAC[std_tetrahedron] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_cube` THEN
    ASM_REWRITE_TAC[CUBE_EDGES_PER_VERTEX; CUBE_EDGES_PER_FACE;
                    STD_CUBE_FULLDIM] THEN
    REWRITE_TAC[std_cube] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_octahedron` THEN
    ASM_REWRITE_TAC[OCTAHEDRON_EDGES_PER_VERTEX; OCTAHEDRON_EDGES_PER_FACE;
                    STD_OCTAHEDRON_FULLDIM] THEN
    REWRITE_TAC[std_octahedron] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_dodecahedron` THEN
    ASM_REWRITE_TAC[DODECAHEDRON_EDGES_PER_VERTEX; DODECAHEDRON_EDGES_PER_FACE;
                    STD_DODECAHEDRON_FULLDIM] THEN
    REWRITE_TAC[STD_DODECAHEDRON] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    EXISTS_TAC `std_icosahedron` THEN
    ASM_REWRITE_TAC[ICOSAHEDRON_EDGES_PER_VERTEX; ICOSAHEDRON_EDGES_PER_FACE;
                    STD_ICOSAHEDRON_FULLDIM] THEN
    REWRITE_TAC[STD_ICOSAHEDRON] THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]]);;
```
### Informal statement
For all real numbers `m` and `n`, the following holds: There exists a set `p` of points in 3-dimensional real space such that `p` is a polytope, the affine dimension of `p` is equal to 3, and for all `f`, if `f` is a face of `p` and the affine dimension of `f` is 2, then the cardinality of the set of `e` such that `e` is a face of `p`, the affine dimension of `e` is 1, and `e` is a subset of `f` is equal to `m`, and for all `v`, if `v` is a face of `p` and the affine dimension of `v` is 0, then the cardinality of the set of `e` such that `e` is a face of `p`, the affine dimension of `e` is 1, and `v` is a subset of `e` is equal to `n`, if and only if `m` equals 3 and `n` equals 3, or `m` equals 4 and `n` equals 3, or `m` equals 3 and `n` equals 4, or `m` equals 5 and `n` equals 3, or `m` equals 3 and `n` equals 5.

### Informal sketch
The theorem states necessary and sufficient conditions on `m` and `n` for the existence of a 3D polytope where `m` is the number of edges per face and `n` is the number of edges meeting at each vertex. The theorem proves this by showing that such a polytope exists if and only if it is one of the five Platonic solids: tetrahedron, cube, octahedron, dodecahedron, or icosahedron.

The proof proceeds by:
- proving the implication in both directions (if and only if)
- The implication from right to left is proven by exhibiting each of the five platonic solids with the specified properties.
  - For each Platonic solid (tetrahedron, cube, octahedron, dodecahedron, icosahedron), the proof explicitly constructs a standard instance (`std_tetrahedron`, `std_cube`, `std_octahedron`, `std_dodecahedron`, `std_icosahedron`).
  - For each standard instance, it is shown that it is a polytope using `POLYTOPE_CONVEX_HULL` and that it satisfies the edge per face/vertex constraints. This uses theorems like `TETRAHEDRON_EDGES_PER_VERTEX`, `TETRAHEDRON_EDGES_PER_FACE`, `CUBE_EDGES_PER_VERTEX`, `CUBE_EDGES_PER_FACE`, etc.
  - The full dimensionality (`aff_dim = &3`) of the instance is also verified using theorems like `STD_TETRAHEDRON_FULLDIM`, `STD_CUBE_FULLDIM`.

### Mathematical insight
This theorem provides a formal statement of the classification of Platonic solids in terms of the number of edges per face and edges per vertex. The Platonic solids are fundamental geometric objects with high symmetry, and this theorem offers a precise algebraic characterization based on combinatorial properties.

### Dependencies
Geometrical Definitions and Theorems:
- `polytope`
- `aff_dim`
- `face_of`
- `SUBSET`
Theorems for specific Platonic Solids:
- `TETRAHEDRON_EDGES_PER_VERTEX`
- `TETRAHEDRON_EDGES_PER_FACE`
- `STD_TETRAHEDRON_FULLDIM`
- `CUBE_EDGES_PER_VERTEX`
- `CUBE_EDGES_PER_FACE`
- `STD_CUBE_FULLDIM`
- `OCTAHEDRON_EDGES_PER_VERTEX`
- `OCTAHEDRON_EDGES_PER_FACE`
- `STD_OCTAHEDRON_FULLDIM`
- `DODECAHEDRON_EDGES_PER_VERTEX`
- `DODECAHEDRON_EDGES_PER_FACE`
- `STD_DODECAHEDRON_FULLDIM`
- `ICOSAHEDRON_EDGES_PER_VERTEX`
- `ICOSAHEDRON_EDGES_PER_FACE`
- `STD_ICOSAHEDRON_FULLDIM`
- `POLYTOPE_CONVEX_HULL`
Set and Cardinality related theorems
- `FINITE_INSERT`
- `FINITE_EMPTY`

### Porting notes (optional)
- The theorem relies on the definitions of polytopes, faces, and affine dimension, which may need to be adapted based on the target proof assistant's geometric library.
- In proof assistants such as Coq or Lean, the definitions and theorems for specific Platonic solids might need to be constructed from scratch or imported from a suitable geometry library. Libraries like MathComp might be useful.
- The explicit construction of standard instances (`std_tetrahedron`, etc.) might involve defining the vertices explicitly as vectors.


---

## congruent

### Name of formal statement
congruent

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let congruent = new_definition
 `(s:real^N->bool) congruent (t:real^N->bool) <=>
        ?c f. orthogonal_transformation f /\ t = IMAGE (\x. c + f x) s`;;
```

### Informal statement
For any sets `s` and `t` of points in `N`-dimensional real space, `s` is congruent to `t` if and only if there exists a vector `c` in `N`-dimensional real space and a function `f` such that `f` is an orthogonal transformation and `t` is the image of `s` under the transformation `x` maps to `c + f x`.

### Informal sketch
The definition of `congruent` states that two sets are congruent if one can be obtained from the other by an orthogonal transformation (rotation and/or reflection) followed by a translation.

- The existential quantifier introduces a translation vector `c` and an orthogonal transformation `f`.
- The predicate `orthogonal_transformation f` formalizes the condition that `f` is an orthogonal transformation.
- The equation `t = IMAGE (\x. c + f x) s` formalizes that `t` is the image of `s` after applying the transformation `x` is mapped to `c + f x` to each element `x` of `s`. `IMAGE` represents the image of the set `s` under the mapping `\x. c + f x`.

### Mathematical insight
This definition captures the intuitive notion of congruence in Euclidean space: two sets are congruent if they are the same up to rigid motion (rotation, reflection, and translation). This definition provides a precise and useful way to reason about congruence formally.

### Dependencies
- `orthogonal_transformation`
- `IMAGE`

### Porting notes (optional)
- The definition relies on the presence of orthogonal transformation and image operation.
- Ensure that when porting that there exist corresponding definitions of real vectors, addition between vectors, and orthogonal transformation in the target proof assistant.
- The handling of the variable `N`, which denotes dimension, needs care. In HOL Light, it is a type variable, but other systems might require it to be explicitly quantified, and/or require constraints that it is positive.


---

## CONGRUENT_SIMPLE

### Name of formal statement
CONGRUENT_SIMPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONGRUENT_SIMPLE = prove
 (`(?A:real^3^3. orthogonal_matrix A /\ IMAGE (\x:real^3. A ** x) s = t)
   ==> (convex hull s) congruent (convex hull t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
  SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  REWRITE_TAC[congruent] THEN EXISTS_TAC `vec 0:real^3` THEN
  EXISTS_TAC `\x:real^3. (A:real^3^3) ** x` THEN
  REWRITE_TAC[VECTOR_ADD_LID; ORTHOGONAL_TRANSFORMATION_MATRIX] THEN
  ASM_SIMP_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR]);;
```
### Informal statement
For all real matrices `A` of dimension 3x3, if `A` is an orthogonal matrix and the image of the set `s` under the linear transformation induced by `A` is equal to the set `t`, then the convex hull of `s` is congruent to the convex hull of `t`.

### Informal sketch
The proof demonstrates that if a set `t` is the image of a set `s` under an orthogonal transformation (given by the matrix `A`), then the convex hulls of `s` and `t` are congruent.
- The proof starts by assuming the hypothesis: `A` is an orthogonal matrix and the image of `s` under the transformation `A` is equal to `t`.
- It then uses the theorem `CONVEX_HULL_LINEAR_IMAGE` and the linearity of matrix-vector multiplication (`MATRIX_VECTOR_MUL_LINEAR`) to show that the image of the convex hull of `s` under the transformation `A` is the convex hull of the image of `s`, namely `t`.
- Next uses the definition of `congruent`.
- The theorem `ORTHOGONAL_TRANSFORMATION_MATRIX` and properties of linear transformations are used to show that the required conditions for congruence are met (namely, the existence of a translation vector `vec 0` and linear transformation `\x. A ** x`). We verify that matrix multiplication is linear.
- The proof concludes by applying the definition of congruence, demonstrating that the convex hull of `s` is congruent to the convex hull of `t`.

### Mathematical insight
This theorem establishes a fundamental relationship between convex hulls and orthogonal transformations. It shows that orthogonal transformations (rotations, reflections, and their combinations) preserve the congruence of convex hulls. This is important because convex hulls are fundamental geometric objects, and orthogonal transformations are distance-preserving transformations. Therefore, this theorem formalizes the intuition that rotating or reflecting a convex object does not change its shape in terms of congruence.

### Dependencies
- `CONVEX_HULL_LINEAR_IMAGE`
- `MATRIX_VECTOR_MUL_LINEAR`
- `congruent`
- `VECTOR_ADD_LID`
- `ORTHOGONAL_TRANSFORMATION_MATRIX`
- `MATRIX_OF_MATRIX_VECTOR_MUL`


---

## CONGRUENT_SEGMENTS

### Name of formal statement
CONGRUENT_SEGMENTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONGRUENT_SEGMENTS = prove
 (`!a b c d:real^N.
        dist(a,b) = dist(c,d)
        ==> segment[a,b] congruent segment[c,d]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b - a:real^N`; `d - c:real^N`]
    ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
  ANTS_TAC THENL [POP_ASSUM MP_TAC THEN NORM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[congruent] THEN
  EXISTS_TAC `c - (f:real^N->real^N) a` THEN
  EXISTS_TAC `f:real^N->real^N` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  SUBGOAL_THEN
   `(\x. (c - f a) + (f:real^N->real^N) x) = (\x. (c - f a) + x) o f`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CONVEX_HULL_LINEAR_IMAGE; SEGMENT_CONVEX_HULL; IMAGE_o;
               GSYM CONVEX_HULL_TRANSLATION] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [VECTOR_ARITH_TAC; AP_THM_TAC THEN AP_TERM_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `d:real^N = c - a + b <=> b - a = d - c`] THEN
  ASM_MESON_TAC[LINEAR_SUB]);;
```
### Informal statement
For all vectors `a`, `b`, `c`, and `d` in `real^N`, if the distance between `a` and `b` is equal to the distance between `c` and `d`, then the segment with endpoints `a` and `b` is congruent to the segment with endpoints `c` and `d`.

### Informal sketch
The proof proceeds as follows:
- Assume `dist(a, b) = dist(c, d)`.
- Show that there exists an orthogonal transformation `f` such that `dist(a, b) = |b - a| = |d - c| = dist(c, d)`.
- Show that there exists a function `f` such that the segment from `a` to `b` is congruent to the segment from `c` to `d`. This involves finding a suitable affine transformation.
- Choose a function `f` such that it meets the definition of `congruent`.
- The affine transformation needed is `(\x. (c - f a) + (f:real^N->real^N) x)`, which is equivalent to `(\x. (c - f a) + x) o f`.
- Show that the image of `segment[a, b]` under the affine transformation `(\x. (c - f a) + (f:real^N->real^N) x)` is equal to `segment[c, d]`. This involves using properties of convex hulls and linear images.
- Use the property that the image of a convex hull under a linear transformation equals the convex hull of the image. Also, the image of a convex hull under a translation equals the translation of the convex hull.
- Use vector arithmetic and the fact that `f` is linear to complete the proof.

### Mathematical insight
The theorem `CONGRUENT_SEGMENTS` provides a formal statement about the congruence of two line segments in `real^N`. The congruence of line segments is defined by existing orthogonal transformations. The theorem's purpose is to establish that two segments are congruent if and only if their lengths are equal. This is a fundamental concept in Euclidean geometry, formalizing the notion that segments of the same length are geometrically equivalent.

### Dependencies
- Theorems:
  - `ORTHOGONAL_TRANSFORMATION_EXISTS`
  - `ORTHOGONAL_TRANSFORMATION_LINEAR`.
  - `FUN_EQ_THM`
  - `o_THM`
- Definitions:
  - `congruent`
- Other:
  - `CONVEX_HULL_LINEAR_IMAGE`
  - `SEGMENT_CONVEX_HULL`
  - `IMAGE_o`
  - `CONVEX_HULL_TRANSLATION`
  - `IMAGE_CLAUSES`
  - `LINEAR_SUB`

### Porting notes (optional)
- The definition of `congruent` is crucial, and its representation should be carefully considered in the target proof assistant.
- The handling of orthogonal transformations, their properties, and their existence may require specific libraries or constructions in the target system.
- The properties of convex hulls and linear transformations are extensively used. Ensure that the corresponding libraries (or equivalent constructions) are available.


---

## compute_dist

### Name of formal statement
compute_dist

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let compute_dist =
  let mk_sub = mk_binop `(-):real^3->real^3->real^3`
  and dot_tm = `(dot):real^3->real^3->real` in
  fun v1 v2 -> let vth = VECTOR3_SUB_CONV(mk_sub v1 v2) in
               let dth = CONV_RULE(RAND_CONV VECTOR3_DOT_CONV)
                          (MK_COMB(AP_TERM dot_tm vth,vth)) in
               rand(concl dth);;
```

### Informal statement
The function `compute_dist` is defined as follows: Given two vectors `v1` and `v2` of type `real^3`, it computes the square of the Euclidean distance between them. First, it calculates the vector `vth` which is the result of subtracting `v2` from `v1`. Then, it computes the dot product of `vth` with itself, and returns the result.

### Informal sketch
The definition calculates the squared Euclidean distance between two 3D real vectors.
- Define `mk_sub` as a binary operation representing vector subtraction.
- Define `dot_tm` as a term representing the dot product operation.
- Given input vectors `v1` and `v2`:
  - Calculate `vth` as the vector difference `v1 - v2` using `VECTOR3_SUB_CONV` to perform the subtraction.
  - Compute the dot product of `vth` with itself using `VECTOR3_DOT_CONV`, resulting in `vth dot vth`. `RAND_CONV VECTOR3_DOT_CONV` applies `VECTOR3_DOT_CONV` to randomly instantiated variables.
  - Extract the conclusion of the resulting theorem using `concl dth` and then randomly instantiate all variables using `rand`.

### Mathematical insight
The function computes the square of the Euclidean distance between two points in 3D space. The Euclidean distance is the magnitude of the vector connecting the two points. Squaring this magnitude avoids the need for a square root operation and is often useful in optimization problems where the true distance is less important than a monotonic measure of separation.

### Dependencies
- `VECTOR3_SUB_CONV`
- `VECTOR3_DOT_CONV`
- `dot`

### Porting notes (optional)
- This definition requires a real vector library and theorems about vector subtraction and dot products.
- The calls to `VECTOR3_SUB_CONV` and `VECTOR3_DOT_CONV` suggest that these are conversionals, which may need to be implemented explicitly in other systems by providing appropriate rewrite rules or simplification tactics.
- Specifically, the `VECTOR3_SUB_CONV` likely unfolds the vector subtraction, and the `VECTOR3_DOT_CONV` probably expands the dot product in terms of component-wise multiplication and addition.


---

## le_rat5

### Name of formal statement
le_rat5

### Type of the formal statement
theorem

### Formal Content
```ocaml
let le_rat5 =
  let mk_le = mk_binop `(<=):real->real->bool` and t_tm = `T` in
  fun r1 r2 -> rand(concl(REAL_RAT5_LE_CONV(mk_le r1 r2))) = t_tm;;
```

### Informal statement
For any real numbers `r1` and `r2`, the randomizing function `rand` applied to the conclusion of the theorem `REAL_RAT5_LE_CONV` applied to the inequality `r1 <= r2` yields the boolean value `T` (true).

### Informal sketch
- The theorem states that applying the theorem `REAL_RAT5_LE_CONV` to the term `r1 <= r2`, and then taking the conclusion of the resulting theorem, and finally randomizing the resulting boolean by `rand`, yields the boolean value `T` (true).
- `REAL_RAT5_LE_CONV` is a conversion that simplifies inequalities between real numbers.
- The application of `rand` likely normalizes the boolean term to `T`.

### Mathematical insight
This theorem essentially states that the conversion `REAL_RAT5_LE_CONV` fully decides the inequality `r1 <= r2`, and the result can be normalized to either true or false when the conversion is applicable. `REAL_RAT5_LE_CONV` likely reduces some expressions involving real numbers and shows how to reduce inequalities on real numbers to true. `rand` is likely a conversion that normalizes boolean values after the application of appropriate conversions.

### Dependencies
- Definitions:
   - `mk_binop`
- Theorems:
   - `REAL_RAT5_LE_CONV`


---

## three_adjacent_points

### Name of formal statement
three_adjacent_points

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let three_adjacent_points s =
  match s with
  | x::t -> let (y,_)::(z,_)::_ =
              sort (fun (_,r1) (_,r2) -> le_rat5 r1 r2)
                   (map (fun y -> y,compute_dist x y) t) in
            x,y,z
  | _ -> failwith "three_adjacent_points: no points";;
```

### Informal statement
Given a set of points `s`, if `s` is non-empty, let `x` be an arbitrary element of `s` and `t` be the remainder of `s` after removing `x`. Then, consider the list of pairs formed by mapping each point `y` in `t` to the pair `(y, compute_dist x y)`, where `compute_dist x y` is the distance between `x` and `y`. Sort this list of pairs by the distances, using `le_rat5` to compare distances. Let `y` and `z` be the first and second elements of this sorted list, respectively. Return the triple `(x, y, z)`. If the set `s` is empty, then `failwith` with the string `"three_adjacent_points: no points"`.

### Informal sketch
- The function `three_adjacent_points` takes a set of points `s` as input.
- If `s` is empty, the function fails.
- Otherwise, an arbitrary point `x` is selected from `s`.
- The function then computes the distance between `x` and every other point `y` in `s`, creating a list of pairs `(y, distance(x, y))`.
- This list is sorted by distance using `le_rat5`.
  - Note: `le_rat5` is likely a comparator for rational numbers, used here to sort distances.
- The function then extracts the two points `y` and `z` that are closest to `x` (according to the sorted list.)
- Finally, it returns the tuple `(x, y, z)`.

### Mathematical insight
The function `three_adjacent_points` attempts to find three points that are "adjacent" in some sense. It chooses one point arbitrarily, and then finds the two closest points to that point. The concept of choosing the first two elements from the sorted list implies defining proximity between points based on the computed distance. The sorting ensures that points are ordered based on their distance from the initially chosen point `x`.

### Dependencies
- `compute_dist`: A function that computes the distance between two points.
- `le_rat5`: A function that compares two rational numbers, presumably for comparing distances.
- `sort`: A sorting function.
- `map`: A mapping function.


---

## mk_33matrix

### Name of formal statement
mk_33matrix

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let mk_33matrix =
  let a11_tm = `a11:real`
  and a12_tm = `a12:real`
  and a13_tm = `a13:real`
  and a21_tm = `a21:real`
  and a22_tm = `a22:real`
  and a23_tm = `a23:real`
  and a31_tm = `a31:real`
  and a32_tm = `a32:real`
  and a33_tm = `a33:real`
  and pat_tm =
   `vector[vector[a11; a12; a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33]]:real^3^3` in
  fun [a11;a12;a13;a21;a22;a23;a31;a32;a33] ->
    vsubst[a11,a11_tm;
           a12,a12_tm;
           a13,a13_tm;
           a21,a21_tm;
           a22,a22_tm;
           a23,a23_tm;
           a31,a31_tm;
           a32,a32_tm;
           a33,a33_tm] pat_tm;;
```

### Informal statement
The function `mk_33matrix` takes nine real numbers `a11`, `a12`, `a13`, `a21`, `a22`, `a23`, `a31`, `a32`, and `a33` as input, and returns a 3x3 matrix of real numbers. This matrix is constructed by substituting the input values for the corresponding variables in the term `vector[vector[a11; a12; a13]; vector[a21; a22; a23]; vector[a31; a32; a33]]`.

### Informal sketch
The function `mk_33matrix` is defined by:
- First, define terms `a11_tm`, `a12_tm`, `a13_tm`, `a21_tm`, `a22_tm`, `a23_tm`, `a31_tm`, `a32_tm`, and `a33_tm` to represent the variables *a11*, *a12*, *a13*, *a21*, *a22*, *a23*, *a31*, *a32*, and *a33* respectively.
- Then construct a term `pat_tm` describing a 3x3 matrix, where the entries are `a11`, `a12`, `a13`, `a21`, `a22`, `a23`, `a31`, `a32`, and `a33`. The type of `pat_tm` is `real^3^3`.
- Finally, create a function that takes nine real numbers as input and substitutes them into the term `pat_tm` using `vsubst`.

### Mathematical insight
This definition provides a convenient way to construct a 3x3 matrix given its individual real-valued components. The use of `vsubst` ensures that the resulting term represents the matrix with the given values.

### Dependencies
None

### Porting notes (optional)
The `vsubst` function and the representation of vectors and matrices might need to be adapted depending on the target proof assistant. Some systems might have built-in matrix types with corresponding constructor functions, so `vsubst` may not be necessary.


---

## MATRIX_VECTOR_MUL_3

### Name of formal statement
MATRIX_VECTOR_MUL_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIX_VECTOR_MUL_3 = prove
 (`(vector[vector[a11;a12;a13];
           vector[a21; a22; a23];
           vector[a31; a32; a33]]:real^3^3) **
   (vector[x1;x2;x3]:real^3) =
   vector[a11 * x1 + a12 * x2 + a13 * x3;
          a21 * x1 + a22 * x2 + a23 * x3;
          a31 * x1 + a32 * x2 + a33 * x3]`,
  SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; SUM_3; VECTOR_3]);;
```
### Informal statement
For any 3x3 matrix `A` of real numbers, represented as a vector of vectors `vector[vector[a11;a12;a13]; vector[a21; a22; a23]; vector[a31; a32; a33]]`, and any 3-dimensional vector `x` of real numbers, represented as `vector[x1;x2;x3]`, the matrix-vector product `A ** x` is equal to the vector `vector[a11 * x1 + a12 * x2 + a13 * x3; a21 * x1 + a22 * x2 + a23 * x3; a31 * x1 + a32 * x2 + a33 * x3]`.

### Informal sketch
The proof proceeds by:
- First, simplifying using `CART_EQ`, `matrix_vector_mul` (presumably the definition of matrix-vector multiplication), and `LAMBDA_BETA` reduction. This expands the matrix-vector multiplication into a summation over the rows and columns of the matrix and components of the vector.
- Second, rewriting using `DIMINDEX_3`, `FORALL_3`, `SUM_3`, and `VECTOR_3`. These lemmas likely provide expansions or simplifications related to finite sums, vector construction, and quantifications over the index set `{0, 1, 2}` representing the three dimensions. These rewrites evaluate the summation, thereby establishing the equality of the vectors.

### Mathematical insight
This theorem provides an explicit formula for the matrix-vector product in the specific case of a 3x3 matrix and a 3-dimensional vector. It is a fundamental result in linear algebra, showing how matrix-vector multiplication corresponds to a linear combination of the columns of the matrix, with the coefficients being the components of the vector.

### Dependencies
- Definitions:
  - `matrix_vector_mul`
- Theorems/Lemmas:
  - `CART_EQ`
  - `DIMINDEX_3`
  - `FORALL_3`
  - `SUM_3`
  - `VECTOR_3`


---

## MATRIX_LEMMA

### Name of formal statement
MATRIX_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIX_LEMMA = prove
 (`!A:real^3^3.
   A ** x1 = x2 /\
   A ** y1 = y2 /\
   A ** z1 = z2 <=>
   (vector [x1; y1; z1]:real^3^3) ** (row 1 A:real^3) =
   vector [x2$1; y2$1; z2$1] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 2 A:real^3) =
   vector [x2$2; y2$2; z2$2] /\
   (vector [x1; y1; z1]:real^3^3) ** (row 3 A:real^3) =
   vector [x2$3; y2$3; z2$3]`,
  SIMP_TAC[CART_EQ; transp; matrix_vector_mul; row; VECTOR_3; LAMBDA_BETA] THEN
  REWRITE_TAC[FORALL_3; DIMINDEX_3; VECTOR_3; SUM_3] THEN REAL_ARITH_TAC);;
```
### Informal statement
For all 3x3 matrices A of real numbers, the following equivalence holds:
`A` multiplied by the vector `x1` equals `x2`, and `A` multiplied by the vector `y1` equals `y2`, and `A` multiplied by the vector `z1` equals `z2` if and only if the matrix formed by the column vectors `x1`, `y1`, and `z1` multiplied by the first row of `A` equals the vector formed from the first components of `x2`, `y2`, and `z2`, and the matrix formed by the column vectors `x1`, `y1`, and `z1` multiplied by the second row of `A` equals the vector formed from the second components of `x2`, `y2`, and `z2`, and the matrix formed by the column vectors `x1`, `y1`, and `z1` multiplied by the third row of `A` equals the vector formed from the third components of `x2`, `y2`, and `z2`.
### Informal sketch
The proof proceeds as follows:
- The first stage uses simplification tactics (`SIMP_TAC`) along with `CART_EQ`, `transp`, `matrix_vector_mul`, `row`, `VECTOR_3`, and `LAMBDA_BETA` to expand the definitions of matrix-vector multiplication, the `row` operator, and vector equality.
- The second stage uses rewriting tactics (`REWRITE_TAC`) with `FORALL_3`, `DIMINDEX_3`, `VECTOR_3`, and `SUM_3` to further expand definitions related to vector operations and quantifiers over indices.
- The final call to `REAL_ARITH_TAC` uses real arithmetic decision procedures to complete the proof by establishing the equivalence of the expressions.
### Mathematical insight
The theorem relates matrix-vector multiplication to matrix multiplication of a matrix formed by column vectors and the rows of a matrix. It essentially decomposes the matrix-vector equations into sets of equations involving the columns `x1`, `y1`, `z1` seen as a matrix. This is useful for reasoning about linear independence and change of basis.

### Dependencies
- `CART_EQ`
- `transp`
- `matrix_vector_mul`
- `row`
- `VECTOR_3`
- `LAMBDA_BETA`
- `FORALL_3`
- `DIMINDEX_3`
- `SUM_3`


---

## MATRIX_BY_CRAMER_LEMMA

### Name of formal statement
MATRIX_BY_CRAMER_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIX_BY_CRAMER_LEMMA = prove
 (`!A:real^3^3.
        ~(det(vector[x1; y1; z1]:real^3^3) = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
             A = lambda m k. det((lambda i j.
                                  if j = k
                                  then (vector[x2$m; y2$m; z2$m]:real^3)$i
                                  else (vector[x1; y1; z1]:real^3^3)$i$j)
                                 :real^3^3) /
                             det(vector[x1;y1;z1]:real^3^3))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [MATRIX_LEMMA] THEN
  ASM_SIMP_TAC[CRAMER] THEN REWRITE_TAC[CART_EQ; row] THEN
  SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[DIMINDEX_3; FORALL_3]);;
```
### Informal statement
For any 3x3 real matrix `A`, the determinant of the matrix formed by the column vectors `x1`, `y1`, and `z1` (i.e., `vector[x1; y1; z1]`) is not equal to 0 if and only if the following holds: `A` multiplied by `x1` equals `x2`, `A` multiplied by `y1` equals `y2`, and `A` multiplied by `z1` equals `z2` if and only if `A` is equal to a lambda expression that maps `m` and `k` to the determinant of a matrix divided by the determinant of `vector[x1; y1; z1]`, where the inner matrix is constructed such that the k-th column is replaced by the vector `vector[x2$m; y2$m; z2$m]`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and implications.
- Applying the `MATRIX_LEMMA` which likely decomposes the matrix equation into scalar equations.
- Simplifying using `CRAMER`, suggesting application of Cramer's rule.
- Rewriting using `CART_EQ` and `row`, perhaps to manipulate vector/matrix representations.
- Simplifying using `LAMBDA_BETA`, to reduce the lambda expression.
- Rewriting using `DIMINDEX_3` and `FORALL_3` to expand or simplify equations related to the 3x3 matrix dimension.

### Mathematical insight
This theorem relates the solution of a system of linear equations `Ax = b` to Cramer's rule. More specifically, it provides a condition under which the matrix `A` can be explicitly constructed from the vectors `x1`, `y1`, `z1`, `x2`, `y2`, and `z2`, where `x2 = A**x1`, `y2 = A**y1`, `z2 = A**z1`. The condition states that the determinant of the matrix formed by `x1`, `y1`, and `z1` must be non-zero, which is the usual requirement for Cramer's rule to be applicable.

### Dependencies
- `MATRIX_LEMMA`
- `CRAMER`
- `CART_EQ`
- `row`
- `LAMBDA_BETA`
- `DIMINDEX_3`
- `FORALL_3`

### Porting notes (optional)
- The handling of matrix indexing and vector representation might differ across systems, so special attention should be given to the definitions of `vector` and `$`.
- The tactic `ASM_SIMP_TAC` indicates that the proof relies on automatic simplification with assumptions from the context, which suggests that recreating the proof may require careful management of assumptions.


---

## MATRIX_BY_CRAMER

### Name of formal statement
MATRIX_BY_CRAMER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MATRIX_BY_CRAMER = prove
 (`!A:real^3^3 x1 y1 z1 x2 y2 z2.
        let d = det(vector[x1; y1; z1]:real^3^3) in
        ~(d = &0)
        ==> (A ** x1 = x2 /\
             A ** y1 = y2 /\
             A ** z1 = z2 <=>
               A$1$1 =
               (x2$1 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$1 +
                x1$3 * y2$1 * z1$2 -
                x2$1 * y1$3 * z1$2 -
                x1$2 * y2$1 * z1$3 -
                x1$3 * y1$2 * z2$1) / d /\
               A$1$2 =
               (x1$1 * y2$1 * z1$3 +
                x2$1 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$1 -
                x1$1 * y1$3 * z2$1 -
                x2$1 * y1$1 * z1$3 -
                x1$3 * y2$1 * z1$1) / d /\
               A$1$3 =
               (x1$1 * y1$2 * z2$1 +
                x1$2 * y2$1 * z1$1 +
                x2$1 * y1$1 * z1$2 -
                x1$1 * y2$1 * z1$2 -
                x1$2 * y1$1 * z2$1 -
                x2$1 * y1$2 * z1$1) / d /\
               A$2$1 =
               (x2$2 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$2 +
                x1$3 * y2$2 * z1$2 -
                x2$2 * y1$3 * z1$2 -
                x1$2 * y2$2 * z1$3 -
                x1$3 * y1$2 * z2$2) / d /\
               A$2$2 =
               (x1$1 * y2$2 * z1$3 +
                x2$2 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$2 -
                x1$1 * y1$3 * z2$2 -
                x2$2 * y1$1 * z1$3 -
                x1$3 * y2$2 * z1$1) / d /\
               A$2$3 =
               (x1$1 * y1$2 * z2$2 +
                x1$2 * y2$2 * z1$1 +
                x2$2 * y1$1 * z1$2 -
                x1$1 * y2$2 * z1$2 -
                x1$2 * y1$1 * z2$2 -
                x2$2 * y1$2 * z1$1) / d /\
               A$3$1 =
               (x2$3 * y1$2 * z1$3 +
                x1$2 * y1$3 * z2$3 +
                x1$3 * y2$3 * z1$2 -
                x2$3 * y1$3 * z1$2 -
                x1$2 * y2$3 * z1$3 -
                x1$3 * y1$2 * z2$3) / d /\
               A$3$2 =
               (x1$1 * y2$3 * z1$3 +
                x2$3 * y1$3 * z1$1 +
                x1$3 * y1$1 * z2$3 -
                x1$1 * y1$3 * z2$3 -
                x2$3 * y1$1 * z1$3 -
                x1$3 * y2$3 * z1$1) / d /\
               A$3$3 =
               (x1$1 * y1$2 * z2$3 +
                x1$2 * y2$3 * z1$1 +
                x2$3 * y1$1 * z1$2 -
                x1$1 * y2$3 * z1$2 -
                x1$2 * y1$1 * z2$3 -
                x2$3 * y1$2 * z1$1) / d)`,
  REPEAT GEN_TAC THEN CONV_TAC let_CONV THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MATRIX_BY_CRAMER_LEMMA] THEN
  REWRITE_TAC[DET_3; CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH; VECTOR_3] THEN
  REWRITE_TAC[FORALL_3; ARITH; VECTOR_3] THEN REWRITE_TAC[CONJ_ACI]);;
```
### Informal statement
For all real-valued 3x3 matrices `A` and all real-valued vectors `x1`, `y1`, `z1`, `x2`, `y2`, `z2`, if the determinant of the matrix formed by the vectors `x1`, `y1`, and `z1` is not equal to zero, then the equations `A` applied to `x1` equals `x2`, `A` applied to `y1` equals `y2`, and `A` applied to `z1` equals `z2` hold if and only if the components `A$1$1`, `A$1$2`, `A$1$3`, `A$2$1`, `A$2$2`, `A$2$3`, `A$3$1`, `A$3$2`, and `A$3$3` of the matrix `A` are given by the explicit formulas involving the components of `x1`, `y1`, `z1`, `x2`, `y2`, `z2` and the determinant `d`, as expressed in the conclusion.

### Informal sketch
The proof shows the matrix `A` can be defined in terms of its action on three independent vectors `x1`, `y1`, `z1`.
- The assumption that the determinant is nonzero ensures that the vectors `x1`, `y1`, `z1` are linearly independent and thus form a basis.
- The theorem then uses `MATRIX_BY_CRAMER_LEMMA`, which expresses the matrix elements of `A` in terms of the inverse matrix and applies simplification rules. This lemma effectively captures Cramer's rule.
- The determinant of the 3x3 matrix uses `DET_3`.
- The proof then simplifies the vector and matrix component accesses using `CART_EQ`, `LAMBDA_BETA`, `DIMINDEX_3`, along with field and ring arithmetic properties (`ARITH`).
- The quantifiers are eliminated using `FORALL_3`.
- Finally, `CONJ_ACI` rewrites the resulting conjunction.

### Mathematical insight
This theorem explicitly expresses the matrix `A` in terms of its action on three linearly independent vectors.  It shows how to compute the components of `A` given only the inputs `x1`, `y1`, `z1`, and the outputs `x2`, `y2`, `z2`. The result is an explicit formula for the matrix elements using Cramer's rule. This is useful in various contexts, for example, solving linear systems or defining linear transformations.

### Dependencies
- `MATRIX_BY_CRAMER_LEMMA`
- `DET_3`
- `CART_EQ`
- `LAMBDA_BETA`
- `DIMINDEX_3`
- `ARITH`
- `VECTOR_3`
- `FORALL_3`
- `CONJ_ACI`


---

## CONGRUENT_EDGES_TAC

### Name of formal statement
CONGRUENT_EDGES_TAC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONGRUENT_EDGES_TAC edges =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[IMP_IMP] THEN
  REWRITE_TAC[edges] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  MATCH_MP_TAC CONGRUENT_SEGMENTS THEN REWRITE_TAC[DIST_EQ] THEN
  REWRITE_TAC[dist; NORM_POW_2] THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_SUB_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV VECTOR3_DOT_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
  REWRITE_TAC[];;
```

### Informal statement
The tactic `CONGRUENT_EDGES_TAC` takes a list of rewrite theorems `edges` as input. It aims to prove that two edges are congruent by rewriting and simplifying the goal.

### Informal sketch
The tactic performs the following steps:

- Rewrite the goal using `IMP_CONJ` and `RIGHT_FORALL_IMP_THM` to break down implications and quantifiers.
- Rewrite the result using `IMP_IMP` to further simplify implications.
- Rewrite using the given list of theorems `edges` to apply relevant assumptions about the edges.
- Repeatedly apply `STRIP_TAC` to remove assumptions from the hypothesis and add them to the assumptions.
- Rewrite using `GSYM SEGMENT_CONVEX_HULL` and assumptions to express segments based on convex hulls of their endpoints.
- Match with the theorem `CONGRUENT_SEGMENTS` (applying it via `MATCH_MP_TAC`). This theorem likely states the conditions under which two segments are congruent, which is probably equivalent to equality of their lengths after some rewriting.
- Rewrite using the theorem `DIST_EQ`, which equates segment equality (congruence) with equality of distances between endpoints.
- Rewrite using `dist` and `NORM_POW_2` to expand the distance calculation, likely involving norms and squares.
- Perform depth-first conversion using `VECTOR3_SUB_CONV` to simplify vector subtractions.
- Perform depth-first conversion using `VECTOR3_DOT_CONV` to simplify vector dot products.
- Perform depth-first conversion using `REAL_RAT5_EQ_CONV` to simplify real number equalities.
- Final rewrite pass with no additional theorems to clean up any remaining terms.

### Mathematical insight
This tactic automates the proof that two edges (segments) are congruent. It relies on rewriting the congruence condition into an equality of distances, expanding distances into vector operations (subtraction, dot product), and then simplifying those operations. The tactic demonstrates a standard approach to proving geometric properties by reducing them to algebraic calculations.

### Dependencies
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`
- `IMP_IMP`
- `SEGMENT_CONVEX_HULL`
- `CONGRUENT_SEGMENTS`
- `DIST_EQ`
- `dist`
- `NORM_POW_2`
- `VECTOR3_SUB_CONV`
- `VECTOR3_DOT_CONV`
- `REAL_RAT5_EQ_CONV`

### Porting notes (optional)
- The `CONV_TAC` with `ONCE_DEPTH_CONV` are specific to HOL Light's conversion system. In other proof assistants, similar effects might be achieved with targeted simplification or normalization tactics. For example, in Coq, one might use `simpl` or `cbv` combined with rewrite rules.
- The success of this tactic depends heavily on the rewrite rules provided in `edges`. The porter should ensure that equivalent rules or lemmas are available in the target system.
- The `ASM_REWRITE_TAC` is also HOL Light specific by rewriting the goal using assumptions in the context. Other proof assistants have similar automated tactics.


---

## CONGRUENT_FACES_TAC

### Name of formal statement
CONGRUENT_FACES_TAC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONGRUENT_FACES_TAC facets =
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[IMP_IMP] THEN
  REWRITE_TAC[facets] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  W(fun (asl,w) ->
        let t1 = rand(lhand w) and t2 = rand(rand w) in
        let (x1,y1,z1) = three_adjacent_points (dest_setenum t1)
        and (x2,y2,z2) = three_adjacent_points (dest_setenum t2) in
        let th1 = SPECL [`A:real^3^3`;x1;y1;z1;x2;y2;z2] MATRIX_BY_CRAMER in
        let th2 = REWRITE_RULE[VECTOR_3; DET_3] th1 in
        let th3 = CONV_RULE (DEPTH_CONV REAL_RAT5_MUL_CONV) th2 in
        let th4 = CONV_RULE (DEPTH_CONV
         (REAL_RAT5_ADD_CONV ORELSEC REAL_RAT5_SUB_CONV)) th3 in
        let th5 = CONV_RULE let_CONV th4 in
        let th6 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT5_DIV_CONV) th5 in
        let th7 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) th6 in
        let th8 = MP th7 (EQT_ELIM(REWRITE_CONV[] (lhand(concl th7)))) in
        let tms = map rhs (conjuncts(rand(concl th8))) in
        let matt = mk_33matrix tms in
        MATCH_MP_TAC CONGRUENT_SIMPLE THEN EXISTS_TAC matt THEN CONJ_TAC THENL
         [REWRITE_TAC[ORTHOGONAL_MATRIX; CART_EQ] THEN
          SIMP_TAC[transp; LAMBDA_BETA; matrix_mul; mat] THEN
          REWRITE_TAC[DIMINDEX_3; SUM_3; FORALL_3; VECTOR_3; ARITH] THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
          CONV_TAC(DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_EQ_CONV) THEN
          REWRITE_TAC[] THEN NO_TAC;
          REWRITE_TAC[IMAGE_CLAUSES; MATRIX_VECTOR_MUL_3] THEN
          CONV_TAC(ONCE_DEPTH_CONV REAL_RAT5_MUL_CONV) THEN
          CONV_TAC(DEPTH_CONV REAL_RAT5_ADD_CONV) THEN
          REWRITE_TAC[INSERT_AC]]);;
```

### Informal statement
The tactic `CONGRUENT_FACES_TAC` takes a list of theorems `facets` as input and attempts to prove that two faces are congruent. It utilizes equational reasoning, rewriting with arithmetic simplification, the Cramer's rule to establish the existence of a matrix mapping one face to the other, and leverages congruence properties of orthogonal matrices.

### Informal sketch
The tactic `CONGRUENT_FACES_TAC` operates as follows:

- It begins by rewriting the goal using `IMP_CONJ`, `RIGHT_FORALL_IMP_THM`, `IMP_IMP`, and the user-provided theorems in `facets` to expose the core assumptions and the desired conclusion.
- It then applies `REPEAT STRIP_TAC` to eliminate quantifiers or implications from the assumptions.
- Simplifies the assumptions using `ASM_REWRITE_TAC`.
- It then selects two faces from the current goal (`t1` and `t2`), extracts three adjacent points (`x1`, `y1`, `z1`) and (`x2`, `y2`, `z2`) from each.
- Instances `MATRIX_BY_CRAMER` with those points to construct a candidate for a linear transformation matrix `A`.
- It simplifies the candidate matrix using `VECTOR_3` and `DET_3`. It performs arithmetic simplification using `REAL_RAT5_MUL_CONV`, `REAL_RAT5_ADD_CONV`, `REAL_RAT5_SUB_CONV`, `let_CONV`, `REAL_RAT5_DIV_CONV`, and `REAL_RAT5_EQ_CONV`.
- It extracts the entries of the resulting matrix, constructs a 3x3 matrix `matt` and attempts to prove congruence of the two faces using `CONGRUENT_SIMPLE`, existential instantiation with the matrix `matt`, and splitting the resulting conjunction into two subgoals.
- The first subgoal involves showing that the constructed matrix is orthogonal. This is achieved by rewriting with `ORTHOGONAL_MATRIX` and `CART_EQ`, simplifying with properties of transposes, matrix multiplication, and vector indexing, and finally performing arithmetic simplification and rewriting.
- The second subgoal involves showing that the constructed matrix maps the first face to the second. This is achieved by rewriting with image clauses and properties of matrix-vector multiplication then perform arithmetic simplification and rewriting.

### Mathematical insight
The tactic embodies a general strategy for proving the congruence of two geometric faces in 3D space. The core idea is to explicitly construct a matrix that transforms one face into the other and then verify that this matrix is orthogonal (i.e., preserves distances and angles, thus representing a rigid transformation). Cramer's rule is used to find a candidate for the matrix, and extensive rewriting and arithmetic simplification are employed to verify the orthogonality condition.

### Dependencies
- Theorems: `IMP_CONJ`, `RIGHT_FORALL_IMP_THM`, `IMP_IMP`, `ORTHOGONAL_MATRIX`, `CART_EQ`, `DIMINDEX_3`, `SUM_3`, `FORALL_3`, `VECTOR_3`, `ARITH`, `IMAGE_CLAUSES`, `MATRIX_VECTOR_MUL_3`, `INSERT_AC`, `CONGRUENT_SIMPLE`
- Definitions: `transp`, `LAMBDA_BETA`, `matrix_mul`, `mat`
- Conversions: `REAL_RAT5_MUL_CONV`, `REAL_RAT5_ADD_CONV`, `REAL_RAT5_SUB_CONV`, `let_CONV`, `REAL_RAT5_DIV_CONV`, `REAL_RAT5_EQ_CONV`

### Porting notes (optional)
- Porting this tactic to another proof assistant would involve reimplementing its control flow using the target system's tactic language. The core mathematical components, such as matrix operations, Cramer's rule, and orthogonality conditions, would need to be translated into equivalent formalizations.
- The extensive use of rewriting and arithmetic simplification highlights the need for robust simplification capabilities in the target system. The specific conversion tactics used in HOL Light (`REAL_RAT5_MUL_CONV`, etc.) might need to be replaced with analogous simplification routines.
- Pay attention to definitions of real numbers and arithmetic formalization.


---

## TETRAHEDRON_CONGRUENT_EDGES

### Name of formal statement
TETRAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TETRAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_tetrahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_tetrahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC TETRAHEDRON_EDGES);;
```
### Informal statement
For all sets `e1` and `e2`, if `e1` is a face of the standard tetrahedron `std_tetrahedron` with affine dimension 1, and `e2` is a face of the standard tetrahedron `std_tetrahedron` with affine dimension 1, then `e1` is congruent to `e2`.

### Informal sketch
The proof demonstrates that any two edges of the standard tetrahedron are congruent.
- The proof relies on the tactic `CONGRUENT_EDGES_TAC`, which likely unfolds the definition of `congruent` and utilizes properties specific to the edges of the standard tetrahedron (`TETRAHEDRON_EDGES`) to show that there exists a suitable isometry between them.
- The condition `e1 face_of std_tetrahedron /\ aff_dim e1 = &1` specifies that `e1` is an edge of the `std_tetrahedron`. The same condition holds for `e2`. Since the standard tetrahedron is a regular tetrahedron, all its edges are congruent, which is what the theorem formalizes.

### Mathematical insight
This theorem formalizes the geometric property that all edges of a regular tetrahedron are congruent. This is a basic property that is important when reasoning about geometrical figures.

### Dependencies
- Theorems: `TETRAHEDRON_EDGES`
- Tactics: `CONGRUENT_EDGES_TAC`


---

## TETRAHEDRON_CONGRUENT_FACETS

### Name of formal statement
TETRAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TETRAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_tetrahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_tetrahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC TETRAHEDRON_FACETS);;
```
### Informal statement
For all sets `f1` and `f2`, if `f1` is a face of the standard tetrahedron and the affine dimension of `f1` is equal to 2, and `f2` is a face of the standard tetrahedron and the affine dimension of `f2` is equal to 2, then `f1` is congruent to `f2`.

### Informal sketch
The proof proceeds by showing that any two faces of the standard tetrahedron with affine dimension 2 are congruent. This is done using the tactic `CONGRUENT_FACES_TAC` applied to the faces of the tetrahedron, denoted by `TETRAHEDRON_FACETS`. The tactic likely leverages the symmetries of the standard tetrahedron to demonstrate the congruence of the faces.

### Mathematical insight
This theorem formalizes the intuition that all faces of the standard tetrahedron are congruent. This is a fundamental property of regular tetrahedra and important for geometric reasoning involving them.

### Dependencies
- Definitions:
  - `face_of`
  - `std_tetrahedron`
  - `aff_dim`
  - `congruent`
- Theorems:
  - `TETRAHEDRON_FACETS`

### Porting notes (optional)
- The tactic `CONGRUENT_FACES_TAC` is specific to HOL Light, so a porter will need to reconstruct the proof of congruence in the target system. This may involve explicitly constructing a rigid transformation (rotation and/or translation) that maps one face onto the other.
- The proof relies on properties of `std_tetrahedron`, which needs to be defined the same way in the target system to easily apply transformation rules.


---

## CUBE_CONGRUENT_EDGES

### Name of formal statement
CUBE_CONGRUENT_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBE_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_cube /\ aff_dim e1 = &1 /\
           e2 face_of std_cube /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC CUBE_EDGES);;
```
### Informal statement
For all `e1` and `e2`, if `e1` is a face of the standard cube `std_cube` and the affine dimension of `e1` is equal to 1, and `e2` is a face of the standard cube `std_cube` and the affine dimension of `e2` is equal to 1, then `e1` is congruent to `e2`.

### Informal sketch
The theorem states that any two edges of the standard cube are congruent. The proof is discharged using the tactic `CONGRUENT_EDGES_TAC` which applies `CUBE_EDGES`. Thus, the proof likely proceeds by showing that any edge `e1` and `e2` of the standard cube meet the criteria for being congruent using properties specific to the edges of `std_cube`.

### Mathematical insight
This theorem captures the geometric intuition that all edges of a cube have the same length and therefore are congruent. This is used for reasoning about the properties of cubes in a formal setting.

### Dependencies
- Definition: `face_of`
- Definition: `aff_dim`
- Definition: `std_cube`
- Definition: `congruent`
- Tactic: `CONGRUENT_EDGES_TAC`
- Theorem: `CUBE_EDGES`


---

## CUBE_CONGRUENT_FACETS

### Name of formal statement
CUBE_CONGRUENT_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBE_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_cube /\ aff_dim f1 = &2 /\
           f2 face_of std_cube /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC CUBE_FACETS);;
```
### Informal statement
For all `f1` and `f2`, if `f1` is a `face_of` the `std_cube` and the `aff_dim` of `f1` is equal to 2, and `f2` is a `face_of` the `std_cube` and the `aff_dim` of `f2` is equal to 2, then `f1` is `congruent` to `f2`.

### Informal sketch
The theorem states that any two 2-dimensional faces (facets) of the standard cube (`std_cube`) are congruent.

- The proof strategy involves using the tactic `CONGRUENT_FACES_TAC` applied to `CUBE_FACETS`. This tactic likely unfolds the definitions of `face_of`, `aff_dim`, `std_cube`, and `congruent`, then uses properties of `CUBE_FACETS` which likely provides a list of all the faces of a cube, to establish the congruence between any pair of 2-dimensional faces by some kind of symmetry argument.

### Mathematical insight
The standard cube is a highly symmetric object. Intuitively, all its facets (2-dimensional faces) are the same size and shape. Therefore, they must be congruent. The theorem formalizes this intuition. It's a basic geometric property that is crucial when reasoning about properties of euclidean space or polyhedra in formal setting.

### Dependencies
- Definitions: `face_of`, `std_cube`, `aff_dim`, `congruent`
- Theorems: `CUBE_FACETS`


---

## OCTAHEDRON_CONGRUENT_EDGES

### Name of formal statement
OCTAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OCTAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_octahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_octahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC OCTAHEDRON_EDGES);;
```
### Informal statement
For all edges `e1` and `e2`, if `e1` is a face of the standard octahedron `std_octahedron` and the affine dimension of `e1` is 1, and `e2` is a face of the standard octahedron `std_octahedron` and the affine dimension of `e2` is 1, then `e1` is congruent to `e2`.

### Informal sketch
The proof demonstrates that any two edges of the standard octahedron are congruent.

- The theorem `OCTAHEDRON_CONGRUENT_EDGES` is proved by applying `CONGRUENT_EDGES_TAC` to `OCTAHEDRON_EDGES`.
- The tactic `CONGRUENT_EDGES_TAC` likely uses a pre-existing list of the edges of the `std_octahedron` (obtained from `OCTAHEDRON_EDGES`) to verify pairwise congruence. This likely involves showing that the distance between the endpoints of each edge is the same.

### Mathematical insight
This theorem establishes a basic geometric property of the standard octahedron: that all its edges have the same length and are therefore congruent. This fact is essential for further reasoning about the symmetry and regularity of the octahedron.

### Dependencies
- Definition: `face_of`
- Definition: `std_octahedron`
- Definition: `aff_dim`
- Definition: `congruent`
- Theorem: `OCTAHEDRON_EDGES`
- Tactic: `CONGRUENT_EDGES_TAC`


---

## OCTAHEDRON_CONGRUENT_FACETS

### Name of formal statement
OCTAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OCTAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_octahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_octahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC OCTAHEDRON_FACETS);;
```
### Informal statement
For all `f1` and `f2`, if `f1` is a face of the standard octahedron `std_octahedron` and the affine dimension of `f1` is 2, and `f2` is a face of the standard octahedron `std_octahedron` and the affine dimension of `f2` is 2, then `f1` is congruent to `f2`.

### Informal sketch
- The proof demonstrates that any two 2-dimensional faces of the standard octahedron are congruent.
- The proof uses the tactic `CONGRUENT_FACES_TAC` applied to the theorem `OCTAHEDRON_FACETS`. This tactic likely automates the proof by considering all possible pairs of 2-dimensional faces of the standard octahedron and verifying their congruence. The congruence is probably shown by exhibiting an isometry (a distance-preserving transformation) that maps one face onto the other. The enumeration of faces is derived from the theorem `OCTAHEDRON_FACETS`, which lists all the faces of the standard octahedron.

### Mathematical insight
This theorem states a basic geometric property of the regular octahedron: all its faces are congruent equilateral triangles. This is a fundamental property often used in geometric reasoning about octahedra.

### Dependencies
- Definitions: `face_of`, `std_octahedron`, `aff_dim`, `congruent`
- Theorems: `OCTAHEDRON_FACETS`

### Porting notes (optional)
The main challenge is porting the tactic `CONGRUENT_FACES_TAC`. In other proof assistants, one would typically need to explicitly construct the list of faces (corresponding to `OCTAHEDRON_FACETS`) and then prove congruence for all pairs of 2-dimensional faces by finding appropriate isometries. Depending on automation available, this may involve explicit construction of rotation matrices or other transformations.


---

## DODECAHEDRON_CONGRUENT_EDGES

### Name of formal statement
DODECAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DODECAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_dodecahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_dodecahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC DODECAHEDRON_EDGES);;
```
### Informal statement
For all `e1` and `e2`, if `e1` is a face of the standard dodecahedron (`std_dodecahedron`) and the affine dimension of `e1` is equal to 1, and `e2` is a face of the standard dodecahedron and the affine dimension of `e2` is equal to 1, then `e1` is congruent to `e2`.

### Informal sketch
The proof demonstrates that all edges of the standard dodecahedron are congruent.
- Assume `e1` and `e2` are faces of `std_dodecahedron` with affine dimension 1 (i.e., they are edges).
- Apply the `CONGRUENT_EDGES_TAC` tactic with the specific set of edges of the dodecahedron (`DODECAHEDRON_EDGES`) to prove that `e1` and `e2` are congruent. This tactic likely relies on properties of the dodecahedron's symmetry and the definition of congruence to show that any two edges can be mapped to each other via an isometry.
- The tactic `CONGRUENT_EDGES_TAC` reduces the goal to showing congruence using the precomputed list of edges `DODECAHEDRON_EDGES`.

### Mathematical insight
This theorem states that all edges of a regular dodecahedron are congruent. This is a fundamental geometric property of regular polyhedra, stemming from their high degree of symmetry.  The theorem simply formalizes this intuitive geometric fact.

### Dependencies
- `std_dodecahedron`
- `face_of`
- `aff_dim`
- `congruent`
- `DODECAHEDRON_EDGES`
- `CONGRUENT_EDGES_TAC`


---

## DODECAHEDRON_CONGRUENT_FACETS

### Name of formal statement
DODECAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DODECAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_dodecahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_dodecahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC DODECAHEDRON_FACETS);;
```
### Informal statement
For all faces `f1` and `f2`, if `f1` is a face of the standard dodecahedron, and the affine dimension of `f1` is equal to 2, and `f2` is a face of the standard dodecahedron, and the affine dimension of `f2` is equal to 2, then `f1` is congruent to `f2`.

### Informal sketch
The proof demonstrates that any two faces of the standard dodecahedron that have affine dimension 2 are congruent.
- The proof uses the tactic `CONGRUENT_FACES_TAC` applied to the hypothesis `DODECAHEDRON_FACETS`. This tactic likely expands the definition of `congruent` and leverages symmetries inherent to the standard dodecahedron to show that the faces are related by a suitable isometry (translation and rotation) and therefore must be congruent.
- The tactic `CONGRUENT_FACES_TAC` probably uses the explicit list of faces presented by the theorem `DODECAHEDRON_FACETS` to show that each face can be mapped to any other by an appropriate symmetry.

### Mathematical insight
This theorem formalizes the geometric intuition that all faces of a regular dodecahedron are congruent. This is a key property of regular polyhedra and is crucial in establishing their geometric regularity and symmetry. It ensures that the dodecahedron is uniform in its faces.

### Dependencies
- Theorems:
    - `DODECAHEDRON_FACETS`
- Tactics:
    - `CONGRUENT_FACES_TAC`


---

## ICOSAHEDRON_CONGRUENT_EDGES

### Name of formal statement
ICOSAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ICOSAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_icosahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_icosahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC ICOSAHEDRON_EDGES);;
```
### Informal statement
For all sets `e1` and `e2`, if `e1` is a face of the standard icosahedron `std_icosahedron` and the affine dimension of `e1` is equal to 1, and `e2` is a face of the standard icosahedron `std_icosahedron` and the affine dimension of `e2` is equal to 1, then `e1` is congruent to `e2`.

### Informal sketch
The proof demonstrates that all edges (1-dimensional faces) of the standard icosahedron are congruent.
- The tactic `CONGRUENT_EDGES_TAC` is applied to the goal `!e1 e2. e1 face_of std_icosahedron /\ aff_dim e1 = &1 /\ e2 face_of std_icosahedron /\ aff_dim e2 = &1 ==> e1 congruent e2`.
- `ICOSAHERDRON_EDGES` is used as an oracle set of edges for the standard icosahedron.

### Mathematical insight
This theorem establishes a fundamental property of the standard icosahedron, namely, that all its edges are congruent. This is a key geometric feature used in reasoning about its symmetry and other properties.

### Dependencies
- Theorems: `ICOSAHERDRON_EDGES`
- Tactics: `CONGRUENT_EDGES_TAC`


---

## ICOSAHEDRON_CONGRUENT_FACETS

### Name of formal statement
ICOSAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ICOSAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_icosahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_icosahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC ICOSAHEDRON_FACETS);;
```

### Informal statement
For all sets `f1` and `f2`, if `f1` is a face of the standard icosahedron (`std_icosahedron`), the affine dimension of `f1` is equal to 2, `f2` is a face of the standard icosahedron, and the affine dimension of `f2` is equal to 2, then `f1` is congruent to `f2`.

### Informal sketch
The proof proceeds by:
- Applying the `CONGRUENT_FACES_TAC` tactic to the faces of the icosahedron (`ICOSAEDRON_FACETS`).
- This tactic likely leverages the symmetry of the icosahedron and the fact that all its faces are equilateral triangles to establish congruence.

### Mathematical insight
This theorem formalizes the intuitive notion that all faces of a standard icosahedron are congruent to each other. This is a key property stemming from the icosahedron's high degree of symmetry, specifically its faces being equilateral triangles. This result is useful when proving properties that hold for any face of the icosahedron since it suffices to prove it for just one.

### Dependencies
- Constants: `std_icosahedron`
- Definitions: `face_of`, `aff_dim`, `congruent`
- Theorems: `ICOSAEDRON_FACETS`
- Tactics: `CONGRUENT_FACES_TAC`


---

