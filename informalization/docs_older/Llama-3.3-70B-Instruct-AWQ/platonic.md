# platonic.ml

## Overview

Number of statements: 91

The `platonic.ml` file formalizes the existence and uniqueness of the five Platonic solids. It builds upon definitions and theorems from `polyhedron.ml` and utilizes geometric constructions from `cross.ml`. The file proves the existence of the five Platonic solids and shows that there are no other such solids. Its key content is centered around geometric and topological properties of polyhedra.

## std_tetrahedron

### Name of formal statement
std_tetrahedron

### Type of the formal statement
new_definition

### Formal Content
```ocaml
std_tetrahedron =
     convex hull
       {vector[&1;&1;&1],vector[-- &1;-- &1;&1],
        vector[-- &1;&1;-- &1],vector[&1;-- &1;-- &1]}:real^3->bool
```

### Informal statement
The `std_tetrahedron` is defined as the convex hull of the set of four vectors in 3-dimensional real space, specifically `{vector[1;1;1], vector[-1;-1;1], vector[-1;1;-1], vector[1;-1;-1]}`.

### Informal sketch
* The definition begins with the `convex hull` of a set of points, which is the smallest convex set that contains all the points.
* The set of points is defined by four vectors in `real^3` space, which are the vertices of the tetrahedron.
* The `convex hull` operation then generates the tetrahedron as the smallest convex shape that includes these four points.

### Mathematical insight
The `std_tetrahedron` definition represents a standard regular tetrahedron, one of the five Platonic solids. This definition is important in geometry and can be used as a building block for more complex geometric constructions.

### Dependencies
* `convex hull`
* `vector`
* `real^3`

### Porting notes
When translating this definition into other proof assistants, note that the `convex hull` operation and the representation of vectors in 3-dimensional real space may need to be defined or imported from relevant libraries. Additionally, the specific syntax for defining sets and applying operations may differ between systems.

---

## std_cube

### Name of formal statement
std_cube

### Type of the formal statement
new_definition

### Formal Content
```ocaml
std_cube =
     convex hull
       {vector[&1;&1;&1],vector[&1;&1;-- &1],
        vector[&1;-- &1;&1],vector[&1;-- &1;-- &1],
        vector[-- &1;&1;&1],vector[-- &1;&1;-- &1],
        vector[-- &1;-- &1;&1],vector[-- &1;-- &1;-- &1]}:real^3->bool
```

### Informal statement
The `std_cube` is defined as the convex hull of the set of eight vectors in 3-dimensional real space, specifically the vertices of a cube with edge length 2 centered at the origin.

### Informal sketch
* The definition involves constructing a set of vectors representing the vertices of a cube.
* These vertices are given in a specific order and with specific coordinates.
* The `convex hull` operation is then applied to this set of points to form the cube.
* The resulting `std_cube` is a boolean-valued function over `real^3`, indicating whether a point is within the cube or not.

### Mathematical insight
The `std_cube` definition provides a canonical representation of a cube in 3-dimensional space, which is a fundamental geometric object. This definition is important for various applications in geometry, computer graphics, and physics, where the cube serves as a basic building block or a primitive shape.

### Dependencies
* `convex hull`
* `vector`
* `real^3`

### Porting notes
When translating this definition into other proof assistants, special attention should be given to the representation of vectors and the `convex hull` operation. In some systems, vectors might be represented as records or tuples, while in others, they could be defined as a separate type. The `convex hull` operation might be available as a built-in function or require a custom implementation. Additionally, the handling of real numbers and 3-dimensional space might differ between systems, requiring adjustments to the definition.

---

## std_octahedron

### Name of formal statement
std_octahedron

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let std_octahedron = new_definition
 `std_octahedron =
      convex hull
       {vector[&1;&0;&0],vector[-- &1;&0;&0],
        vector[&0;&0;&1],vector[&0;&0;-- &1],
        vector[&0;&1;&0],vector[&0;-- &1;&0]}:real^3->bool`
```

### Informal statement
The `std_octahedron` is defined as the convex hull of a set of six vectors in three-dimensional real space. These vectors are: (1, 0, 0), (-1, 0, 0), (0, 0, 1), (0, 0, -1), (0, 1, 0), and (0, -1, 0).

### Informal sketch
* The definition of `std_octahedron` involves computing the convex hull of a specific set of points.
* The `convex hull` operation is applied to a set containing six vectors, which represent the vertices of an octahedron in 3D space.
* The `vector` function is used to define each point in the set, with coordinates given in the format `(x, y, z)`.
* The resulting `std_octahedron` is a boolean-valued function that represents the region in 3D space enclosed by the convex hull of these points.

### Mathematical insight
The `std_octahedron` definition provides a formal representation of a standard octahedron, which is a fundamental geometric shape. This definition is important in geometry and computer graphics, where it can be used to model and analyze the properties of octahedra. The use of `convex hull` ensures that the resulting shape is the smallest convex set that contains all the given points.

### Dependencies
* `convex hull`
* `vector`
* `real^3->bool`

### Porting notes
When translating this definition to other proof assistants, note that the `convex hull` operation and `vector` function may need to be defined or imported from a library. Additionally, the representation of 3D vectors and boolean-valued functions may differ between systems. In Lean, for example, the `vector` function might be replaced with a `ℝ³` type, while in Coq, the `convex hull` operation might be defined using a separate library or module.

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
      vector[p;&0;--inv p],vector[--p;&0;--inv p]}:real^3->bool
```

### Informal statement
The `std_dodecahedron` is defined as the convex hull of a set of vectors in 3-dimensional real space. The set consists of eight vertices of a cube with side length 2, centered at the origin, and twelve vertices of an inscribed dodecahedron. The dodecahedron's vertices are defined using the golden ratio `p = (1 + sqrt(5)) / 2`, which is used to calculate the coordinates of the vertices.

### Informal sketch
* Define the golden ratio `p` as `(1 + sqrt(5)) / 2`
* Calculate the coordinates of the vertices of the cube and the dodecahedron using `p`
* Define the set of vertices of the `std_dodecahedron` as the union of the cube's and dodecahedron's vertices
* Compute the convex hull of the set of vertices to obtain the `std_dodecahedron`

### Mathematical insight
The `std_dodecahedron` is a geometric construction that combines a cube and a dodecahedron to form a convex polyhedron. The use of the golden ratio `p` ensures that the dodecahedron's vertices are properly positioned with respect to the cube's vertices. This construction is likely used to establish geometric properties or theorems about the dodecahedron or its relation to the cube.

### Dependencies
* `convex hull`
* `vector`
* `sqrt`
* `inv`

### Porting notes
When porting this definition to another proof assistant, note that the `convex hull` operation may need to be defined or imported separately. Additionally, the use of `sqrt` and `inv` may require specific libraries or imports. The definition of `vector` and its operations may also need to be adapted to the target system.

---

## std_icosahedron

### Name of formal statement
std_icosahedron

### Type of the formal statement
new_definition

### Formal Content
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
        vector[p; &0; -- &1],vector[--p; &0; -- &1]}:real^3->bool`
```

### Informal statement
The `std_icosahedron` is defined as the convex hull of a set of twelve vectors in three-dimensional real space. The set of vectors is defined using the value `p`, which is calculated as `(1 + sqrt(5)) / 2`. The twelve vectors are: 
- `vector[0; 1; p]`
- `vector[0; 1; -p]`
- `vector[0; -1; p]`
- `vector[0; -1; -p]`
- `vector[1; p; 0]`
- `vector[1; -p; 0]`
- `vector[-1; p; 0]`
- `vector[-1; -p; 0]`
- `vector[p; 0; 1]`
- `vector[-p; 0; 1]`
- `vector[p; 0; -1]`
- `vector[-p; 0; -1]`

### Informal sketch
* The construction starts by calculating the value `p`, which involves the square root of `5`.
* This value `p` is then used to define twelve specific vectors in three-dimensional space.
* The `std_icosahedron` is defined as the convex hull of the set of these twelve vectors.
* The definition relies on understanding the `convex hull` operation and the geometric interpretation of vectors in `real^3` space.

### Mathematical insight
The `std_icosahedron` definition represents a standard geometric shape, an icosahedron, using its vertices. The icosahedron is a regular polyhedron with 20 triangular faces, and its construction is fundamental in geometry. This definition is important for geometric computations and proofs involving 3D shapes.

### Dependencies
- `convex hull`
- `vector`
- `sqrt`
- `real^3`

### Porting notes
When porting this definition to another proof assistant, pay attention to how vectors and convex hulls are represented. Some systems may have built-in support for geometric objects, while others might require a more manual construction. Additionally, the calculation of `p` involving `sqrt(5)` might need special handling depending on how real numbers and square roots are treated in the target system.

---

## REAL_RAT5_OF_RAT_CONV

### Name of formal statement
REAL_RAT5_OF_RAT_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let REAL_RAT5_OF_RAT_CONV =
  let pth = prove
   (`p = p + &0 * sqrt(&5)`,
    REAL_ARITH_TAC) in
  let conv = REWR_CONV pth in
  fun tm -> if is_ratconst tm then conv tm else REFL tm
```

### Informal statement
This definition introduces a conversion function `REAL_RAT5_OF_RAT_CONV` that operates on terms. It first proves a theorem `pth` stating that a variable `p` is equal to itself plus zero times the square root of 5, using the `REAL_ARITH_TAC` tactic. It then defines a conversion `conv` based on this proof. The function applies `conv` to a term `tm` if `tm` is a rational constant; otherwise, it applies the `REFL` conversion, which leaves the term unchanged.

### Informal sketch
* The definition starts by proving a simple equality `p = p + &0 * sqrt(&5)` using `REAL_ARITH_TAC`, which is a tactic for reasoning about real arithmetic.
* This proof is then used to create a conversion `conv` via `REWR_CONV`, which presumably applies the proven equality as a rewrite rule.
* The main conversion function checks if a given term `tm` is a rational constant using `is_ratconst`.
* If `tm` is a rational constant, it applies the `conv` conversion; otherwise, it leaves the term unchanged by applying `REFL`.

### Mathematical insight
This definition appears to be part of a mechanism for handling expressions in the field of rational numbers extended by the square root of 5, denoted as Q[sqrt(5)]. The key idea is to ensure that numbers are represented in a canonical form, either as a rational constant `r` or as an expression `r1 + r2 * sqrt(5)` where `r2` is nonzero. The conversion function seems to facilitate this by adjusting terms to fit into this canonical representation, specifically targeting rational constants for transformation.

### Dependencies
* `REAL_ARITH_TAC`
* `REWR_CONV`
* `REFL`
* `is_ratconst`

### Porting notes
When translating this definition into another proof assistant, careful attention should be paid to how rational constants and expressions involving square roots are handled. The equivalent of `REAL_ARITH_TAC` and the `REWR_CONV` mechanism will need to be identified in the target system. Additionally, the `is_ratconst` check and the application of `REFL` for non-rational constants must be appropriately translated, considering the target system's handling of term equality and rewriting.

---

## REAL_RAT_OF_RAT5_CONV

### Name of formal statement
REAL_RAT_OF_RAT5_CONV

### Type of the formal statement
Theorem/Conversion

### Formal Content
```ocaml
let REAL_RAT_OF_RAT5_CONV =
  let pth = prove
   (`p + &0 * sqrt(&5) = p`,
    REAL_ARITH_TAC) in
  GEN_REWRITE_CONV TRY_CONV [pth];;
```

### Informal statement
For any real number `p`, the expression `p + 0 * sqrt(5)` is equal to `p`. This equality is used to create a conversion `REAL_RAT_OF_RAT5_CONV` that can be applied to rewrite expressions.

### Informal sketch
* The proof starts by establishing the theorem `p + 0 * sqrt(5) = p` using `REAL_ARITH_TAC`, which likely involves basic properties of real arithmetic.
* This theorem is then used to create a conversion `REAL_RAT_OF_RAT5_CONV` via `GEN_REWRITE_CONV` and `TRY_CONV`, indicating a generalization of the proven equality into a more applicable form.
* The conversion likely aims to simplify expressions by eliminating the `0 * sqrt(5)` term, leveraging the proven equality.

### Mathematical insight
The key idea behind `REAL_RAT_OF_RAT5_CONV` is to simplify expressions involving the square root of 5 by eliminating terms that do not contribute to the value, such as `0 * sqrt(5)`. This conversion is important for maintaining simplicity in expressions and can be crucial in more complex algebraic manipulations involving real numbers and square roots.

### Dependencies
* `REAL_ARITH_TAC`
* `GEN_REWRITE_CONV`
* `TRY_CONV`

### Porting notes
When translating `REAL_RAT_OF_RAT5_CONV` into another proof assistant, pay attention to how real arithmetic and conversions are handled. The equivalent of `REAL_ARITH_TAC` and the conversion mechanisms (`GEN_REWRITE_CONV`, `TRY_CONV`) might differ. For instance, in systems like Lean or Coq, you might need to use specific tactics or libraries for real numbers and rewriting. Ensure that the target system supports similar generalization and application of proven equalities as conversions.

---

## REAL_RAT5_ADD_CONV

### Name of formal statement
REAL_RAT5_ADD_CONV

### Type of the formal statement
Theorem/conversion rule

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
   REAL_RAT_OF_RAT5_CONV)
```

### Informal statement
The theorem `REAL_RAT5_ADD_CONV` states that for any real numbers `a1`, `b1`, `a2`, and `b2`, the expression `(a1 + b1 * sqrt(5)) + (a2 + b2 * sqrt(5))` is equal to `(a1 + a2) + (b1 + b2) * sqrt(5)`. This equality is proven using `REAL_ARITH_TAC` and then used to define a conversion rule for adding expressions of the form `a + b * sqrt(5)`.

### Informal sketch
* The proof begins by establishing the equality `(a1 + b1 * sqrt(5)) + (a2 + b2 * sqrt(5)) = (a1 + a2) + (b1 + b2) * sqrt(5)` using `REAL_ARITH_TAC`.
* This equality is then used to define a conversion rule `REAL_RAT5_ADD_CONV` that combines `REAL_RAT_ADD_CONV` with several other conversions:
  + `BINOP_CONV REAL_RAT5_OF_RAT_CONV` for handling binary operations
  + `GEN_REWRITE_CONV I [pth]` for rewriting using the proven equality
  + `LAND_CONV REAL_RAT_ADD_CONV` and `RAND_CONV(LAND_CONV REAL_RAT_ADD_CONV)` for handling conjunctions and recursive applications
  + `REAL_RAT_OF_RAT5_CONV` for converting back to rational expressions

### Mathematical insight
The `REAL_RAT5_ADD_CONV` conversion rule is designed to simplify expressions involving the sum of two terms of the form `a + b * sqrt(5)`. By applying this rule, one can rearrange such expressions into a more canonical form, which can be useful for further reasoning or computation. The rule relies on basic properties of arithmetic and the definition of `sqrt(5)`, making it a fundamental tool for manipulating expressions involving irrational numbers.

### Dependencies
* `REAL_ARITH_TAC`
* `REAL_RAT_ADD_CONV`
* `BINOP_CONV`
* `REAL_RAT5_OF_RAT_CONV`
* `GEN_REWRITE_CONV`
* `LAND_CONV`
* `RAND_CONV`
* `REAL_RAT_OF_RAT5_CONV`

### Porting notes
When translating `REAL_RAT5_ADD_CONV` to another proof assistant, pay attention to the handling of `sqrt(5)` and the `REAL_ARITH_TAC` tactic, as these may be represented differently. Additionally, the conversion rule's reliance on `ORELSEC` and `THENC` may require careful translation to ensure that the resulting rule is applied correctly in the target system.

---

## REAL_RAT5_SUB_CONV

### Name of formal statement
REAL_RAT5_SUB_CONV

### Type of the formal statement
Theorem/conversion rule

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
   REAL_RAT_OF_RAT5_CONV)
```

### Informal statement
The theorem `REAL_RAT5_SUB_CONV` asserts that for any real numbers `a1`, `b1`, `a2`, and `b2`, the expression `(a1 + b1 * sqrt(5)) - (a2 + b2 * sqrt(5))` is equal to `(a1 - a2) + (b1 - b2) * sqrt(5)`. This equality is proven using `REAL_ARITH_TAC` and then used to define a conversion rule for simplifying expressions involving subtraction of real numbers of the form `a + b * sqrt(5)`.

### Informal sketch
* The proof starts by establishing the key equality `(a1 + b1 * sqrt(5)) - (a2 + b2 * sqrt(5)) = (a1 - a2) + (b1 - b2) * sqrt(5)` using `REAL_ARITH_TAC`.
* This equality is then used as a rewrite rule in `GEN_REWRITE_CONV` to simplify expressions.
* The conversion rule `REAL_RAT5_SUB_CONV` is defined by combining several conversions:
  + `REAL_RAT_SUB_CONV` for simplifying real rational subtractions
  + `BINOP_CONV REAL_RAT5_OF_RAT_CONV` for converting between representations
  + `LAND_CONV REAL_RAT_SUB_CONV` and `RAND_CONV(LAND_CONV REAL_RAT_SUB_CONV)` for applying the conversion to the left and right parts of expressions, respectively
  + `REAL_RAT_OF_RAT5_CONV` for converting back to a standard form
* The `ORELSEC` operator is used to combine these conversions, attempting each in sequence until one succeeds.

### Mathematical insight
This theorem and conversion rule are crucial for simplifying expressions involving real numbers extended with `sqrt(5)`, enabling more efficient manipulation and proof of properties in this domain. The use of `sqrt(5)` indicates that the theory is working within a context that requires handling irrational numbers, which is common in number theory and algebra.

### Dependencies
* `REAL_ARITH_TAC`
* `REAL_RAT_SUB_CONV`
* `REAL_RAT5_OF_RAT_CONV`
* `GEN_REWRITE_CONV`
* `LAND_CONV`
* `RAND_CONV`
* `REAL_RAT_OF_RAT5_CONV`

### Porting notes
When porting `REAL_RAT5_SUB_CONV` to another proof assistant, pay special attention to how that system handles:
* Extensions of the real numbers by irrational numbers like `sqrt(5)`
* Conversion rules and tactics for simplifying expressions
* The equivalent of `ORELSEC` for combining conversion rules
* Differences in how binders and quantifiers are handled in the target system may affect the direct translation of `GEN_REWRITE_CONV` and other tactics.

---

## REAL_RAT5_MUL_CONV

### Name of formal statement
REAL_RAT5_MUL_CONV

### Type of the formal statement
Theorem/Conversion Rule

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
The `REAL_RAT5_MUL_CONV` conversion rule is defined for multiplying two expressions of the form `a1 + b1 * sqrt(5)` and `a2 + b2 * sqrt(5)`, where `a1`, `b1`, `a2`, and `b2` are rational numbers. It states that the product of these two expressions is equal to `(a1 * a2 + 5 * b1 * b2) + (a1 * b2 + a2 * b1) * sqrt(5)`. This rule is used to simplify multiplication involving square roots of 5 in rational expressions.

### Informal sketch
* The proof begins by using the `MP_TAC` tactic with `ISPEC` to instantiate the `SQRT_POW_2` theorem for the case of `&5`, which is then followed by `CONV_TAC REAL_FIELD` to convert the goal into a form that can be solved using field operations.
* The `REAL_RAT5_MUL_CONV` conversion is defined as a combination of several conversion rules applied in sequence, including `REAL_RAT_MUL_CONV`, `BINOP_CONV`, `GEN_REWRITE_CONV`, `LAND_CONV`, and `RAND_CONV`.
* Key steps involve rewriting the multiplication using `GEN_REWRITE_CONV` with the proved theorem `pth`, and then applying various conversions to simplify the expression, including `REAL_RAT_MUL_CONV`, `REAL_RAT_ADD_CONV`, and `REAL_RAT_OF_RAT5_CONV`.

### Mathematical insight
This conversion rule is essential for simplifying expressions involving the multiplication of rational numbers and square roots of 5, which is crucial in various mathematical theories, especially those involving quadratic fields and algebraic number theory. The rule leverages the properties of fields and the specific form of expressions involving `sqrt(5)` to provide a simplified result that can be more easily manipulated in further calculations.

### Dependencies
* Theorems:
  * `SQRT_POW_2`
* Conversion rules:
  * `REAL_RAT_MUL_CONV`
  * `BINOP_CONV`
  * `GEN_REWRITE_CONV`
  * `LAND_CONV`
  * `RAND_CONV`
  * `REAL_RAT_ADD_CONV`
  * `REAL_RAT_OF_RAT5_CONV`
* Definitions:
  * `REAL_RAT5_OF_RAT_CONV`

### Porting notes
When porting this conversion rule to another proof assistant, special attention should be given to how each system handles rewriting and conversion rules, especially in the context of algebraic manipulations and field operations. The porting process may require adapting the sequence of conversions and rewrites to match the target system's capabilities and tactic language. Additionally, ensuring that the `SQRT_POW_2` theorem and other dependencies are appropriately translated or proved in the target system is crucial for the correctness of the ported `REAL_RAT5_MUL_CONV` rule.

---

## REAL_RAT5_INV_CONV

### Name of formal statement
REAL_RAT5_INV_CONV

### Type of the formal statement
Theorem/Conversion Rule

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
Assuming that $a^2$ is not equal to $5b^2$, the inverse of $a + b\sqrt{5}$ is equal to $\frac{a}{a^2 - 5b^2} - \frac{b}{a^2 - 5b^2}\sqrt{5}$.

### Informal sketch
* The proof starts by assuming the condition $a^2 \neq 5b^2$.
* It then applies various `GEN_REWRITE_TAC` and `SUBGOAL_THEN` steps to manipulate the expression for the inverse, utilizing `SQRT_POW_2`, `REAL_ENTIRE`, and `DE_MORGAN_THM` to handle square roots and field operations.
* Key steps involve using `PART_MATCH` to align the goal with a known theorem, `MP` for modus ponens, `EQT_ELIM` for equality elimination, and several `CONV_RULE` applications with specific conversions (`REAL_RAT_REDUCE_CONV`, `REAL_RAT_NEG_CONV`, `REAL_RAT_POW_CONV`, `REAL_RAT_MUL_CONV`, `REAL_RAT_SUB_CONV`, `REAL_RAT_DIV_CONV`) to transform the expression into the desired form.
* The conversion rule `REAL_RAT_INV_CONV` is defined to attempt the conversion directly or, upon failure, apply these steps in sequence to achieve the proof.

### Mathematical insight
This theorem provides a specific formula for the inverse of a sum involving a square root, which is crucial in algebraic manipulations involving irrational numbers, particularly in the context of quadratic fields like $\mathbb{Q}(\sqrt{5})$. The condition $a^2 \neq 5b^2$ ensures the denominator is non-zero, making the formula valid.

### Dependencies
* Theorems:
  + `SQRT_POW_2`
  + `REAL_ENTIRE`
  + `DE_MORGAN_THM`
* Definitions/Conversion Rules:
  + `REAL_RAT_REDUCE_CONV`
  + `REAL_RAT_NEG_CONV`
  + `REAL_RAT_POW_CONV`
  + `REAL_RAT_MUL_CONV`
  + `REAL_RAT_SUB_CONV`
  + `REAL_RAT_DIV_CONV`
  + `REAL_RAT_INV_CONV`

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles algebraic manipulations, especially those involving square roots and field operations. The use of `CONV_RULE` with specific conversions may need to be adapted, as different systems have varying levels of support for automated proof and conversion tactics. Additionally, the handling of binders and the representation of the condition $a^2 \neq 5b^2$ may require careful consideration to ensure the formalization accurately captures the mathematical intent.

---

## REAL_RAT5_DIV_CONV

### Name of formal statement
REAL_RAT5_DIV_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let REAL_RAT5_DIV_CONV =
  GEN_REWRITE_CONV I [real_div] THENC
  RAND_CONV REAL_RAT5_INV_CONV THENC
  REAL_RAT5_MUL_CONV;;
```

### Informal statement
The `REAL_RAT5_DIV_CONV` is a conversion that transforms expressions involving real number division into a specific form, utilizing the `GEN_REWRITE_CONV` with the `real_div` rule, followed by an application of `RAND_CONV` with the `REAL_RAT5_INV_CONV` conversion, and finally applying the `REAL_RAT5_MUL_CONV` conversion.

### Informal sketch
* The conversion starts with a general rewriting step using `GEN_REWRITE_CONV` with the `I` identity theorem and the `real_div` rule, which aims to set up the expression for further manipulation.
* Next, it applies `RAND_CONV` with the `REAL_RAT5_INV_CONV` conversion to the right-hand side of the expression, which is expected to transform the expression involving division into a form suitable for multiplication.
* Finally, it applies the `REAL_RAT5_MUL_CONV` conversion, which should further simplify or normalize the expression to the desired form.

### Mathematical insight
The `REAL_RAT5_DIV_CONV` conversion appears to be designed to manipulate expressions involving division of real numbers into a form that is more amenable to further reasoning or computation, likely leveraging properties of real numbers and rational approximations. This could be crucial in proofs or derivations that require handling real number divisions in a specific manner.

### Dependencies
* `GEN_REWRITE_CONV`
* `real_div`
* `RAND_CONV`
* `REAL_RAT5_INV_CONV`
* `REAL_RAT5_MUL_CONV`

### Porting notes
When translating this conversion into another proof assistant, special attention should be given to how each system handles rewriting and conversion tactics, especially in the context of real numbers and rational approximations. The equivalent of `GEN_REWRITE_CONV`, `RAND_CONV`, and the specific conversions `REAL_RAT5_INV_CONV` and `REAL_RAT5_MUL_CONV` will need to be identified or implemented in the target system. Additionally, the handling of real number properties and the specific form of `real_div` may vary, requiring careful consideration to ensure the conversion achieves the same mathematical effect.

---

## REAL_RAT5_LE_CONV

### Name of formal statement
REAL_RAT5_LE_CONV

### Type of the formal statement
Theorem

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
   REAL_RAT_REDUCE_CONV)
```

### Informal statement
The theorem `REAL_RAT5_LE_CONV` states that for all real numbers `x` and `y`, the following equivalence holds: `x` is less than or equal to `y` times the square root of `5` if and only if one of the following conditions is true: 
1. `x` is less than or equal to `0` and `0` is less than or equal to `y`, 
2. `0` is less than or equal to `x` and `0` is less than or equal to `y` and `x` squared is less than or equal to `5` times `y` squared, 
or 
3. `x` is less than or equal to `0` and `y` is less than or equal to `0` and `5` times `y` squared is less than or equal to `x` squared. 
Furthermore, it proves that `(a1 + b1 * sqrt(5))` is less than or equal to `(a2 + b2 * sqrt(5))` if and only if one of the following conditions holds: 
1. `a1` is less than or equal to `a2` and `b1` is less than or equal to `b2`, 
2. `a2` is less than or equal to `a1` and `b1` is less than or equal to `b2` and `(a1 - a2)` squared is less than or equal to `5` times `(b2 - b1)` squared, 
or 
3. `a1` is less than or equal to `a2` and `b2` is less than or equal to `b1` and `5` times `(b2 - b1)` squared is less than or equal to `(a1 - a2)` squared.

### Informal sketch
* The proof first establishes a lemma about the relationship between a real number `x`, `y`, and the square root of `5`.
* It uses `REPEAT GEN_TAC` to generalize the variables, then applies `MP_TAC` with `ISPEC `&5`` `SQRT_POW_2` to introduce a key inequality involving the square root of `5`.
* The proof then applies various rewriting and simplification tactics, including `REWRITE_TAC`, `DISCH_THEN`, `GEN_REWRITE_TAC`, and `REAL_ARITH_TAC`, to manipulate and simplify the inequalities.
* For the second part, it uses `REWRITE_TAC` with a specific arithmetic rule to transform the expression, then applies the previously established lemma and further simplifications to derive the final equivalence.

### Mathematical insight
The theorem `REAL_RAT5_LE_CONV` provides a crucial equivalence for comparing expressions involving the square root of `5`, which is essential in various mathematical contexts, particularly in algebra and geometry. The ability to convert between different forms of inequalities facilitates reasoning and proof construction in these areas.

### Dependencies
* Theorems: 
  - `SQRT_POW_2`
  - `REAL_LE_MUL_EQ`
  - `REAL_POS`
  - `REAL_POW_MUL`
  - `REAL_LE_SQUARE_ABS`
* Definitions: 
  - `REAL_RAT_LE_CONV`
  - `REAL_RAT5_OF_RAT_CONV`
  - `REAL_RAT_REDUCE_CONV`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of real numbers, square roots, and the specific arithmetic rules and lemmas used. The structure of the proof, involving the establishment of a key lemma followed by its application in a more complex equivalence, should be preserved. However, the exact tactics and their order may vary depending on the target system's capabilities and proof scripting language.

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
This statement defines a conversion `REAL_RAT5_EQ_CONV` for proving equalities involving real numbers and rational numbers, leveraging the antisymmetry of the less-than-or-equal-to relation (`REAL_LE_ANTISYM`), a conversion for proving less-than-or-equal-to relations between real and rational numbers (`REAL_RAT5_LE_CONV`), and applying clauses for conjunctions (`AND_CLAUSES`).

### Informal sketch
* The conversion starts by applying `GEN_REWRITE_CONV` with the inverse of `REAL_LE_ANTISYM` to potentially transform equalities into less-than-or-equal-to relations.
* It then applies `BINOP_CONV` with `REAL_RAT5_LE_CONV` to handle the comparison between real and rational numbers.
* Finally, it applies `GEN_REWRITE_CONV` again, this time with `AND_CLAUSES`, to simplify any conjunctions that may have arisen during the previous steps.
* The use of `THENC` indicates a sequential application of these conversions, aiming to transform the original goal into a more manageable form.

### Mathematical insight
This conversion is designed to facilitate proofs involving comparisons between real and rational numbers, exploiting the properties of order relations and the specific characteristics of rational numbers to simplify or solve these comparisons. It fits into a broader theory of real numbers and their interactions with rational numbers, providing a tool for automated reasoning in this domain.

### Dependencies
* Theorems:
  + `REAL_LE_ANTISYM`
  + `REAL_RAT5_LE_CONV`
* Definitions:
  + `GEN_REWRITE_CONV`
  + `BINOP_CONV`
  + `AND_CLAUSES`

### Porting notes
When translating this conversion into another proof assistant, special attention should be paid to how each system handles rewriting, conversions, and the manipulation of real and rational numbers. The direct equivalents of `GEN_REWRITE_CONV`, `BINOP_CONV`, and the specific tactics like `GSYM` and `THENC` may vary, requiring adjustments to replicate the exact strategy in a different system. Additionally, the representation and handling of real and rational numbers, as well as the properties like `REAL_LE_ANTISYM`, need to be correctly mapped to their counterparts in the target system.

---

## VECTOR3_SUB_CONV

### Name of formal statement
VECTOR3_SUB_CONV

### Type of the formal statement
Theorem/Conversion Rule

### Formal Content
```ocaml
let VECTOR3_SUB_CONV =
  let pth = prove
   (`vector[x1;x2;x3] - vector[y1;y2;y3]:real^3 =
     vector[x1-y1; x2-y2; x3-y3]`,
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
    REWRITE_TAC[VECTOR_3; VECTOR_SUB_COMPONENT]) in
  GEN_REWRITE_CONV I [pth] THENC RAND_CONV(LIST_CONV REAL_RAT5_SUB_CONV)
```

### Informal statement
The theorem states that the difference between two vectors `vector[x1; x2; x3]` and `vector[y1; y2; y3]` in 3-dimensional real space is equal to the vector `vector[x1 - y1; x2 - y2; x3 - y3]`.

### Informal sketch
* The proof starts with the goal of showing the equality between the difference of two vectors and the vector of component-wise differences.
* It first applies simplification using `SIMP_TAC` with theorems `CART_EQ`, `DIMINDEX_3`, and `FORALL_3` to set up the equation.
* Then, it applies `REWRITE_TAC` with `VECTOR_3` and `VECTOR_SUB_COMPONENT` to transform the vector operations into component-wise operations.
* The conversion rule `GEN_REWRITE_CONV` is used to generalize the proof, and `RAND_CONV` with `LIST_CONV` and `REAL_RAT5_SUB_CONV` are applied to handle the component-wise subtraction in the context of rational numbers extended with the square root of 5.

### Mathematical insight
This theorem provides a fundamental property of vector subtraction in 3-dimensional space, showing that it can be reduced to component-wise subtraction. This is crucial for manipulating vectors in geometric and algebraic contexts, especially when working with rational coordinates extended by irrational numbers like the square root of 5.

### Dependencies
#### Theorems
* `CART_EQ`
* `DIMINDEX_3`
* `FORALL_3`
* `VECTOR_3`
* `VECTOR_SUB_COMPONENT`
#### Definitions
* `VECTOR`
* `REAL_RAT5_SUB_CONV`

### Porting notes
When translating this into another proof assistant, special attention should be paid to how vectors and their operations are defined, as well as how rational numbers extended with irrational numbers are handled. The `GEN_REWRITE_CONV` and `RAND_CONV` tactics may have direct analogs in other systems, but their application and the underlying logic of the proof should be carefully mirrored to ensure correctness.

---

## VECTOR3_CROSS_CONV

### Name of formal statement
VECTOR3_CROSS_CONV

### Type of the formal statement
Theorem/Conversion Rule

### Formal Content
```ocaml
let VECTOR3_CROSS_CONV =
  let pth = prove
   (`(vector[x1;x2;x3]) cross (vector[y1;y2;y3]) =
     vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1]`,
    REWRITE_TAC[cross; VECTOR_3]) in
  GEN_REWRITE_CONV I [pth] THENC
  RAND_CONV(LIST_CONV(BINOP_CONV REAL_RAT5_MUL_CONV THENC REAL_RAT5_SUB_CONV))
```

### Informal statement
The conversion rule `VECTOR3_CROSS_CONV` proves that the cross product of two vectors `vector[x1;x2;x3]` and `vector[y1;y2;y3]` is equal to the vector `vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1]`.

### Informal sketch
* The proof starts by using the `REWRITE_TAC` tactic with the `cross` and `VECTOR_3` theorems to establish the equality of the cross product expression.
* The `GEN_REWRITE_CONV` tactic is then applied to generalize the proof to any vectors.
* The `RAND_CONV` and `LIST_CONV` tactics are used in combination with `BINOP_CONV`, `REAL_RAT5_MUL_CONV`, and `REAL_RAT5_SUB_CONV` to handle the arithmetic operations and vector components.
* The key steps involve recognizing the `cross` product and applying the `VECTOR_3` definition to expand the vectors.

### Mathematical insight
This conversion rule provides a way to compute the cross product of two 3-dimensional vectors, which is a fundamental operation in vector calculus and geometry. The rule is based on the definition of the cross product and the representation of vectors in 3-dimensional space.

### Dependencies
* `cross`
* `VECTOR_3`
* `REAL_RAT5_MUL_CONV`
* `REAL_RAT5_SUB_CONV`

### Porting notes
When translating this conversion rule to other proof assistants, pay attention to the handling of vector operations and arithmetic. The `REWRITE_TAC` and `GEN_REWRITE_CONV` tactics may have counterparts in other systems, but the specific implementation of `RAND_CONV` and `LIST_CONV` might require adjustments. Additionally, the `REAL_RAT5_MUL_CONV` and `REAL_RAT5_SUB_CONV` tactics may need to be replaced with equivalent arithmetic conversion rules in the target system.

---

## VECTOR3_EQ_0_CONV

### Name of formal statement
VECTOR3_EQ_0_CONV

### Type of the formal statement
Theorem/Conversion Rule

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
  REWRITE_CONV;;
```

### Informal statement
The theorem `VECTOR3_EQ_0_CONV` states that a vector `vector[x1; x2; x3]` in `real^3` is equal to the zero vector `vec 0` if and only if each of its components `x1`, `x2`, and `x3` is equal to `0`. This equivalence is expressed as `x1 = 0 /\ x2 = 0 /\ x3 = 0`.

### Informal sketch
* The proof starts by setting up the equivalence to be proven: `vector[x1; x2; x3] = vec 0` if and only if `x1 = 0 /\ x2 = 0 /\ x3 = 0`.
* It then applies `SIMP_TAC` with theorems `CART_EQ`, `DIMINDEX_3`, and `FORALL_3` to simplify the statement, leveraging properties of Cartesian equality, dimension indices, and universal quantification.
* Next, it uses `REWRITE_TAC` with `VECTOR_3` and `VEC_COMPONENT` to rewrite the vector equation in terms of its components.
* The `GEN_REWRITE_CONV` is applied to generalize the proof, followed by `DEPTH_BINOP_CONV` on the conjunction operator `/\)` and `REAL_RAT5_EQ_CONV` for real number equality, and finally `REWRITE_CONV` to conclude the conversion.

### Mathematical insight
This theorem provides a fundamental equivalence for vectors in 3-dimensional real space, allowing for the simplification of vector equations by reducing them to component-wise comparisons. It is essential for various geometric and algebraic manipulations in vector spaces.

### Dependencies
#### Theorems
* `CART_EQ`
* `DIMINDEX_3`
* `FORALL_3`
* `VECTOR_3`
* `VEC_COMPONENT`
* `REAL_RAT5_EQ_CONV`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles vector operations, real number arithmetic, and the representation of `vec 0`. Specifically, consider how to express the component-wise equality and how the different systems automate or require manual specification of the proof steps, potentially leveraging tactics or built-in decision procedures for real numbers.

---

## VECTOR3_DOT_CONV

### Name of formal statement
VECTOR3_DOT_CONV

### Type of the formal statement
Theorem/Conversion Rule

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
  REAL_RAT5_ADD_CONV
```

### Informal statement
The conversion rule `VECTOR3_DOT_CONV` is defined such that for any two vectors `vector[x1; x2; x3]` and `vector[y1; y2; y3]` in 3-dimensional real space, the dot product of these vectors is equal to the sum of the products of their corresponding components, i.e., `x1*y1 + x2*y2 + x3*y3`.

### Informal sketch
* The proof starts by establishing the equation `(vector[x1;x2;x3]:real^3) dot (vector[y1;y2;y3]) = x1*y1 + x2*y2 + x3*y3` using `REWRITE_TAC` with `DOT_3` and `VECTOR_3` as rewrite rules.
* It then applies `GEN_REWRITE_CONV` to generalize this equation.
* The conversion continues by applying `DEPTH_BINOP_CONV` for the `(+):real->real->real` operator, combined with `REAL_RAT5_MUL_CONV` for handling multiplication, followed by `RAND_CONV` with `REAL_RAT5_ADD_CONV` for addition, and finally another application of `REAL_RAT5_ADD_CONV` to ensure the expression is fully simplified.

### Mathematical insight
This conversion rule is fundamental in linear algebra, providing a way to compute the dot product of two vectors in 3-dimensional space. It is crucial for various geometric and algebraic operations, including calculating vector lengths, determining orthogonality, and projecting vectors onto each other.

### Dependencies
#### Theorems and Definitions
* `DOT_3`
* `VECTOR_3`
* `REAL_RAT5_MUL_CONV`
* `REAL_RAT5_ADD_CONV`

### Porting notes
When translating `VECTOR3_DOT_CONV` into another proof assistant, pay special attention to how vector operations and the dot product are defined. Ensure that the target system supports similar rewrite tactics or conversion rules, such as `REWRITE_TAC`, `GEN_REWRITE_CONV`, `DEPTH_BINOP_CONV`, and specific convolution rules like `REAL_RAT5_MUL_CONV` and `REAL_RAT5_ADD_CONV`. Differences in handling real numbers, vectors, and the dot product operation may require adjustments to the proof strategy.

---

## STD_DODECAHEDRON

### Name of formal statement
STD_DODECAHEDRON

### Type of the formal statement
new_definition

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
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[])
```

### Informal statement
The `STD_DODECAHEDRON` is defined as the convex hull of a set of 20 vectors in 3-dimensional space. These vectors are specified by their coordinates, involving rational numbers and the square root of 5. The definition involves proving that a specific expression for the inverse of the golden ratio is equal to another expression involving the square root of 5.

### Informal sketch
* The definition of `STD_DODECAHEDRON` starts with specifying the vertices of a dodecahedron using vectors with rational and irrational coordinates.
* The `golden_inverse` lemma proves that the inverse of the golden ratio `(&1 + sqrt(&5)) / &2` can be expressed as `-- &1 / &2 + &1 / &2 * sqrt(&5)`.
* The proof involves applying various rewriting and conversion tactics, including `MP_TAC`, `CONV_TAC`, `REWRITE_TAC`, to simplify and manipulate the expressions.
* Key steps include using `SQRT_POW_2` to handle the square root, and `REAL_FIELD` to apply field properties to the real numbers.
* The proof also uses `REAL_ARITH` to apply arithmetic properties to the real numbers, and `REAL_RAT_REDUCE_CONV` to reduce rational expressions.

### Mathematical insight
The `STD_DODECAHEDRON` definition provides a precise specification of a dodecahedron in 3-dimensional space, which is a fundamental concept in geometry. The use of the golden ratio and its inverse in the definition reflects the unique properties of this polyhedron. The proof of the `golden_inverse` lemma demonstrates the importance of algebraic manipulations in establishing geometric properties.

### Dependencies
* `SQRT_POW_2`
* `REAL_FIELD`
* `REAL_ARITH`

### Porting notes
When porting this definition to another proof assistant, care should be taken to ensure that the algebraic manipulations and rewriting tactics are correctly translated. In particular, the use of `MP_TAC` and `CONV_TAC` may need to be adapted to the target system's tactic language. Additionally, the `REAL_RAT_REDUCE_CONV` tactic may need to be replaced with an equivalent tactic in the target system.

---

## STD_ICOSAHEDRON

### Name of formal statement
STD_ICOSAHEDRON

### Type of the formal statement
new_definition

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
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[])
```

### Informal statement
The `STD_ICOSAHEDRON` is defined as the convex hull of a set of twelve vectors in three-dimensional space. These vectors are defined using the `vector` function and involve arithmetic operations including addition, subtraction, multiplication, and division, as well as the square root of 5.

### Informal sketch
* The definition begins with the `let` keyword, introducing a new constant `STD_ICOSAHEDRON`.
* The `prove` keyword indicates that the following expression is to be proven or verified.
* The expression defines `std_icosahedron` as the convex hull of a specific set of twelve vectors.
* The `REWRITE_TAC` tactic is used with `std_icosahedron` to apply rewriting rules.
* The `CONV_TAC` tactic with `ONCE_DEPTH_CONV let_CONV` is applied to convert the expression.
* Further `REWRITE_TAC` applications are made with specific arithmetic rules, including `REAL_ARITH` rules for handling expressions involving `&1`, `&2`, and `sqrt(&5)`.
* The `CONV_TAC REAL_RAT_REDUCE_CONV` tactic is used for rational reduction, followed by a final `REWRITE_TAC` application.

### Mathematical insight
The `STD_ICOSAHEDRON` definition represents a geometric object, specifically a regular icosahedron, in a formal mathematical setting. This definition is crucial for geometric and topological studies, as it provides a precise, algebraic representation of the icosahedron's vertices. The use of `convex hull` indicates that the icosahedron is defined by the smallest convex set containing these points.

### Dependencies
#### Theorems and definitions
* `std_icosahedron`
* `REAL_ARITH`
* `convex hull`
* `vector`
#### Tactics
* `REWRITE_TAC`
* `CONV_TAC`
* `REAL_RAT_REDUCE_CONV`

### Porting notes
When translating this definition into another proof assistant, careful attention must be paid to the handling of arithmetic operations, especially those involving irrational numbers like `sqrt(&5)`. The `REAL_ARITH` rules and `REAL_RAT_REDUCE_CONV` tactic may need to be replaced with equivalent constructs in the target system. Additionally, the representation of vectors and the `convex hull` operation may vary between systems, requiring adjustments to the definition and proof strategy.

---

## COMPUTE_FACES_2

### Name of formal statement
COMPUTE_FACES_2

### Type of the formal statement
Theorem

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
         [SET_RULE `f x <= b /\ ~(f x = b) <=> x IN {x | f x <= b} /\ ~(x IN {x | f x = b})`] THEN
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
        REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE]];
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
          FIRST_XASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
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
          FIRST_XASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `x IN s ==> s SUBSET t ==> x IN t`)) THEN
          MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HALFSPACE_GT] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; real_gt; REAL_LT_LE]];
        ALL_TAC] THEN
      FIRST_XASSUM DISJ_CASES_TAC THENL
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
          VEC3_TAC]]])
```

### Informal statement
For all `f` and `s`, where `s` is a finite set of vectors in `ℝ³`, the following holds: `f` is a face of the convex hull of `s` with affine dimension 2 if and only if there exist `x`, `y`, and `z` in `s` such that the cross product of `(z - x)` and `(y - x)` is not the zero vector, and the dot product of this cross product with `x` equals some `b`, and for all `w` in `s`, the dot product of the cross product with `w` is less than or equal to `b`, or for all `w` in `s`, the dot product of the cross product with `w` is greater than or equal to `b`, and `f` is the convex hull of the intersection of `s` with the set of vectors whose dot product with the cross product equals `b`.

### Informal sketch
* The proof begins with the assumption that `f` is a face of the convex hull of `s` and `f` has affine dimension 2.
* It uses the `FACE_OF_CONVEX_HULL_SUBSET` theorem to find a subset `t` of `s` such that `f` is the convex hull of `t`.
* The `AFFINE_BASIS_EXISTS` theorem is applied to find an affine basis `u` of `t`.
* Since `f` has affine dimension 2, it follows that `u` has size 3.
* The proof then proceeds to show that there exist `x`, `y`, and `z` in `u` (and hence in `s`) such that the cross product of `(z - x)` and `(y - x)` is not the zero vector.
* It calculates `a` as this cross product and `b` as the dot product of `a` with `x`.
* The proof then splits into cases based on whether `s` is a subset of the set of vectors whose dot product with `a` equals `b`.
* In the case where `s` is a subset, it directly shows that `f` is the convex hull of the intersection of `s` with the set of vectors whose dot product with `a` equals `b`.
* In the other case, it uses the `CONVEX_HULL_UNION_NONEMPTY_EXPLICIT` theorem and further reasoning to establish the same conclusion.
* The converse direction of the theorem is also proven by showing that if the conditions involving `x`, `y`, `z`, `a`, and `b` are met, then `f` is indeed a face of the convex hull of `s` with affine dimension 2.

### Mathematical insight
This theorem provides a characterization of the faces of the convex hull of a finite set of points in `ℝ³`. It shows that a face of affine dimension 2 corresponds to a particular geometric configuration involving the points and their cross products. This is useful in understanding the structure of polyhedra and in algorithms for computing their faces.

### Dependencies
* `FACE_OF_CONVEX_HULL_SUBSET`
* `AFFINE_BASIS_EXISTS`
* `CONVEX_HULL_UNION_NONEMPTY_EXPLICIT`
* `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE`
* `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`
* `AFF_DIM_AFFINE_HULL`
* `AFF_DIM_SUBSET`
* `HULL_MINIMAL`
* `CONVEX_HULL_EQ`
* `CONVEX_HALFSPACE_LE`
* `CONVEX_HALFSPACE_GT`
* `REAL_ARITH`
* `VECTOR_ARITH`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of vector operations (e.g., cross product, dot product) and the representation of affine sets and their dimensions. Additionally, the use of `CONVEX_HULL_UNION_NONEMPTY_EXPLICIT` might require careful consideration due to its reliance on specific properties of convex hulls and unions.

---

## COMPUTE_FACES_2_STEP_1

### Name of formal statement
COMPUTE_FACES_2_STEP_1

### Type of the formal statement
Theorem

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
   `((z - x) cross (y - x)) dot y = ((z - x) cross (y - x)) dot x`])
```

### Informal statement
For all functions `f`, vectors `v`, sets `s` and `t` in 3-dimensional real space, the following statement holds: there exist `x`, `y`, and `z` in the set `v` inserted into `s`, such that `x`, `y`, and `z` satisfy certain conditions involving vector cross products, dot products, and set membership, if and only if either there exist `y` and `z` in `s` satisfying similar conditions with `v` as a reference point, or there exist `x`, `y`, and `z` all in `s` satisfying the conditions. The conditions include that the cross product of vectors formed by `x`, `y`, and `z` is not the zero vector, and that the dot product of this cross product with `x` (or `v` in the second case) is such that it is either less than or equal to, or greater than or equal to, the dot product of the cross product with any `w` in `t`. Furthermore, `f` must be the convex hull of the intersection of `t` with the set of points whose dot product with the cross product equals the dot product of `x` (or `v`) with the cross product.

### Informal sketch
* The proof involves showing an equivalence between three conditions involving vector operations and set membership.
* It starts by applying the `REPEAT GEN_TAC` and `REWRITE_TAC[IN_INSERT]` to set up the equivalence to be proven.
* Then, it uses `MATCH_MP_TAC` with a meson rule to apply a logical equivalence that helps in rearranging the conditions.
* The `CONV_TAC` and `REWRITE_TAC` with various vector and real number properties are used to simplify the expressions and conditions.
* Key steps involve using properties of vector cross and dot products, such as `VECTOR_SUB_REFL`, `CROSS_0`, `VECTOR_NEG_EQ_0`, `DOT_LNEG`, and `REAL_EQ_NEG2`, to simplify and manipulate the conditions.
* The proof also involves using `MAP_EVERY` with `SUBST1_TAC` and `VEC3_RULE` to apply specific vector rules and substitutions to simplify the expressions.
* The final steps involve rewriting the conditions using `DISJ_ACI` and applying another `VEC3_RULE` to conclude the proof.

### Mathematical insight
This theorem appears to be related to the computation of faces in a geometric or spatial context, possibly in the context of computational geometry or geometric algorithms. The use of vector cross and dot products, along with the concept of convex hulls, suggests that it is dealing with the spatial relationships and orientations of points and sets in 3D space. The theorem provides a way to equivalently express certain conditions involving these geometric concepts, which could be useful in proving other results or in the implementation of geometric algorithms.

### Dependencies
#### Theorems
* `IN_INSERT`
* `VECTOR_SUB_REFL`
* `CROSS_0`
* `VECTOR_NEG_EQ_0`
* `DOT_LNEG`
* `REAL_EQ_NEG2`
* `REAL_LE_NEG2`
* `real_ge`
* `DISJ_ACI`
#### Definitions
* `convex hull`
* `vec 0`
* `cross`
* `dot`
#### Other
* `MESON` rule
* `VEC3_RULE`

---

## COMPUTE_FACES_2_STEP_2

### Name of formal statement
COMPUTE_FACES_2_STEP_2

### Type of the formal statement
Theorem

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
              real_ge] THEN REWRITE_TAC[DISJ_ACI])
```

### Informal statement
For all functions `f`, vectors `u`, `v`, and sets `s` of vectors in 3D real space, the following statement holds: there exist vectors `y` and `z` in the set `u` inserted into `s` such that the cross product of `(z - v)` and `(y - v)` is not the zero vector, and the dot product of this cross product with `v` is `b`, and for all vectors `w` in `t`, the dot product of the cross product with `w` is less than or equal to `b` or greater than or equal to `b`, and `f` is the convex hull of the intersection of `t` with the set of vectors whose dot product with the cross product equals `b`, if and only if there exists a vector `z` in `s` such that the cross product of `(z - v)` and `(u - v)` is not the zero vector, and the dot product of this cross product with `v` is `b`, and for all vectors `w` in `t`, the dot product of the cross product with `w` is less than or equal to `b` or greater than or equal to `b`, and `f` is the convex hull of the intersection of `t` with the set of vectors whose dot product with the cross product equals `b`, or there exist vectors `y` and `z` in `s` such that the cross product of `(z - v)` and `(y - v)` is not the zero vector, and the dot product of this cross product with `v` is `b`, and for all vectors `w` in `t`, the dot product of the cross product with `w` is less than or equal to `b` or greater than or equal to `b`, and `f` is the convex hull of the intersection of `t` with the set of vectors whose dot product with the cross product equals `b`.

### Informal sketch
* The proof starts by applying `REPEAT GEN_TAC` to generalize the statement for all `f`, `u`, `v`, and `s`.
* It then uses `REWRITE_TAC[IN_INSERT]` to rewrite the membership in `u INSERT s`.
* The `MATCH_MP_TAC` tactic is applied with a `MESON` statement to transform the existential quantification.
* The proof involves several applications of `CONV_TAC` with `let_CONV` to simplify the `let` expressions and `REWRITE_TAC` with various rules (`CROSS_REFL`, `VECTOR_NEG_EQ_0`, `DOT_LNEG`, `REAL_EQ_NEG2`, `REAL_LE_NEG2`, `real_ge`, and `DISJ_ACI`) to simplify the vector operations and logical expressions.
* Key steps involve recognizing the symmetry and properties of cross and dot products, as well as the manipulation of convex hulls and set intersections.
* The use of `SUBST1_TAC` with a `VEC3_RULE` indicates a substitution based on vector properties.

### Mathematical insight
This theorem appears to be related to the computation of faces in a geometric or convex hull context, involving vectors and sets in 3D real space. The statement is about the equivalence of different conditions involving cross products, dot products, and convex hulls, which suggests it's a foundational result in computational geometry or a related field. The theorem's conditions and the proof's steps indicate a deep understanding of vector calculus and convex geometry principles.

### Dependencies
* `IN_INSERT`
* `CROSS_REFL`
* `VECTOR_NEG_EQ_0`
* `DOT_LNEG`
* `REAL_EQ_NEG2`
* `REAL_LE_NEG2`
* `real_ge`
* `DISJ_ACI`
* `VEC3_RULE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of vector operations (cross and dot products), the representation of convex hulls, and the manipulation of set intersections. Additionally, the use of `let` expressions and the specific tactics applied (like `CONV_TAC` and `MATCH_MP_TAC`) might require careful consideration due to differences in how these systems handle binders, equality, and propositional logic.

---

## COMPUTE_FACES_TAC

### Name of formal statement
COMPUTE_FACES_TAC

### Type of the formal statement
Theorem/Tactic

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
  REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI]
```

### Informal statement
The `COMPUTE_FACES_TAC` tactic proves that for any set `s`, element `x`, and predicate `P`, the intersection of the set `{x} ∪ s` and the set of elements satisfying `P` is equivalent to either `x ∪ (s ∩ {x | P x})` if `P x` holds, or `s ∩ {x | P x}` if `P x` does not hold. This equivalence is then used to simplify and rewrite various expressions involving set operations, vector calculations, and logical statements.

### Informal sketch
* The proof begins by establishing a `lemma` that describes the intersection of a set with a predicate-based set.
* It then applies various rewriting and simplification tactics to manipulate expressions involving sets, vectors, and logical operations.
* Key steps involve:
  + Simplifying set expressions using `COMPUTE_FACES_2`, `FINITE_INSERT`, and `FINITE_EMPTY`.
  + Rewriting vector operations with `VECTOR3_SUB_CONV`, `VECTOR3_CROSS_CONV`, and `VECTOR3_EQ_0_CONV`.
  + Applying `REAL_RAT5_LE_CONV` for real number comparisons.
  + Using `INSERT_AC` and `DISJ_ACI` for set and logical operation manipulations.
  + Repeatedly applying the established `lemma` and simplifying with `REWRITE_TAC` to reach the final conclusion.

### Mathematical insight
This tactic appears to be part of a larger development involving geometric or spatial reasoning, given the presence of vector operations and predicates that might define regions or shapes. The core idea is to provide a systematic way to compute or reason about the faces of objects, possibly in a constructive or computational geometry context. The tactic's complexity and the variety of rewriting and simplification steps suggest it is designed to handle intricate geometric or topological arguments.

### Dependencies
#### Theorems and definitions
* `COMPUTE_FACES_2`
* `FINITE_INSERT`
* `FINITE_EMPTY`
* `COMPUTE_FACES_2_STEP_1`
* `COMPUTE_FACES_2_STEP_2`
* `NOT_IN_EMPTY`
* `EXISTS_IN_INSERT`
* `FORALL_IN_INSERT`
* `VECTOR3_SUB_CONV`
* `VECTOR3_CROSS_CONV`
* `VECTOR3_EQ_0_CONV`
* `REAL_RAT5_LE_CONV`
* `INSERT_AC`
* `DISJ_ACI`
* `INTER_EMPTY`

### Porting notes
When translating this tactic into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles set operations, vector calculations, and logical manipulations. The tactic's reliance on specific rewriting and simplification steps may require adjustments due to differences in the target system's automation and tactic language. In particular, the use of `COND_CASES_TAC`, `ASM SET_TAC`, and various `CONV_TAC` and `REWRITE_TAC` applications will need to be carefully translated to ensure the same logical flow and computational behavior.

---

## TETRAHEDRON_FACETS

### Name of formal statement
TETRAHEDRON_FACETS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TETRAHEDRON_FACETS = time prove
 (`!f:real^3->bool.
        f face_of std_tetrahedron /\ aff_dim f = &2 <=>
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]} \/
        f = convex hull {vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`,
  GEN_TAC THEN REWRITE_TAC[std_tetrahedron] THEN COMPUTE_FACES_TAC)
```

### Informal statement
For all functions `f` from `real^3` to `bool`, `f` is a face of the standard tetrahedron and the affine dimension of `f` is 2 if and only if `f` is equal to the convex hull of one of the following sets of vectors: `{vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1]}`, `{vector[-- &1; -- &1; &1], vector[-- &1; &1; -- &1], vector[&1; &1; &1]}`, `{vector[-- &1; -- &1; &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`, or `{vector[-- &1; &1; -- &1], vector[&1; -- &1; -- &1], vector[&1; &1; &1]}`.

### Informal sketch
* The proof starts by assuming `f` is a face of the standard tetrahedron and the affine dimension of `f` is 2.
* It then uses the `GEN_TAC` tactic to generalize the assumption.
* The `REWRITE_TAC[std_tetrahedron]` tactic is applied to rewrite the standard tetrahedron using its definition.
* The `COMPUTE_FACES_TAC` tactic is used to compute the faces of the tetrahedron.
* The proof then proceeds to show that `f` must be equal to one of the specified convex hulls.
* The converse direction is also proved, showing that each of the specified convex hulls is a face of the standard tetrahedron with affine dimension 2.

### Mathematical insight
This theorem provides a characterization of the faces of the standard tetrahedron in 3-dimensional space. It shows that the faces of the tetrahedron are precisely the convex hulls of certain sets of vertices. This result is important in geometry and topology, as it provides a way to understand the structure of polyhedra and their faces.

### Dependencies
* `std_tetrahedron`
* `face_of`
* `aff_dim`
* `convex hull`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the definitions of `std_tetrahedron`, `face_of`, `aff_dim`, and `convex hull` are correctly translated. Additionally, the `GEN_TAC`, `REWRITE_TAC`, and `COMPUTE_FACES_TAC` tactics may need to be replaced with equivalent tactics in the target proof assistant.

---

## CUBE_FACETS

### Name of formal statement
CUBE_FACETS

### Type of the formal statement
Theorem

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
  GEN_TAC THEN REWRITE_TAC[std_cube] THEN COMPUTE_FACES_TAC)
```

### Informal statement
For all functions `f` from `real^3` to `bool`, `f` is a face of the standard cube and the affine dimension of `f` is 2 if and only if `f` is equal to the convex hull of one of the six sets of four vectors that define the faces of the cube.

### Informal sketch
* The proof starts by assuming `f` is a face of the standard cube and its affine dimension is 2.
* It then uses the `GEN_TAC` tactic to generalize the goal.
* The `REWRITE_TAC[std_cube]` tactic is applied to rewrite the standard cube definition.
* The `COMPUTE_FACES_TAC` tactic computes the faces of the cube.
* The proof then proceeds to show that `f` must be one of the six convex hulls of the specified sets of vectors.
* The converse direction is also proven, showing that each of these convex hulls is indeed a face of the standard cube with affine dimension 2.

### Mathematical insight
This theorem provides a characterization of the faces of the standard cube in terms of their affine dimension and convex hulls. It is a fundamental result in geometry and is useful for reasoning about geometric objects and their properties.

### Dependencies
* `std_cube`
* `face_of`
* `aff_dim`
* `convex hull`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the definitions of `std_cube`, `face_of`, and `aff_dim` are properly translated. Additionally, the `COMPUTE_FACES_TAC` tactic may need to be reimplemented or replaced with a similar tactic in the target proof assistant.

---

## OCTAHEDRON_FACETS

### Name of formal statement
OCTAHEDRON_FACETS

### Type of the formal statement
Theorem

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
  GEN_TAC THEN REWRITE_TAC[std_octahedron] THEN COMPUTE_FACES_TAC)
```

### Informal statement
For all functions `f` from `real^3` to `bool`, `f` is a face of the standard octahedron and the affine dimension of `f` is 2 if and only if `f` is equal to the convex hull of one of the following sets of vectors: 
{ `vector[-- &1; &0; &0]`, `vector[&0; -- &1; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[-- &1; &0; &0]`, `vector[&0; -- &1; &0]`, `vector[&0; &0; &1]` },
{ `vector[-- &1; &0; &0]`, `vector[&0; &1; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[-- &1; &0; &0]`, `vector[&0; &1; &0]`, `vector[&0; &0; &1]` },
{ `vector[&1; &0; &0]`, `vector[&0; -- &1; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[&1; &0; &0]`, `vector[&0; -- &1; &0]`, `vector[&0; &0; &1]` },
{ `vector[&1; &0; &0]`, `vector[&0; &1; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[&1; &0; &0]`, `vector[&0; &1; &0]`, `vector[&0; &0; &1]` }.

### Informal sketch
* The proof starts with a generalization using `GEN_TAC`.
* It then applies `REWRITE_TAC` with the definition of `std_octahedron` to rewrite the goal.
* The `COMPUTE_FACES_TAC` tactic is used to compute the faces of the standard octahedron.
* The key idea is to identify the faces of the octahedron and show that they are exactly the convex hulls of the specified sets of vectors.
* The proof involves showing that each face of the octahedron satisfies the condition `aff_dim f = &2`, and that each convex hull of the specified sets of vectors is a face of the octahedron.

### Mathematical insight
This theorem provides a characterization of the faces of the standard octahedron in terms of their affine dimension and convex hulls of specific sets of vectors. The octahedron is a fundamental geometric object, and understanding its faces is crucial in various areas of mathematics and computer science, such as geometry, topology, and computer-aided design.

### Dependencies
* `std_octahedron`
* `face_of`
* `aff_dim`
* `convex hull`

### Porting notes
When porting this theorem to other proof assistants, pay attention to the handling of binders and the definition of the `std_octahedron`. The `COMPUTE_FACES_TAC` tactic may need to be replaced with a similar tactic or a manual proof step. Additionally, the `REWRITE_TAC` tactic may need to be adjusted to accommodate differences in the rewriting mechanisms of the target proof assistant.

---

## ICOSAHEDRON_FACETS

### Name of formal statement
ICOSAHEDRON_FACETS

### Type of the formal statement
Theorem

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
  GEN_TAC THEN REWRITE_TAC[STD_ICOSAHEDRON] THEN COMPUTE_FACES_TAC)
```

### Informal statement
For all functions `f` from `real^3` to `bool`, `f` is a face of the standard icosahedron and has affine dimension 2 if and only if `f` is equal to the convex hull of one of the specified sets of vectors.

### Informal sketch
* The proof begins by assuming `f` is a face of the standard icosahedron and has affine dimension 2.
* It then uses the `GEN_TAC` and `REWRITE_TAC[STD_ICOSAHEDRON]` tactics to rewrite the standard icosahedron in terms of its definition.
* The `COMPUTE_FACES_TAC` tactic is then applied to compute the faces of the icosahedron.
* The proof then proceeds by checking each possible face of the icosahedron and verifying that it satisfies the condition.
* The converse direction is also proved by showing that each of the specified convex hulls is a face of the icosahedron with affine dimension 2.

### Mathematical insight
This theorem provides a characterization of the faces of the standard icosahedron in terms of their convex hulls. The icosahedron is a regular polyhedron with 20 triangular faces, and this theorem provides a way to identify these faces using their geometric properties.

### Dependencies
* `STD_ICOSAHEDRON`
* `face_of`
* `aff_dim`
* `convex hull`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `STD_ICOSAHEDRON` definition is correctly translated, as well as the `face_of` and `aff_dim` functions. The `COMPUTE_FACES_TAC` tactic may need to be replaced with a similar tactic or a manual proof. Additionally, the convex hull computation may require a different approach depending on the proof assistant's capabilities.

---

## DODECAHEDRON_FACETS

### Name of formal statement
DODECAHEDRON_FACETS

### Type of the formal statement
Theorem

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
        f = convex hull {vector[&1 / &2 + &1 / &2 * sqrt(&5); &0; &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&1; -- &1; -- &1], vector[&1; &1; -- &1], vector[&0; -- &1 / &2 + &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)], vector[&0; &1 / &2 + -- &1 / &2 * sqrt(&5); -- &1 / &2 + -- &1 / &2 * sqrt(&5)]}`)
  GEN_TAC THEN REWRITE_TAC[STD_DODECAHEDRON] THEN COMPUTE_FACES_TAC
```

### Informal statement
For all functions `f` from `real^3` to `bool`, `f` is a face of the standard dodecahedron and the affine dimension of `f` is 2 if and only if `f` is equal to the convex hull of one of the sets of vectors listed.

### Informal sketch
* The theorem `DODECAHEDRON_FACETS` characterizes the faces of a standard dodecahedron.
* It states that a function `f` from `real^3` to `bool` is a face of the standard dodecahedron with affine dimension 2 if and only if `f` is the convex hull of one of the specific sets of vectors provided in the statement.
* The proof involves using the `GEN_TAC` tactic to introduce a generic function `f`, followed by `REWRITE_TAC` with `STD_DODECAHEDRON` to apply the definition of the standard dodecahedron.
* Then, `COMPUTE_FACES_TAC` is applied to compute the faces of the dodecahedron.

### Mathematical insight
This theorem provides a precise characterization of the faces of a standard dodecahedron, which is a fundamental concept in geometry. The dodecahedron is a regular polyhedron with 12 pentagonal faces, and understanding its structure is crucial in various mathematical and scientific contexts.

### Dependencies
* `STD_DODECAHEDRON`
* `face_of`
* `aff_dim`
* `convex hull`

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to the representation of the standard dodecahedron and the computation of its faces. The `COMPUTE_FACES_TAC` tactic may need to be replaced with an equivalent tactic or a custom implementation in the target proof assistant. Additionally, the handling of convex hulls and affine dimensions may require careful consideration to ensure compatibility with the target system.

---

## COPLANAR_HYPERPLANE_RULE

### Name of formal statement
COPLANAR_HYPERPLANE_RULE

### Type of the formal statement
Theorem

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
      GEN_REWRITE_CONV DEPTH_CONV [AND_CLAUSES]) ptm)
```

### Informal statement
Given a set `s` of points in 3-dimensional space, the `COPLANAR_HYPERPLANE_RULE` theorem generates a hyperplane that contains all points in `s`. The theorem assumes that `s` has at least three points. It first computes the normal vector `n` to the hyperplane by considering all possible combinations of three points in `s` and checking if they are coplanar. Once `n` is found, it computes the distance `d` from the origin to the hyperplane along `n`. The theorem then states that for all points `x` in `s`, the dot product of `x` and `n` equals `d`, which is the equation of the hyperplane.

### Informal sketch
* The proof starts by generating all possible subsets of three points from the given set `s`.
* For each subset of three points, it computes the normal vector `n` to the plane defined by these points using the cross product of two vectors formed by subtracting pairs of points.
* The `check_normal` function checks if the computed normal vector `n` is not the zero vector, ensuring that the points are indeed coplanar.
* Once a valid normal vector `n` is found, the proof computes the distance `d` from the origin to the hyperplane by taking the dot product of `n` with one of the points in `s`.
* The final step involves constructing the equation of the hyperplane in the form `n dot x = d` for all `x` in `s`, which is then simplified and proved using various rewrite rules and conversions.

### Mathematical insight
The `COPLANAR_HYPERPLANE_RULE` theorem is important because it provides a way to define a hyperplane that contains a given set of coplanar points in 3-dimensional space. This is a fundamental construction in geometry and has numerous applications in computer graphics, robotics, and geometric modeling. The theorem relies on the concept of normal vectors and the dot product to define the equation of the hyperplane, which is a standard technique in linear algebra and geometry.

### Dependencies
* `VECTOR3_SUB_CONV`
* `VECTOR3_CROSS_CONV`
* `VECTOR3_DOT_CONV`
* `FORALL_IN_INSERT`
* `NOT_IN_EMPTY`
* `AND_CLAUSES`
* `REAL_RAT5_EQ_CONV`
* `GEN_REWRITE_CONV`
* `DEPTH_CONV`
* `LAND_CONV`
* `BINOP_CONV`
* `EQT_ELIM`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of vector operations, such as the cross product and dot product, as well as the representation of points and hyperplanes. Additionally, the use of `tryfind` and `failwith` may need to be adapted to the target system's exception handling mechanisms. The proof's reliance on various rewrite rules and conversions may also require careful translation to ensure that the resulting proof is valid and efficient in the target system.

---

## COMPUTE_FACES_1

### Name of formal statement
COMPUTE_FACES_1

### Type of the formal statement
Theorem

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
         [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ASM_SET_TAC[]];
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
         [SET_RULE `f x <= b /\ ~(f x = b) <=> x IN {x | f x <= b} /\ ~(x IN {x | f x = b})`] THEN
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
        REWRITE_TAC[CONVEX_HULL_EQ; CONVEX_HYPERPLANE]];
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
          FIRST_X-AssUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
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
          ASM_SIMP_TAC[SUBSET; IN_DIFF; IN_ELIM_THM; real_gt; REAL_LT_LE]];
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
For all sets $s$ of points in $\mathbb{R}^3$, vectors $n$, and real numbers $d$, if for all points $x$ in $s$, the dot product of $n$ and $x$ equals $d$, and if $s$ is finite and $n$ is not the zero vector, then for all faces $f$ of the convex hull of $s$ with affine dimension $1$, there exist points $x$ and $y$ in $s$ such that the cross product of $n$ and $y-x$ is not the zero vector, and the dot product of this cross product with $x$ equals some real number $b$, and for all points $w$ in $s$, the dot product of the cross product with $w$ is less than or equal to $b$, or for all points $w$ in $s$, the dot product of the cross product with $w$ is greater than or equal to $b$, and $f$ is the convex hull of the intersection of $s$ with the set of points whose dot product with the cross product equals $b$.

### Informal sketch
* The proof starts by assuming the premises: $s$ is finite, $n$ is not the zero vector, and for all $x$ in $s$, $n \cdot x = d$.
* It then uses the `FACE_OF_CONVEX_HULL_SUBSET` theorem to find a subset $t$ of $s$ such that $f$ is the convex hull of $t$.
* The proof then applies the `AFFINE_BASIS_EXISTS` theorem to find an affine basis $u$ for $t$.
* Since $f$ has affine dimension $1$, the size of $u$ must be $2$.
* The proof then chooses two points $x$ and $y$ from $u$ and computes the cross product $a = n \times (y - x)$.
* It then computes the dot product $b = a \cdot x$.
* The proof then shows that for all points $w$ in $s$, either $a \cdot w \leq b$ or $a \cdot w \geq b$.
* The proof then uses the `CONVEX_HULL_EQ` theorem to show that $f$ is the convex hull of the intersection of $s$ with the set of points whose dot product with $a$ equals $b$.
* The proof also uses the `AFF_DIM_AFFINE_INTER_HYPERPLANE` theorem to show that the affine dimension of the intersection of $s$ with the set of points whose dot product with $a$ equals $b$ is less than or equal to $1$.
* The proof concludes by showing that $f$ is the convex hull of this intersection.

### Mathematical insight
This theorem provides a way to compute the faces of the convex hull of a finite set of points in $\mathbb{R}^3$, assuming that the set lies in a hyperplane. The theorem shows that each face of the convex hull can be represented as the convex hull of the intersection of the set with a hyperplane.

### Dependencies
* `FACE_OF_CONVEX_HULL_SUBSET`
* `AFFINE_BASIS_EXISTS`
* `CONVEX_HULL_EQ`
* `AFF_DIM_AFFINE_INTER_HYPERPLANE`
* `HULL_MINIMAL`
* `CONVEX_HYPERPLANE`
* `SUBSET_TRANS`
* `INSERT_SUBSET`
* `EMPTY_SUBSET`
* `IN_ELIM_THM`
* `REAL_LT_IMP_NE`
* `CONNECTED_IVT_HYPERPLANE`
* `ENDS_IN_SEGMENT`
* `CONNECTED_SEGMENT`
* `REAL_LT_IMP_LE`
* `CONJ_ASSOC`
* `RIGHT_EXISTS_AND_THM`
* `UNWIND_THM2`
* `DOT_RADD`
* `DOT_RMUL`
* `CONJ_ASSOC`
* `INT_LE_TRANS`
* `AFF_DIM_2`
* `CROSS_0`
* `VECTOR_SUB_REFL`
* `INT_LE_REFL`
* `AFF_DIM_SUBSET`
* `INSERT_SUBSET`
* `EMPTY_SUBSET`
* `HULL_INC`
* `IN_INTER`
* `IN_ELIM_THM`
* `REAL_EQ_ADD_LCANCEL_0`
* `DOT_EQ_0`
* `EXPAND_TAC`
* `VEC3_TAC`

### Porting notes
When porting this theorem to another proof assistant, note that the `CONVEX_HULL_EQ` theorem may need to be replaced with a similar theorem that is specific to the target proof assistant. Additionally, the `AFF_DIM_AFFINE_INTER_HYPERPLANE` theorem may need to be replaced with a similar theorem that is specific to the target proof assistant. The `HULL_MINIMAL` theorem may also need to be replaced with a similar theorem that is specific to the target proof assistant. The `SUBSET_TRANS` and `INSERT_SUBSET` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `IN_ELIM_THM` and `REAL_LT_IMP_NE` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `CONNECTED_IVT_HYPERPLANE` theorem may need to be replaced with a similar theorem that is specific to the target proof assistant. The `ENDS_IN_SEGMENT` and `CONNECTED_SEGMENT` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `REAL_LT_IMP_LE` theorem is likely to be available in most proof assistants, but may need to be renamed or rephrased. The `CONJ_ASSOC` and `RIGHT_EXISTS_AND_THM` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `UNWIND_THM2` theorem may need to be replaced with a similar theorem that is specific to the target proof assistant. The `DOT_RADD` and `DOT_RMUL` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `CONJ_ASSOC` theorem is likely to be available in most proof assistants, but may need to be renamed or rephrased. The `INT_LE_TRANS` theorem is likely to be available in most proof assistants, but may need to be renamed or rephrased. The `AFF_DIM_2` theorem is likely to be available in most proof assistants, but may need to be renamed or rephrased. The `CROSS_0` and `VECTOR_SUB_REFL` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `INT_LE_REFL` theorem is likely to be available in most proof assistants, but may need to be renamed or rephrased. The `AFF_DIM_SUBSET` theorem is likely to be available in most proof assistants, but may need to be renamed or rephrased. The `INSERT_SUBSET` and `EMPTY_SUBSET` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `HULL_INC` theorem may need to be replaced with a similar theorem that is specific to the target proof assistant. The `IN_INTER` and `IN_ELIM_THM` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `REAL_EQ_ADD_LCANCEL_0` and `DOT_EQ_0` theorems are likely to be available in most proof assistants, but may need to be renamed or rephrased. The `EXPAND_TAC` and `VEC3_TAC` theorems may need to be replaced with similar theorems that are specific to the target proof assistant.

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
Given a term `tm` representing a coplanar set, `COMPUTE_EDGES_CONV` returns an exhaustive edge case theorem. The theorem is derived by first proving a lemma about set intersection and then applying a series of rewriting and convolution rules to `COMPUTE_FACES_1` and `COPLANAR_HYPERPLANE_RULE tm`. The resulting theorem is then further transformed using various rewriting and convolution rules to obtain the final edge case theorem.

### Informal sketch
* Prove a lemma about set intersection: `(x INSERT s) INTER {x | P x} = if P x then x INSERT (s INTER {x | P x}) else s INTER {x | P x}`
* Apply `MATCH_MP` with `COMPUTE_FACES_1` and `COPLANAR_HYPERPLANE_RULE tm` to obtain `th1`
* Apply `CONV_RULE` with `LAND_CONV` and other rewriting rules to `th1` to obtain `th2`
* Apply `BINDER_CONV` with `RAND_CONV` and various rewriting rules to `th2` to obtain the final edge case theorem
* Key HOL Light terms used include `COMPUTE_FACES_1`, `COPLANAR_HYPERPLANE_RULE`, `MATCH_MP`, `CONV_RULE`, `BINDER_CONV`, and `RAND_CONV`

### Mathematical insight
The `COMPUTE_EDGES_CONV` theorem is important for deriving exhaustive edge cases for coplanar sets. The theorem is constructed by applying a series of rewriting and convolution rules to existing theorems, demonstrating a key aspect of formal proof development: the derivation of new results from existing ones through logical manipulation.

### Dependencies
* Theorems:
	+ `COMPUTE_FACES_1`
	+ `COPLANAR_HYPERPLANE_RULE`
* Definitions:
	+ `FINITE_INSERT`
	+ `FINITE_EMPTY`
	+ `VECTOR3_EQ_0`
	+ `NOT_CLAUSES`
	+ `AND_CLAUSES`
	+ `RIGHT_EXISTS_AND_THM`
	+ `EXISTS_IN_INSERT`
	+ `NOT_IN_EMPTY`
	+ `FORALL_IN_INSERT`
	+ `VECTOR3_SUB`
	+ `VECTOR3_CROSS`
	+ `let`
	+ `VECTOR3_EQ_0`
	+ `real_ge`
	+ `VECTOR3_DOT`
	+ `REAL_RAT5_LE`
	+ `INSERT_AC`
	+ `DISJ_ACI`
	+ `INTER_EMPTY`
* Inductive rules: None

### Porting notes
When porting this theorem to other proof assistants, note that the `COMPUTE_EDGES_CONV` function is defined using a combination of rewriting and convolution rules. The `MATCH_MP` and `CONV_RULE` tactics may need to be replaced with equivalent tactics in the target proof assistant. Additionally, the `BINDER_CONV` and `RAND_CONV` tactics may require special handling due to their use of binders and rewriting rules. It is recommended to carefully examine the HOL Light code and identify the key mathematical insights and dependencies before attempting to port the theorem.

---

## CARD_EQ_LEMMA

### Name of formal statement
CARD_EQ_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CARD_EQ_LEMMA = prove
 (`!x s n. 0 < n /\ ~(x IN s) /\ s HAS_SIZE (n - 1)
           ==> (x INSERT s) HAS_SIZE n`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT] THEN ASM_ARITH_TAC)
```

### Informal statement
For all `x`, `s`, and `n`, if `n` is greater than 0, `x` is not an element of `s`, and `s` has a size of `n-1`, then the set resulting from inserting `x` into `s` has a size of `n`.

### Informal sketch
* Start with the assumption that `n` is greater than 0, `x` is not in `s`, and `s` has `n-1` elements.
* Use the definition of `HAS_SIZE` to relate the size of `s` and the size of `x INSERT s`.
* Apply `CARD_CLAUSES` and `FINITE_INSERT` to simplify the expression for the size of `x INSERT s`.
* Perform arithmetic simplification to show that `x INSERT s` has `n` elements.

### Mathematical insight
This theorem provides a way to reason about the size of sets when elements are added. It is a fundamental property of finite sets and is used in various proofs involving set sizes and combinatorics. The theorem is important because it allows us to conclude that adding a new element to a set increases its size by one, provided the element is not already in the set.

### Dependencies
* `HAS_SIZE`
* `CARD_CLAUSES`
* `FINITE_INSERT`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of set sizes and the `INSERT` operation. Some systems may have different notations or tactics for working with sets and sizes. Additionally, the `ASM_SIMP_TAC` and `ASM_ARITH_TAC` tactics may need to be replaced with equivalent tactics in the target system.

---

## EDGES_PER_FACE_TAC

### Name of formal statement
EDGES_PER_FACE_TAC

### Type of the formal statement
Theorem/Tactic

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
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES]
```

### Informal statement
For a given `th` (presumably a theorem or hypothesis), `EDGES_PER_FACE_TAC` is a tactic that proves a statement about the cardinality of edges of a face `f` in a 3D real space. Specifically, it involves proving that the number of edges of `f` is equal to the cardinality of the set of edges `e` such that `e` is a face of `f` and the affine dimension of `e` is 1. This involves several steps including using transitivity of equality, existence of a set with specific properties, and applying various rewrite rules and theorems related to sets, faces, and dimensions.

### Informal sketch
* The tactic starts by applying `REPEAT STRIP_TAC` to strip away any universal quantifiers and then applies `MATCH_MP_TAC EQ_TRANS` to set up an equality proof.
* It then uses `EXISTS_TAC` to assert the existence of a set of edges `e` that are faces of `f` with affine dimension 1 and applies `CONJ_TAC` to split the goal into two parts.
* The first part involves applying `AP_TERM_TAC`, `GEN_REWRITE_TAC`, and `ASM_MESON_TAC` with specific theorems (`FACE_OF_FACE`, `FACE_OF_TRANS`, `FACE_OF_IMP_SUBSET`) to reason about the properties of faces.
* The second part involves applying `MP_TAC` with a specific instantiation, followed by `DISCH_THEN` and `REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC` to handle disjunctions and substitutions.
* Further steps involve applying various rewrite rules and theorems (`COMPUTE_EDGES_CONV`, `SET_RULE`, `GSYM IN_INSERT`, `GSYM SEGMENT_CONVEX_HULL`) to simplify and transform the goal.
* The tactic also applies `MATCH_MP_TAC` with a lemma about cardinality (`CARD_EQ_LEMMA`) and uses `CONV_TAC` with specific conversions (`NUM_REDUCE_CONV`, `VECTOR3_SUB_CONV`, `VECTOR3_EQ_0_CONV`) to finalize the proof.

### Mathematical insight
This tactic appears to be designed to reason about geometric objects (faces and edges) in a 3D real space, leveraging properties of sets, affine dimensions, and cardinalities. The key idea is to establish a relationship between the number of edges of a face and the cardinality of a set of edges that satisfy certain geometric conditions. This is likely part of a larger development in geometric or computational geometry, where such relationships are crucial for proving theorems about geometric objects and their transformations.

### Dependencies
- Theorems:
  - `FACE_OF_FACE`
  - `FACE_OF_TRANS`
  - `FACE_OF_IMP_SUBSET`
  - `HAS_SIZE`
  - `CARD_EQ_LEMMA`
- Definitions:
  - `face_of`
  - `aff_dim`
  - `COMPUTE_EDGES_CONV`
- Tactics and functions:
  - `REPEAT STRIP_TAC`
  - `MATCH_MP_TAC`
  - `EXISTS_TAC`
  - `CONJ_TAC`
  - `AP_TERM_TAC`
  - `GEN_REWRITE_TAC`
  - `ASM_MESON_TAC`
  - `MP_TAC`
  - `DISCH_THEN`
  - `REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC`
  - `CONV_TAC`
  - `PURE_ONCE_REWRITE_TAC`
  - `MATCH_MP_TAC` with `SET_RULE` and `CARD_EQ_LEMMA`

---

## TETRAHEDRON_EDGES_PER_FACE

### Name of formal statement
TETRAHEDRON_EDGES_PER_FACE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TETRAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_tetrahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_tetrahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC TETRAHEDRON_FACETS);;
```

### Informal statement
For all faces `f` of the standard tetrahedron, if `f` has affine dimension 2, then the cardinality of the set of edges `e` of the standard tetrahedron with affine dimension 1 that are subsets of `f` is equal to 3.

### Informal sketch
* The proof starts with a universal quantification over all faces `f` of the `std_tetrahedron`.
* It assumes that `f` is a face of the `std_tetrahedron` and has an affine dimension of 2.
* The goal is to show that the number of edges `e` of the `std_tetrahedron` with affine dimension 1 that are subsets of `f` is exactly 3.
* The `EDGES_PER_FACE_TAC` tactic is used in conjunction with the `TETRAHEDRON_FACETS` to establish this result, likely by analyzing the geometric properties of a tetrahedron's faces and edges.

### Mathematical insight
This theorem provides a fundamental property of the standard tetrahedron, specifically regarding the number of edges per face. It is crucial for understanding the geometric and topological structure of tetrahedrons, which are basic building blocks in geometry and topology. The theorem's importance lies in its contribution to the formal verification of geometric properties, which is essential in various fields like computer-aided design, computational geometry, and mathematical proofs.

### Dependencies
* `std_tetrahedron`
* `face_of`
* `aff_dim`
* `TETRAHEDRON_FACETS`
* `EDGES_PER_FACE_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be given to the representation of geometric objects (like the `std_tetrahedron`), the definition of `face_of` and `aff_dim`, and the tactic `EDGES_PER_FACE_TAC`. The porting process may require adapting these components to fit the target system's syntax and semantic framework, potentially involving differences in how binders, quantifiers, and geometric primitives are handled.

---

## CUBE_EDGES_PER_FACE

### Name of formal statement
CUBE_EDGES_PER_FACE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CUBE_EDGES_PER_FACE = prove
 (`!f. f face_of std_cube /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 4`,
  EDGES_PER_FACE_TAC CUBE_FACETS);;
```

### Informal statement
For all faces `f` of the standard cube, if `f` has affine dimension 2, then the cardinality of the set of edges `e` of the standard cube with affine dimension 1, such that `e` is a subset of `f`, is equal to 4.

### Informal sketch
* The proof starts by considering an arbitrary face `f` of the standard cube `std_cube`.
* It then assumes that the affine dimension of `f` is 2, which implies that `f` is a 2-dimensional face.
* The goal is to show that the number of edges `e` of `std_cube` with affine dimension 1, such that `e` is a subset of `f`, is equal to 4.
* The `EDGES_PER_FACE_TAC` tactic is used to prove this statement, which likely involves analyzing the structure of the cube and its faces.

### Mathematical insight
This theorem provides insight into the geometric structure of the standard cube, specifically the relationship between its faces and edges. It shows that each 2-dimensional face of the cube has exactly 4 edges, which is a fundamental property of the cube.

### Dependencies
* `std_cube`
* `face_of`
* `aff_dim`
* `CUBE_FACETS`
* `EDGES_PER_FACE_TAC`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of affine dimensions and subset relationships. The `EDGES_PER_FACE_TAC` tactic may need to be reimplemented or replaced with a similar tactic in the target system. Additionally, the representation of the standard cube and its faces may differ between systems, requiring adjustments to the proof.

---

## OCTAHEDRON_EDGES_PER_FACE

### Name of formal statement
OCTAHEDRON_EDGES_PER_FACE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OCTAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_octahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC OCTAHEDRON_FACETS);;
```

### Informal statement
For all faces `f` of the standard octahedron, if `f` has affine dimension 2, then the number of edges `e` of the standard octahedron with affine dimension 1 that are subsets of `f` is 3.

### Informal sketch
* The proof involves considering each face `f` of the `std_octahedron` and assuming it has an affine dimension of 2.
* It then examines the edges `e` of the `std_octahedron` that are subsets of `f` and have an affine dimension of 1.
* The `EDGES_PER_FACE_TAC` tactic is applied with `OCTAHEDRON_FACETS` to establish that there are exactly 3 such edges for each face `f`.
* The key insight is recognizing the geometric structure of the octahedron and how its faces and edges relate, which is encapsulated in the `std_octahedron` and `face_of` definitions.

### Mathematical insight
This theorem is important because it characterizes a fundamental property of the octahedron's geometry, specifically how many edges bound each face. This kind of property is crucial in geometric and topological studies, as it helps in understanding the structure and behavior of polyhedra.

### Dependencies
* `std_octahedron`
* `face_of`
* `aff_dim`
* `EDGES_PER_FACE_TAC`
* `OCTAHEDRON_FACETS`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles geometric definitions and properties, especially the representation of the octahedron and its faces and edges. The `EDGES_PER_FACE_TAC` tactic and its interaction with `OCTAHEDRON_FACETS` might need to be reinterpreted or reimplemented in terms of the target system's tactics and theorems.

---

## DODECAHEDRON_EDGES_PER_FACE

### Name of formal statement
DODECAHEDRON_EDGES_PER_FACE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DODECAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_dodecahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_dodecahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 5`,
  EDGES_PER_FACE_TAC DODECAHEDRON_FACETS);;
```

### Informal statement
For all faces `f` of the standard dodecahedron, if `f` has affine dimension 2, then the cardinality of the set of edges `e` of the standard dodecahedron with affine dimension 1 that are subsets of `f` is equal to 5.

### Informal sketch
* The proof starts by assuming a face `f` of the standard dodecahedron with affine dimension 2.
* It then considers the set of edges `e` of the standard dodecahedron with affine dimension 1 that are subsets of `f`.
* The `EDGES_PER_FACE_TAC` tactic is applied to `DODECAHEDRON_FACETS` to derive the conclusion that the cardinality of this set of edges is 5.
* This involves understanding the geometric properties of the dodecahedron and its facets, as well as the relationships between faces and edges.

### Mathematical insight
This theorem provides a fundamental property of the standard dodecahedron, specifically that each of its faces has exactly 5 edges. This is a key aspect of the geometry of the dodecahedron and is likely used in various geometric and topological arguments.

### Dependencies
* `std_dodecahedron`
* `face_of`
* `aff_dim`
* `DODECAHEDRON_FACETS`
* `EDGES_PER_FACE_TAC`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the geometric definitions and properties are translated correctly. In particular, the `EDGES_PER_FACE_TAC` tactic may need to be reimplemented or replaced with an equivalent tactic in the target system. Additionally, the `aff_dim` function and `face_of` predicate may require special attention to ensure that they are defined and used consistently with the original HOL Light code.

---

## ICOSAHEDRON_EDGES_PER_FACE

### Name of formal statement
ICOSAHEDRON_EDGES_PER_FACE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ICOSAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_icosahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC ICOSAHEDRON_FACETS);;
```

### Informal statement
For all faces `f` of the standard icosahedron, if `f` has affine dimension 2, then the number of edges `e` of the standard icosahedron with affine dimension 1 that are subsets of `f` is 3.

### Informal sketch
* The theorem starts by quantifying over all faces `f` of the `std_icosahedron`.
* It then restricts to faces `f` with `aff_dim(f) = &2`, ensuring they are 2-dimensional.
* For each such face `f`, it considers the set of edges `e` that are both faces of the `std_icosahedron` with `aff_dim(e) = &1` (making them 1-dimensional) and subsets of `f`.
* The theorem asserts that the cardinality of this set of edges `e` is exactly 3 for any face `f` satisfying the conditions.
* The proof involves the `EDGES_PER_FACE_TAC` tactic, which is likely tailored to reason about the edges per face in the context of the `std_icosahedron`, leveraging the `ICOSAHEDRON_FACETS` to establish the result.

### Mathematical insight
This theorem provides a fundamental property of the standard icosahedron, specifically concerning the number of edges that bound each of its faces. The icosahedron, being a regular polyhedron, has all its faces as triangles, which by definition have three edges. This theorem formalizes this geometric intuition in the context of the `std_icosahedron`.

### Dependencies
- `std_icosahedron`
- `face_of`
- `aff_dim`
- `ICOSAHEDRON_FACETS`
- `EDGES_PER_FACE_TAC`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the representation of the standard icosahedron and its facets, as well as the definition of `face_of` and `aff_dim`. The `EDGES_PER_FACE_TAC` tactic is likely specific to the HOL Light environment, so the corresponding proof strategy in the target system will need to be identified or developed. This might involve leveraging geometric or combinatorial libraries and tactics available in the target proof assistant.

---

## POLYTOPE_3D_LEMMA

### Name of formal statement
POLYTOPE_3D_LEMMA

### Type of the formal statement
Theorem

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
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN INT_ARITH_TAC])
```

### Informal statement
Let `a` be the cross product of `(z - x)` and `(y - x)`. If `a` is not the zero vector and there exists a `w` in `s` such that the dot product of `a` and `w` is not equal to the dot product of `a` and `x`, then the affine dimension of the convex hull of `x`, `y`, `z`, and `s` is 3.

### Informal sketch
* The proof starts by assuming the conditions on `a` and `w`.
* It then applies various mathematical properties and theorems, such as `AFF_DIM_CONVEX_HULL`, `INT_LE_TRANS`, and `AFF_DIM_SUBSET`, to establish relationships between the affine dimensions of different sets.
* The proof considers two cases based on the condition `w IN {w:real^3 | a dot w = a dot x}` and uses `MATCH_MP_TAC` and `SUBGOAL_THEN` to apply relevant theorems and rules.
* Key steps involve showing that `a` is not the zero vector, expanding `a` using `EXPAND_TAC "a"`, and applying `VEC3_TAC` to reason about vectors in 3D space.
* The proof also uses `COND_CASES_TAC` to consider different scenarios and `ASM_REWRITE_TAC` to apply various definitions and properties.

### Mathematical insight
This theorem provides a condition under which the convex hull of a set of points in 3D space has full dimension, i.e., the dimension is 3. The condition involves the existence of a non-zero cross product and a point `w` in the set `s` that satisfies a certain dot product condition. This result is important in geometry and can be used to show that certain polytopes, such as the Platonic solids, are full-dimensional.

### Dependencies
* Theorems:
	+ `AFF_DIM_CONVEX_HULL`
	+ `INT_LE_TRANS`
	+ `AFF_DIM_SUBSET`
	+ `HULL_MINIMAL`
	+ `AFFINE_HYPERPLANE`
	+ `AFF_DIM_AFFINE_INDEPENDENT`
* Definitions:
	+ `aff_dim`
	+ `convex hull`
	+ `INSERT`
	+ `cross`
	+ `dot`
* Rules:
	+ `MATCH_MP_TAC`
	+ `SUBGOAL_THEN`
	+ `COND_CASES_TAC`
	+ `ASM_REWRITE_TAC`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of vectors, dot products, and cross products. The `VEC3_TAC` and `EXPAND_TAC "a"` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `MATCH_MP_TAC` and `SUBGOAL_THEN` tactics may require different syntax or strategic application in other systems.

---

## POLYTOPE_FULLDIM_TAC

### Name of formal statement
POLYTOPE_FULLDIM_TAC

### Type of the formal statement
Theorem/Tactic

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
    REWRITE_TAC[]]
```

### Informal statement
This tactic proves a statement about polytopes by first applying the `POLYTOPE_3D_LEMMA`, then performing a series of conversions using `VECTOR3_SUB_CONV`, `VECTOR3_CROSS_CONV`, and `let_CONV`. It then splits into two branches: one proving a vector equation using `VECTOR3_EQ_0_CONV` and the other involving dot products and existential statements, utilizing `VECTOR3_DOT_CONV`, `EXISTS_IN_INSERT`, `NOT_IN_EMPTY`, and `REAL_RAT5_EQ_CONV` for simplifications.

### Informal sketch
* Apply the `POLYTOPE_3D_LEMMA` to establish a foundation for the proof.
* Perform conversions to manipulate vector expressions, specifically using `VECTOR3_SUB_CONV` and `VECTOR3_CROSS_CONV` to simplify vector operations.
* Apply `let_CONV` to handle let bindings, potentially simplifying expressions further.
* Split the proof into two concurrent paths using `CONJ_TAC`:
  + One path focuses on proving a vector is zero using `VECTOR3_EQ_0_CONV`.
  + The other path involves more complex manipulations, including applying `VECTOR3_DOT_CONV` to simplify dot products, and utilizing `EXISTS_IN_INSERT` and `NOT_IN_EMPTY` to handle existential quantifiers and set operations. Further simplifications are made using `REAL_RAT5_EQ_CONV`.

### Mathematical insight
This tactic appears to be designed for proving properties of polytopes, specifically leveraging the `POLYTOPE_3D_LEMMA` as a starting point. The use of various conversion tactics (`VECTOR3_SUB_CONV`, `VECTOR3_CROSS_CONV`, `VECTOR3_DOT_CONV`) suggests that the proof involves significant algebraic manipulation of vectors, potentially to establish geometric properties or relationships. The tactic's structure implies it is tailored for proofs that require breaking down complex vector operations and set existential statements into more manageable parts.

### Dependencies
* Theorems/Definitions:
  + `POLYTOPE_3D_LEMMA`
  + `VECTOR3_SUB_CONV`
  + `VECTOR3_CROSS_CONV`
  + `VECTOR3_DOT_CONV`
  + `VECTOR3_EQ_0_CONV`
  + `REAL_RAT5_EQ_CONV`
  + `EXISTS_IN_INSERT`
  + `NOT_IN_EMPTY`
* Tactics:
  + `MATCH_MP_TAC`
  + `CONV_TAC`
  + `CONJ_TAC`
  + `REWRITE_TAC`

### Porting notes
When translating this tactic into another proof assistant, special attention should be given to how vector operations and conversions are handled. The direct application of tactics like `MATCH_MP_TAC` and `CONV_TAC` with specific conversions may need to be adapted based on the target system's tactic language and library of vector operations. Additionally, the handling of existential quantifiers and set operations (`EXISTS_IN_INSERT`, `NOT_IN_EMPTY`) should be carefully considered to ensure compatibility with the target system's logic and set theory foundations.

---

## STD_TETRAHEDRON_FULLDIM

### Name of formal statement
STD_TETRAHEDRON_FULLDIM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let STD_TETRAHEDRON_FULLDIM = prove
 (`aff_dim std_tetrahedron = &3`,
  REWRITE_TAC[std_tetrahedron] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
The affine dimension of the standard tetrahedron is equal to 3.

### Informal sketch
* The proof involves rewriting the `std_tetrahedron` using the `REWRITE_TAC` tactic with the `std_tetrahedron` definition.
* Then, it applies the `POLYTOPE_FULLDIM_TAC` tactic to establish the affine dimension of the `std_tetrahedron` as 3.
* The key steps mirror the structure of proving geometric properties, specifically focusing on the dimensionality of a polytope.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard tetrahedron, which is a basic geometric object. Knowing its affine dimension is crucial in various geometric and topological contexts, as it influences the object's behavior and interactions within higher-dimensional spaces.

### Dependencies
* `std_tetrahedron`
* `aff_dim`
* `REWRITE_TAC`
* `POLYTOPE_FULLDIM_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles geometric definitions and properties, such as the `std_tetrahedron` and its affine dimension. The `REWRITE_TAC` and `POLYTOPE_FULLDIM_TAC` tactics may have direct or similar counterparts in these systems, but their application and the underlying logic might require adjustments to fit the target system's syntax and proof paradigm.

---

## STD_CUBE_FULLDIM

### Name of formal statement
STD_CUBE_FULLDIM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let STD_CUBE_FULLDIM = prove
 (`aff_dim std_cube = &3`,
  REWRITE_TAC[std_cube] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
The affine dimension of the standard cube is equal to 3.

### Informal sketch
* The proof involves rewriting the `std_cube` using the `REWRITE_TAC` tactic with the `std_cube` definition.
* Then, it applies the `POLYTOPE_FULLDIM_TAC` tactic to establish the affine dimension of the standard cube.
* The key step is recognizing that the `std_cube` has a specific geometric structure that allows its affine dimension to be determined using `POLYTOPE_FULLDIM_TAC`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard cube in geometric terms. The affine dimension of an object is a measure of its intrinsic dimensionality, and knowing this dimension is crucial for various geometric and topological analyses. The standard cube, being a basic geometric shape, serves as a foundation for more complex constructions, making this theorem a building block for further results.

### Dependencies
* `std_cube`
* `aff_dim`
* `POLYTOPE_FULLDIM_TAC`
* `REWRITE_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay attention to how geometric objects like the standard cube are represented and how their properties, such as affine dimension, are defined and computed. The `POLYTOPE_FULLDIM_TAC` tactic, which is specific to HOL Light, may need to be replaced with equivalent tactics or strategies in the target system that can handle geometric reasoning and dimension calculations.

---

## STD_OCTAHEDRON_FULLDIM

### Name of formal statement
STD_OCTAHEDRON_FULLDIM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let STD_OCTAHEDRON_FULLDIM = prove
 (`aff_dim std_octahedron = &3`,
  REWRITE_TAC[std_octahedron] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
The affine dimension of the standard octahedron is equal to 3.

### Informal sketch
* The proof involves rewriting the `std_octahedron` using the `REWRITE_TAC` tactic with the `std_octahedron` definition.
* Then, it applies the `POLYTOPE_FULLDIM_TAC` tactic to establish the affine dimension of the `std_octahedron` as 3.
* The key step is recognizing that `std_octahedron` can be transformed using its definition, allowing the `POLYTOPE_FULLDIM_TAC` tactic to conclude the dimension.

### Mathematical insight
This theorem provides a fundamental property of the standard octahedron, a geometric object, by determining its affine dimension. The affine dimension is a measure of the minimum number of independent coordinates needed to describe the object. In this case, the standard octahedron can be fully described within a 3-dimensional affine space, which is intuitive given its geometric structure.

### Dependencies
#### Theorems and definitions
* `std_octahedron`
* `aff_dim`
* `POLYTOPE_FULLDIM_TAC`

### Porting notes
When porting this theorem to another proof assistant, ensure that the equivalent of `REWRITE_TAC` and `POLYTOPE_FULLDIM_TAC` tactics are used appropriately. The `std_octahedron` definition and the concept of affine dimension (`aff_dim`) must be defined or imported correctly in the target system. Note that the automation and tactic structure might differ between systems, requiring adjustments to replicate the proof strategy.

---

## STD_DODECAHEDRON_FULLDIM

### Name of formal statement
STD_DODECAHEDRON_FULLDIM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let STD_DODECAHEDRON_FULLDIM = prove
 (`aff_dim std_dodecahedron = &3`,
  REWRITE_TAC[STD_DODECAHEDRON] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
The affine dimension of the standard dodecahedron is equal to 3.

### Informal sketch
* The proof involves rewriting the `std_dodecahedron` using the `STD_DODECAHEDRON` definition.
* Then, it applies the `POLYTOPE_FULLDIM_TAC` tactic to establish the affine dimension of the `std_dodecahedron` as 3.
* The key insight here is that the `POLYTOPE_FULLDIM_TAC` tactic is used to derive the full dimension of the polytope, leveraging the properties defined in `STD_DODECAHEDRON`.

### Mathematical insight
This theorem provides a fundamental property of the standard dodecahedron, which is a regular polyhedron with 12 pentagonal faces. Establishing its affine dimension as 3 is crucial for understanding its geometric structure and relationships with other geometric objects in 3-dimensional space.

### Dependencies
* `STD_DODECAHEDRON`
* `POLYTOPE_FULLDIM_TAC`
* `REWRITE_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles geometric definitions and properties, such as the `std_dodecahedron` and its dimension. The equivalent of `POLYTOPE_FULLDIM_TAC` and `REWRITE_TAC` tactics may need to be identified or implemented in the target system to replicate the proof strategy. Additionally, the representation of the dodecahedron and its properties may vary, requiring adjustments to the proof script to align with the target system's formalisms and libraries.

---

## STD_ICOSAHEDRON_FULLDIM

### Name of formal statement
STD_ICOSAHEDRON_FULLDIM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let STD_ICOSAHEDRON_FULLDIM = prove
 (`aff_dim std_icosahedron = &3`,
  REWRITE_TAC[STD_ICOSAHEDRON] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
The affine dimension of the standard icosahedron is equal to 3.

### Informal sketch
* The proof involves rewriting the `std_icosahedron` using the `STD_ICOSAHEDRON` definition.
* Then, it applies the `POLYTOPE_FULLDIM_TAC` tactic to establish the affine dimension of the `std_icosahedron` as 3.
* The key steps rely on the properties of the `std_icosahedron` and the `POLYTOPE_FULLDIM_TAC` tactic to derive the dimension.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard icosahedron, which is a canonical geometric object. Knowing its affine dimension is crucial for various geometric and topological considerations.

### Dependencies
* `STD_ICOSAHEDRON`
* `POLYTOPE_FULLDIM_TAC`

### Porting notes
When porting this theorem to another proof assistant, ensure that the equivalent of `POLYTOPE_FULLDIM_TAC` is available or can be implemented. Additionally, the representation of the `std_icosahedron` and its properties should be correctly translated to maintain the proof's validity.

---

## COMPUTE_EDGES_TAC

### Name of formal statement
COMPUTE_EDGES_TAC

### Type of the formal statement
Theorem/Tactic

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
    REWRITE_TAC[INSERT_AC] THEN REWRITE_TAC[DISJ_ACI]]
```

### Informal statement
The `COMPUTE_EDGES_TAC` tactic is defined to compute the edges of a polyhedron given its definition `defn`, its full dimension `fulldim`, and its facets. It involves proving the existence of a face `f` of the polyhedron `p` with dimension 2 and an edge `e` of `f` with dimension 1, using various properties of faces and polyhedra, such as `FACE_OF_TRANS`, `FACE_OF_POLYHEDRON_SUBSET_FACET`, `POLYHEDRON_CONVEX_HULL`, and `MONO_EXISTS`.

### Informal sketch
* The tactic starts by applying `GEN_TAC` to introduce a generic variable.
* It then uses `MATCH_MP_TAC EQ_TRANS` to establish an equality through transitivity.
* The `EXISTS_TAC` is used to introduce an existential quantifier, asserting the existence of a face `f` and an edge `e` with specific properties.
* The tactic proceeds with `CONJ_TAC` to split the goal into two parts, each of which is then addressed through a series of rewriting and application of specific theorems and properties, including `FACE_OF_TRANS`, `POLYHEDRON_CONVEX_HULL`, and `MONO_EXISTS`.
* Key steps involve substituting definitions, applying mathematical properties of faces and polyhedra, and using logical equivalences to simplify and solve the goals.

### Mathematical insight
The `COMPUTE_EDGES_TAC` tactic is designed to automate the process of computing the edges of a polyhedron based on its definition and geometric properties. It relies on the mathematical structure of polyhedra, including the relationships between faces, edges, and dimensions. The tactic's construction reflects the logical and geometric insights into how edges can be identified and characterized within a polyhedron, utilizing principles of geometry and logic to derive the existence and properties of edges.

### Dependencies
#### Theorems
- `FACE_OF_TRANS`
- `FACE_OF_POLYHEDRON_SUBSET_FACET`
- `POLYHEDRON_CONVEX_HULL`
- `MONO_EXISTS`
- `EXISTS_OR_THM`
- `UNWIND_THM2`
#### Definitions
- `facet_of`
- `fulldim`
- `aff_dim`
- `COMPUTE_EDGES_CONV` 

### Porting notes
When translating this tactic into another proof assistant like Lean, Coq, or Isabelle, special attention should be paid to how existential quantification and equality reasoning are handled, as these are central to the tactic's operation. Additionally, the equivalents of `GEN_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, and `CONJ_TAC` need to be identified in the target system, along with the corresponding rewriting and simplification mechanisms. The porting process may also require adjusting the tactic to fit the specific proof assistant's handling of mathematical types, such as `real^3->bool`, and its support for automated reasoning about geometric objects like polyhedra.

---

## TETRAHEDRON_EDGES

### Name of formal statement
TETRAHEDRON_EDGES

### Type of the formal statement
Theorem

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
    std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_FACETS)
```

### Informal statement
For all `e`, `e` is a face of the standard tetrahedron and the affine dimension of `e` is 1 if and only if `e` is equal to the convex hull of one of the following pairs of vectors: 
- `vector[-- &1; -- &1; &1]` and `vector[-- &1; &1; -- &1]`, 
- `vector[-- &1; -- &1; &1]` and `vector[&1; -- &1; -- &1]`, 
- `vector[-- &1; -- &1; &1]` and `vector[&1; &1; &1]`, 
- `vector[-- &1; &1; -- &1]` and `vector[&1; -- &1; -- &1]`, 
- `vector[-- &1; &1; -- &1]` and `vector[&1; &1; &1]`, 
- `vector[&1; -- &1; -- &1]` and `vector[&1; &1; &1]`.

### Informal sketch
* The proof involves using the `COMPUTE_EDGES_TAC` tactic to compute the edges of the standard tetrahedron.
* The tactic `COMPUTE_EDGES_TAC` is applied to `std_tetrahedron` with `STD_TETRAHEDRON_FULLDIM` and `TETRAHEDRON_FACETS` as premises.
* The proof checks the affine dimension of each face `e` of the standard tetrahedron and verifies that it is 1 if and only if `e` is one of the specified convex hulls.
* The key steps involve calculating the convex hulls of the given pairs of vectors and comparing them with the faces of the standard tetrahedron.

### Mathematical insight
This theorem provides a characterization of the edges of the standard tetrahedron in terms of the convex hulls of specific pairs of vectors. It is a fundamental result in the geometric theory of polyhedra and is useful for proving other properties of tetrahedra.

### Dependencies
* `std_tetrahedron`
* `STD_TETRAHEDRON_FULLDIM`
* `TETRAHEDRON_FACETS`
* `COMPUTE_EDGES_TAC`

### Porting notes
When porting this theorem to another proof assistant, note that the `COMPUTE_EDGES_TAC` tactic may need to be replaced with an equivalent tactic or a manual proof. Additionally, the representation of vectors and convex hulls may differ between systems, requiring adjustments to the formal statement.

---

## CUBE_EDGES

### Name of formal statement
CUBE_EDGES

### Type of the formal statement
Theorem

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
    std_cube STD_CUBE_FULLDIM CUBE_FACETS)
```

### Informal statement
For all `e`, `e` is a face of the standard cube and the affine dimension of `e` is 1 if and only if `e` is equal to the convex hull of one of the 12 pairs of vertices of the cube that define its edges.

### Informal sketch
* The proof involves using the `COMPUTE_EDGES_TAC` tactic to compute the edges of the standard cube `std_cube`.
* It utilizes the `STD_CUBE_FULLDIM` and `CUBE_FACETS` theorems to establish the properties of the cube.
* The main logical stage is to show that the edges of the cube are exactly the convex hulls of the specified pairs of vertices.
* This involves checking that each edge is a face of the cube and has an affine dimension of 1.

### Mathematical insight
This theorem provides a characterization of the edges of the standard cube in terms of the convex hulls of its vertices. It is a fundamental result in the geometry of the cube and has implications for understanding the structure of higher-dimensional cubes and their subspaces.

### Dependencies
* `std_cube`
* `STD_CUBE_FULLDIM`
* `CUBE_FACETS`
* `COMPUTE_EDGES_TAC`

### Porting notes
When porting this theorem to other proof assistants, note that the `COMPUTE_EDGES_TAC` tactic may not have a direct equivalent. Instead, the proof may need to be reconstructed using the specific tactics and libraries available in the target system. Additionally, the representation of the cube and its vertices may need to be adapted to the target system's geometry library.

---

## OCTAHEDRON_EDGES

### Name of formal statement
OCTAHEDRON_EDGES

### Type of the formal statement
Theorem

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
     std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_FACETS)
```

### Informal statement
For all `e`, `e` is a face of the standard octahedron and the affine dimension of `e` is 1 if and only if `e` is equal to the convex hull of one of the following sets of vectors: 
{ `vector[-- &1; &0; &0]`, `vector[&0; -- &1; &0]` },
{ `vector[-- &1; &0; &0]`, `vector[&0; &1; &0]` },
{ `vector[-- &1; &0; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[-- &1; &0; &0]`, `vector[&0; &0; &1]` },
{ `vector[&1; &0; &0]`, `vector[&0; -- &1; &0]` },
{ `vector[&1; &0; &0]`, `vector[&0; &1; &0]` },
{ `vector[&1; &0; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[&1; &0; &0]`, `vector[&0; &0; &1]` },
{ `vector[&0; -- &1; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[&0; -- &1; &0]`, `vector[&0; &0; &1]` },
{ `vector[&0; &1; &0]`, `vector[&0; &0; -- &1]` },
{ `vector[&0; &1; &0]`, `vector[&0; &0; &1]` }.

### Informal sketch
* The proof involves using the `COMPUTE_EDGES_TAC` tactic to compute the edges of the standard octahedron.
* The tactic `COMPUTE_EDGES_TAC` is applied to `std_octahedron` with `STD_OCTAHEDRON_FULLDIM` and `OCTAHEDRON_FACETS` as premises.
* The main logical stage is to show that the edges of the standard octahedron are exactly the convex hulls of the specified sets of vectors.
* The proof uses the `face_of` predicate to identify the faces of the standard octahedron and the `aff_dim` function to compute their affine dimensions.

### Mathematical insight
The theorem provides a characterization of the edges of the standard octahedron in terms of the convex hulls of specific sets of vectors. This characterization is useful for reasoning about the geometric properties of the octahedron and its faces.

### Dependencies
* `std_octahedron`
* `STD_OCTAHEDRON_FULLDIM`
* `OCTAHEDRON_FACETS`
* `face_of`
* `aff_dim`
* `convex hull`

### Porting notes
When porting this theorem to another proof assistant, note that the `COMPUTE_EDGES_TAC` tactic may not have a direct equivalent. The porter may need to use a combination of tactics to achieve the same result. Additionally, the `face_of` and `aff_dim` predicates may need to be defined or imported from a library.

---

## DODECAHEDRON_EDGES

### Name of formal statement
DODECAHEDRON_EDGES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DODECAHEDRON_EDGES = prove
 (`!e. e face_of std_dodecahedron /\ aff_dim e = &1 <=>
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; -- &1 / &2 + &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); &0; &1 / &2 + -- &1 / &2 * sqrt (&5)]} \/
       e = convex hull {vector[-- &1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0], vector[&1 / &2 + -- &1 / &2 * sqrt (&5); -- &1 / &2 + -- &1 / &2 * sqrt (&5); &0]} \/
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
    STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_FACETS)
```

### Informal statement
For all `e`, `e` is a face of `std_dodecahedron` and the affine dimension of `e` is 1 if and only if `e` is equal to the convex hull of one of the specified sets of vectors. The specified sets of vectors define the edges of the dodecahedron.

### Informal sketch
* The proof involves showing that each edge of the `std_dodecahedron` is a face of dimension 1.
* It uses the `COMPUTE_EDGES_TAC` tactic to compute the edges of the dodecahedron based on its facets and full dimension.
* The `STD_DODECAHEDRON`, `STD_DODECAHEDRON_FULLDIM`, and `DODECAHEDRON_FACETS` are used as premises in the proof.
* The proof is structured as a series of equivalences, where each edge is shown to be equal to the convex hull of a specific set of vectors.

### Mathematical insight
The `DODECAHEDRON_EDGES` theorem provides a characterization of the edges of the `std_dodecahedron` in terms of their convex hulls. This is important for understanding the geometric structure of the dodecahedron and for further reasoning about its properties.

### Dependencies
* `STD_DODECAHEDRON`
* `STD_DODECAHEDRON_FULLDIM`
* `DODECAHEDRON_FACETS`
* `COMPUTE_EDGES_TAC`

### Porting notes
When porting this theorem to another proof assistant, it is necessary to ensure that the `COMPUTE_EDGES_TAC` tactic is implemented correctly and that the `STD_DODECAHEDRON`, `STD_DODECAHEDRON_FULLDIM`, and `DODECAHEDRON_FACETS` are defined and proved accordingly. Additionally, the convex hull operation and the notion of affine dimension should be properly defined and implemented in the target system.

---

## ICOSAHEDRON_EDGES

### Name of formal statement
ICOSAHEDRON_EDGES

### Type of the formal statement
Theorem

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
    STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_FACETS)
```

### Informal statement
For all `e`, `e` is a face of the standard icosahedron and the affine dimension of `e` is 1 if and only if `e` is equal to the convex hull of one of the 30 specified pairs of vectors.

### Informal sketch
The proof involves computing the edges of the standard icosahedron using the `COMPUTE_EDGES_TAC` tactic. This tactic is applied to the `STD_ICOSAHEDRON`, `STD_ICOSAHEDRON_FULLDIM`, and `ICOSAHEDRON_FACETS` definitions. The main steps involve:
* Identifying the faces of the icosahedron
* Computing the affine dimension of each face
* Checking if the face is an edge (i.e., has affine dimension 1)
* If it is an edge, computing its convex hull
The proof is a straightforward application of the `COMPUTE_EDGES_TAC` tactic to the given definitions.

### Mathematical insight
This theorem provides a characterization of the edges of the standard icosahedron in terms of their convex hulls. It is a fundamental result in the geometry of polyhedra and is useful for further reasoning about the properties of icosahedra.

### Dependencies
* `STD_ICOSAHEDRON`
* `STD_ICOSAHEDRON_FULLDIM`
* `ICOSAHEDRON_FACETS`
* `COMPUTE_EDGES_TAC`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `COMPUTE_EDGES_TAC` tactic is properly translated. This may involve rewriting the tactic in terms of the target system's primitives or using a similar tactic if available. Additionally, the definitions of `STD_ICOSAHEDRON`, `STD_ICOSAHEDRON_FULLDIM`, and `ICOSAHEDRON_FACETS` must be properly ported and aligned with the target system's representation of geometric objects.

---

## COMPUTE_VERTICES_TAC

### Name of formal statement
COMPUTE_VERTICES_TAC

### Type of the formal statement
Theorem/Tactic

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
    REWRITE_TAC[DISJ_ACI]]
```

### Informal statement
The `COMPUTE_VERTICES_TAC` theorem/tactic is defined for computing vertices based on a given definition `defn`, full dimension `fulldim`, and edges `edges`. It involves a series of logical deductions and transformations to enumerate all vertices. The process starts by assuming the existence of a set `e` that is a face of `p` with affine dimension 1 and a set `v` that is a face of `e` with affine dimension 0. It then applies various tactics, including `GEN_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, and `CONJ_TAC`, to derive properties about `p`, `e`, and `v`. The theorem/tactic utilizes several other theorems and definitions, such as `FACE_OF_TRANS`, `FACE_OF_POLYHEDRON_SUBSET_FACET`, and `POLYHEDRON_CONVEX_HULL`, to establish the relationships between these sets and their dimensions.

### Informal sketch
* The proof begins by applying `GEN_TAC` to introduce a general variable, followed by `MATCH_MP_TAC EQ_TRANS` to establish an equality.
* It then uses `EXISTS_TAC` to assume the existence of sets `e` and `v` with specific properties regarding their face relationships and affine dimensions.
* The tactic `CONJ_TAC` is applied to split the goal into two parts, which are then addressed separately using `EQ_TAC`, `STRIP_TAC`, and `MESON_TAC` to derive equalities and properties about the faces and dimensions.
* Further applications of `MP_TAC`, `ANTS_TAC`, and `REWRITE_TAC` are used to manipulate and simplify the expressions, leveraging theorems like `FACE_OF_POLYHEDRON_SUBSET_FACET` and `POLYHEDRON_CONVEX_HULL`.
* The process involves choosing specific sets `f` and `v` and applying `MATCH_MP_TAC` with `FACE_OF_POLYHEDRON_POLYHEDRON` to establish their properties.
* The tactic `REPEAT CONJ_TAC` is used to handle multiple conjunctions, and `DISCH_THEN` is applied to discharge assumptions and apply `MP_TAC` with specific terms.
* The final steps involve rewriting expressions using `REWRITE_TAC` with various theorems and properties, such as `edges`, `EXISTS_OR_THM`, and `AFF_DIM_EQ_0`, to conclude the enumeration of vertices.

### Mathematical insight
The `COMPUTE_VERTICES_TAC` theorem/tactic is crucial for computing vertices in geometric and topological contexts, particularly in the study of polyhedra and their faces. It provides a systematic approach to enumerating vertices based on the definitions and properties of the sets involved. The underlying mathematics relies on concepts from geometry, topology, and set theory, including face relationships, affine dimensions, and convex hulls. This theorem/tactic is important for understanding and working with geometric objects and their properties in a formal and rigorous manner.

### Dependencies
#### Theorems
* `FACE_OF_TRANS`
* `FACE_OF_POLYHEDRON_SUBSET_FACET`
* `POLYHEDRON_CONVEX_HULL`
* `FACE_OF_POLYHEDRON_POLYHEDRON`
* `MONO_EXISTS`
* `EXISTS_OR_THM`
* `UNWIND_THM2`
* `AFF_DIM_EQ_0`
* `RIGHT_AND_EXISTS_THM`
* `GSYM SEGMENT_CONVEX_HULL`
* `FACE_OF_SING`
* `EXTREME_POINT_OF_SEGMENT`
* `DISJ_ACI`

#### Definitions
* `defn`
* `fulldim`
* `edges`
* `facet_of`
* `aff_dim`

### Porting notes
When translating this theorem/tactic into other proof assistants like Lean, Coq, or Isabelle, special attention should be given to the handling of binders, existential quantification, and the application of tactics. The `EXISTS_TAC` and `CONJ_TAC` tactics, in particular, may require careful translation to ensure that the introduction of existential quantifiers and conjunctions is properly managed. Additionally, the use of `REWRITE_TAC` with various theorems may need to be adapted to the target proof assistant's rewriting mechanisms. It is also important to ensure that the translated theorem/tactic correctly handles the geometric and topological concepts, such as face relationships and affine dimensions, to maintain the mathematical accuracy and rigor of the original formalization.

---

## TETRAHEDRON_VERTICES

### Name of formal statement
TETRAHEDRON_VERTICES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TETRAHEDRON_VERTICES = prove
 (`!v. v face_of std_tetrahedron /\ aff_dim v = &0 <=>
       v = {vector [-- &1; -- &1; &1]} \/
       v = {vector [-- &1; &1; -- &1]} \/
       v = {vector [&1; -- &1; -- &1]} \/
       v = {vector [&1; &1; &1]}`,
  COMPUTE_VERTICES_TAC
    std_tetrahedron STD_TETRAHEDRON_FULLDIM TETRAHEDRON_EDGES)
```

### Informal statement
For all `v`, `v` is a face of the standard tetrahedron and the affine dimension of `v` is 0 if and only if `v` is equal to one of the following vectors: `[-1, -1, 1]`, `[-1, 1, -1]`, `[1, -1, -1]`, or `[1, 1, 1]`.

### Informal sketch
* The proof involves showing that the vertices of the standard tetrahedron are exactly the four specified points.
* The `COMPUTE_VERTICES_TAC` tactic is used to compute the vertices of the `std_tetrahedron`.
* The `STD_TETRAHEDRON_FULLDIM` and `TETRAHEDRON_EDGES` theorems are likely used to establish properties of the standard tetrahedron.
* The proof proceeds by showing that each of the four specified points satisfies the conditions for being a vertex of the standard tetrahedron, and conversely, that any vertex of the standard tetrahedron must be one of these four points.

### Mathematical insight
This theorem provides a characterization of the vertices of the standard tetrahedron, which is a fundamental geometric object in mathematics. The theorem is important because it provides a precise definition of the vertices of the tetrahedron, which can be used in further mathematical developments.

### Dependencies
* `std_tetrahedron`
* `STD_TETRAHEDRON_FULLDIM`
* `TETRAHEDRON_EDGES`
* `COMPUTE_VERTICES_TAC`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `COMPUTE_VERTICES_TAC` tactic is replaced with an equivalent tactic or strategy in the target system. Additionally, the `STD_TETRAHEDRON_FULLDIM` and `TETRAHEDRON_EDGES` theorems should be ported or re-proved in the target system. The use of `aff_dim` and `face_of` functions may also require special attention, as their implementations may differ between proof assistants.

---

## CUBE_VERTICES

### Name of formal statement
CUBE_VERTICES

### Type of the formal statement
Theorem

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
    std_cube STD_CUBE_FULLDIM CUBE_EDGES)
```

### Informal statement
For all `v`, `v` is a face of the standard cube and the affine dimension of `v` is 0 if and only if `v` is equal to one of the eight vertices of the cube, specifically: 
- the vector `[-1, -1, -1]`, 
- the vector `[-1, -1, 1]`, 
- the vector `[-1, 1, -1]`, 
- the vector `[-1, 1, 1]`, 
- the vector `[1, -1, -1]`, 
- the vector `[1, -1, 1]`, 
- the vector `[1, 1, -1]`, 
- or the vector `[1, 1, 1]`.

### Informal sketch
* The proof involves showing that each of the eight specified vectors is indeed a vertex of the standard cube with affine dimension 0.
* It also involves demonstrating that any point `v` that is a face of the standard cube and has an affine dimension of 0 must be one of these eight vertices.
* The `COMPUTE_VERTICES_TAC` tactic is used in conjunction with `std_cube`, `STD_CUBE_FULLDIM`, and `CUBE_EDGES` to establish these facts.
* The key steps include:
  - Identifying the vertices of the standard cube
  - Verifying the affine dimension of each vertex
  - Using the properties of the standard cube and its edges to ensure no other points satisfy the conditions

### Mathematical insight
This theorem is important because it provides a precise characterization of the vertices of the standard cube in terms of their geometric properties. It is a foundational result in geometric reasoning within HOL Light, allowing for further theorems and proofs about geometric objects and their properties.

### Dependencies
- `std_cube`
- `STD_CUBE_FULLDIM`
- `CUBE_EDGES`
- `COMPUTE_VERTICES_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system represents geometric objects and their properties. The concept of affine dimension and the specific representation of the standard cube may vary, requiring adjustments to the proof strategy. Additionally, the automation provided by `COMPUTE_VERTICES_TAC` may not have a direct equivalent, necessitating a manual or tactic-based approach to prove the characterization of the cube's vertices.

---

## OCTAHEDRON_VERTICES

### Name of formal statement
OCTAHEDRON_VERTICES

### Type of the formal statement
Theorem

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
     std_octahedron STD_OCTAHEDRON_FULLDIM OCTAHEDRON_EDGES)
```

### Informal statement
For all `v`, `v` is a face of the standard octahedron and the affine dimension of `v` is 0 if and only if `v` is equal to one of the following six vectors: `{-1, 0, 0}`, `{1, 0, 0}`, `{0, -1, 0}`, `{0, 1, 0}`, `{0, 0, -1}`, or `{0, 0, 1}`.

### Informal sketch
* The proof involves using the `COMPUTE_VERTICES_TAC` tactic to compute the vertices of the standard octahedron.
* It relies on the definition of `std_octahedron` and the properties of its faces, as well as the `STD_OCTAHEDRON_FULLDIM` and `OCTAHEDRON_EDGES` theorems.
* The proof strategy involves showing that the vertices of the standard octahedron are precisely the six specified vectors, by exploiting the geometric properties of the octahedron and the definition of `face_of`.

### Mathematical insight
This theorem provides a characterization of the vertices of the standard octahedron, which is a fundamental geometric object in mathematics. The theorem is important because it establishes a precise relationship between the geometric properties of the octahedron and its algebraic representation. This characterization is useful in a variety of mathematical contexts, including geometry, topology, and computer science.

### Dependencies
* `std_octahedron`
* `STD_OCTAHEDRON_FULLDIM`
* `OCTAHEDRON_EDGES`
* `COMPUTE_VERTICES_TAC`
* `face_of`
* `aff_dim`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the geometric properties of the octahedron are properly represented. In particular, the definition of `std_octahedron` and the `face_of` predicate may need to be adapted to the target system. Additionally, the `COMPUTE_VERTICES_TAC` tactic may not have a direct analogue in other systems, so an alternative proof strategy may be needed.

---

## DODECAHEDRON_VERTICES

### Name of formal statement
DODECAHEDRON_VERTICES

### Type of the formal statement
Theorem

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
    STD_DODECAHEDRON STD_DODECAHEDRON_FULLDIM DODECAHEDRON_EDGES)
```

### Informal statement
For all `v`, `v` is a vertex of the standard dodecahedron and has affine dimension 0 if and only if `v` is one of the following 20 vertices: 
`{vector[-- 1/2 + -- 1/2 * sqrt(5); 0; -- 1/2 + 1/2 * sqrt(5)]}`,
`{vector[-- 1/2 + -- 1/2 * sqrt(5); 0; 1/2 + -- 1/2 * sqrt(5)]}`,
`{vector[-- 1/2 + 1/2 * sqrt(5); -- 1/2 + -- 1/2 * sqrt(5); 0]}`,
`{vector[-- 1/2 + 1/2 * sqrt(5); 1/2 + 1/2 * sqrt(5); 0]}`,
`{vector[1/2 + -- 1/2 * sqrt(5); -- 1/2 + -- 1/2 * sqrt(5); 0]}`,
`{vector[1/2 + -- 1/2 * sqrt(5); 1/2 + 1/2 * sqrt(5); 0]}`,
`{vector[1/2 + 1/2 * sqrt(5); 0; -- 1/2 + 1/2 * sqrt(5)]}`,
`{vector[1/2 + 1/2 * sqrt(5); 0; 1/2 + -- 1/2 * sqrt(5)]}`,
`{vector[-- 1; -- 1; -- 1]}`,
`{vector[-- 1; -- 1; 1]}`,
`{vector[-- 1; 1; -- 1]}`,
`{vector[-- 1; 1; 1]}`,
`{vector[1; -- 1; -- 1]}`,
`{vector[1; -- 1; 1]}`,
`{vector[1; 1; -- 1]}`,
`{vector[1; 1; 1]}`,
`{vector[0; -- 1/2 + 1/2 * sqrt(5); -- 1/2 + -- 1/2 * sqrt(5)]}`,
`{vector[0; -- 1/2 + 1/2 * sqrt(5); 1/2 + 1/2 * sqrt(5)]}`,
`{vector[0; 1/2 + -- 1/2 * sqrt(5); -- 1/2 + -- 1/2 * sqrt(5)]}`,
`{vector[0; 1/2 + -- 1/2 * sqrt(5); 1/2 + 1/2 * sqrt(5)]}`.

### Informal sketch
* The statement `DODECAHEDRON_VERTICES` characterizes the vertices of the standard dodecahedron `std_dodecahedron`.
* It utilizes the `COMPUTE_VERTICES_TAC` tactic, which is likely a custom tactic for computing vertices of a geometric object.
* The proof involves the `STD_DODECAHEDRON`, `STD_DODECAHEDRON_FULLDIM`, and `DODECAHEDRON_EDGES` theorems or definitions, which provide necessary information about the dodecahedron's structure.
* The `aff_dim v = &0` condition ensures that only points (0-dimensional affine subspaces) are considered as vertices.
* The long disjunction lists all possible vertices of the dodecahedron, which can be seen as a combination of rational and irrational coordinates involving `sqrt(5)`.

### Mathematical insight
This statement provides an exhaustive characterization of the vertices of a standard dodecahedron, a fundamental concept in geometry. The dodecahedron is a regular polyhedron with 12 pentagonal faces, and its vertices are crucial for understanding its structure and properties. The use of `sqrt(5)` in the coordinates reflects the irrational nature of the dodecahedron's geometry.

### Dependencies
* `STD_DODECAHEDRON`
* `STD_DODECAHEDRON_FULLDIM`
* `DODECAHEDRON_EDGES`
* `COMPUTE_VERTICES_TAC` 

### Porting notes
When porting this statement to another proof assistant, special attention should be paid to the `COMPUTE_VERTICES_TAC` tactic, as it may not have a direct equivalent. The porting process may require re-implementing this tactic or finding an alternative approach to compute the vertices of the dodecahedron. Additionally, the use of `sqrt(5)` in the coordinates may require careful handling of irrational numbers in the target proof assistant.

---

## ICOSAHEDRON_VERTICES

### Name of formal statement
ICOSAHEDRON_VERTICES

### Type of the formal statement
Theorem

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
    STD_ICOSAHEDRON STD_ICOSAHEDRON_FULLDIM ICOSAHEDRON_EDGES)
```

### Informal statement
For all `v`, `v` is a vertex of the standard icosahedron and has affine dimension 0 if and only if `v` is equal to one of the twelve specifically defined vectors. These vectors represent the vertices of the icosahedron in 3-dimensional space, with coordinates involving square roots and rational numbers.

### Informal sketch
* The proof involves showing that the given set of vectors are the only possible vertices of the `std_icosahedron`.
* It uses the `COMPUTE_VERTICES_TAC` tactic to compute the vertices based on the `STD_ICOSAHEDRON`, `STD_ICOSAHEDRON_FULLDIM`, and `ICOSAHEDRON_EDGES`.
* The main logical stage is to establish the equivalence between being a vertex of the icosahedron with affine dimension 0 and being one of the specified vectors.
* The proof relies on geometric properties of the icosahedron and the definition of its faces and edges.

### Mathematical insight
This theorem provides a precise characterization of the vertices of a standard icosahedron in terms of their coordinates. It is a fundamental result in geometry, essential for various applications, including computer graphics, engineering, and mathematics. The icosahedron is one of the five Platonic solids, and understanding its structure is crucial for studying the properties of these solids.

### Dependencies
#### Theorems
* `STD_ICOSAHEDRON`
* `ICOSAHEDRON_EDGES`
#### Definitions
* `std_icosahedron`
* `aff_dim`
* `face_of`
#### Inductive rules
None

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system represents vectors, geometric objects, and affine dimensions. The `COMPUTE_VERTICES_TAC` tactic may need to be replaced with equivalent tactics or functions in the target system. Additionally, ensure that the ported version correctly handles the rational numbers and square roots involved in the coordinates of the icosahedron's vertices.

---

## EDGES_PER_VERTEX_TAC

### Name of formal statement
EDGES_PER_VERTEX_TAC

### Type of the formal statement
Theorem

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
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 HAS_SIZE_CLAUSES]
```

### Informal statement
This theorem calculates the number of edges meeting at each vertex in a geometric configuration. It starts with a definition `defn` and two parameters `edges` and `verts`, and applies a series of logical transformations to derive a conclusion about the cardinality of a set of edges related to a given vertex `v`. The statement involves concepts such as faces, affine dimension, and convex hulls, and utilizes various set-theoretic and logical operations.

### Informal sketch
* The proof begins by applying `REPEAT STRIP_TAC` to simplify the goal, followed by `MATCH_MP_TAC EQ_TRANS` to introduce an intermediate equality.
* It then uses `EXISTS_TAC` to introduce a specific set related to the faces of a polyhedron `p` and the edges `e` that have `v` as a vertex.
* The proof proceeds with `CONJ_TAC` to split the goal into two parts, one of which is further simplified using `AP_TERM_TAC`, `REWRITE_TAC`, and `ASM_MESON_TAC`.
* The `MP_TAC` and `ISPEC` tactics are used to instantiate a theorem with a specific term, followed by `ASM_REWRITE_TAC` and `DISCH_THEN` to simplify and discharge assumptions.
* The proof then applies a series of `REWRITE_TAC` steps to transform the goal, using various set-theoretic rules and theorems such as `EXTENSION`, `IN_ELIM_THM`, and `FACE_OF_FACE`.
* It also uses `CONV_TAC` with specific conversions (`VECTOR3_SUB_CONV` and `VECTOR3_EQ_0_CONV`) to manipulate vector expressions.
* The final steps involve applying `MATCH_MP_TAC` with `CARD_EQ_LEMMA` and simplifying the resulting expression using `CONV_TAC` and `REWRITE_TAC`.

### Mathematical insight
This theorem provides a way to calculate the number of edges incident on a vertex in a geometric configuration, which is a fundamental concept in geometry and graph theory. The proof involves a series of logical and set-theoretic manipulations, demonstrating the power of formal reasoning in deriving non-trivial results from basic definitions and axioms.

### Dependencies
* Theorems:
	+ `EQ_TRANS`
	+ `FACE_OF_FACE`
	+ `HAS_SIZE`
	+ `CARD_EQ_LEMMA`
* Definitions:
	+ `defn`
	+ `edges`
	+ `verts`
* Rules:
	+ `EXTENSION`
	+ `IN_ELIM_THM`
	+ `SET_RULE`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the following:
* The use of `REPEAT` and `REPEAT_TCL` tactics, which may need to be replaced with equivalent constructs in the target system.
* The application of `CONV_TAC` with specific conversions, which may require analogous conversions or rewriting rules in the target system.
* The instantiation of theorems using `ISPEC` and `MP_TAC`, which may need to be replaced with equivalent instantiation and modus ponens constructs in the target system.
* The use of set-theoretic rules and theorems, which may need to be replaced with equivalent rules and theorems in the target system.

---

## TETRAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
TETRAHEDRON_EDGES_PER_VERTEX

### Type of the formal statement
Theorem

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
For all vertices `v` of the standard tetrahedron, if `v` has affine dimension 0, then the cardinality of the set of edges `e` of the standard tetrahedron with affine dimension 1, such that `v` is a subset of `e`, is equal to 3.

### Informal sketch
* The proof starts by considering an arbitrary vertex `v` of the `std_tetrahedron`.
* It then uses the `EDGES_PER_VERTEX_TAC` tactic to establish the relationship between `v` and the edges of the tetrahedron.
* The key insight is that each vertex of the tetrahedron is incident to exactly three edges, which can be formally verified using the `std_tetrahedron`, `TETRAHEDRON_EDGES`, and `TETRAHEDRON_VERTICES` definitions.
* The proof leverages the properties of the `face_of` and `aff_dim` functions to constrain the edges and vertices under consideration.

### Mathematical insight
This theorem provides a fundamental property of the standard tetrahedron, namely that each vertex is connected to exactly three edges. This is a crucial aspect of the tetrahedron's combinatorial structure and has implications for its geometric and topological properties.

### Dependencies
* `std_tetrahedron`
* `TETRAHEDRON_EDGES`
* `TETRAHEDRON_VERTICES`
* `face_of`
* `aff_dim`
* `EDGES_PER_VERTEX_TAC`

### Porting notes
When translating this theorem to other proof assistants, pay attention to the handling of affine dimensions and the `face_of` relation. The `EDGES_PER_VERTEX_TAC` tactic may need to be replaced with equivalent tactics or manual proofs, depending on the target system's capabilities. Additionally, the representation of the standard tetrahedron and its edges and vertices may vary between systems, requiring adjustments to the formal statement and its dependencies.

---

## CUBE_EDGES_PER_VERTEX

### Name of formal statement
CUBE_EDGES_PER_VERTEX

### Type of the formal statement
Theorem

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
For all vertices `v` that are faces of the standard cube `std_cube` and have an affine dimension of 0, it holds that the cardinality of the set of edges `e` that are faces of `std_cube`, have an affine dimension of 1, and contain `v` as a subset is equal to 3.

### Informal sketch
* The proof involves assuming a vertex `v` of the `std_cube` with `aff_dim(v) = 0`, indicating `v` is a point.
* It then considers the set of edges `e` of `std_cube` where `aff_dim(e) = 1`, meaning `e` is a line segment, and `v` is a subset of `e`, implying `v` is an endpoint of `e`.
* The `EDGES_PER_VERTEX_TAC` tactic is used to establish that exactly three such edges meet at each vertex `v` of `std_cube`.
* This involves understanding the geometric structure of `std_cube` and the definitions of `face_of`, `aff_dim`, and the relationship between vertices and edges in this context.

### Mathematical insight
This theorem provides insight into the combinatorial structure of the standard cube, specifically how many edges meet at each vertex. It is a fundamental property that can be used in further geometric or topological analyses involving the cube.

### Dependencies
* `std_cube`
* `CUBE_EDGES`
* `CUBE_VERTICES`
* `face_of`
* `aff_dim`
* `SUBSET`
* `CARD`

### Porting notes
When translating this into another proof assistant, ensure that the representations of `std_cube`, its faces, edges, and vertices, as well as the `aff_dim` function and subset relation, are correctly defined and aligned with the target system's libraries or constructions. Special attention should be given to how the target system handles quantifiers, set comprehensions, and cardinality, as these are crucial elements of the formal statement.

---

## OCTAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
OCTAHEDRON_EDGES_PER_VERTEX

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OCTAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_octahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 4`,
  EDGES_PER_VERTEX_TAC
    std_octahedron OCTAHEDRON_EDGES OCTAHEDRON_VERTICES)
```

### Informal statement
For all vertices `v` of the standard octahedron, if `v` has an affine dimension of 0, then the number of edges `e` of the standard octahedron with an affine dimension of 1 that contain `v` is equal to 4.

### Informal sketch
* The proof starts with a universal quantification over all vertices `v` of the `std_octahedron`.
* It assumes that `v` is a face of `std_octahedron` with an affine dimension of 0, which implies `v` is a point.
* The goal is to show that the cardinality of the set of edges `e` that are faces of `std_octahedron`, have an affine dimension of 1, and contain `v` is equal to 4.
* The `EDGES_PER_VERTEX_TAC` tactic is used, which likely involves analyzing the geometric properties of `std_octahedron` and its edges in relation to the vertices.
* This tactic may involve case analysis or leveraging properties of the `std_octahedron` to deduce the number of edges meeting at each vertex.

### Mathematical insight
This theorem provides insight into the geometric structure of the standard octahedron, specifically how many edges meet at each vertex. The standard octahedron is a regular polyhedron with 6 vertices and 12 edges, and understanding its local structure (like how many edges meet at a vertex) is crucial for various geometric and topological analyses.

### Dependencies
* `std_octahedron`
* `OCTAHEDRON_EDGES`
* `OCTAHEDRON_VERTICES`
* `face_of`
* `aff_dim`
* `SUBSET`
* `CARD`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the representation of geometric objects like the `std_octahedron` and the predicates `face_of` and `aff_dim`. Additionally, the `EDGES_PER_VERTEX_TAC` tactic might need to be reimplemented or replaced with equivalent tactics or strategies available in the target proof assistant, potentially involving geometric reasoning or case analysis tailored to the specific system's handling of geometric objects and predicates.

---

## DODECAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
DODECAHEDRON_EDGES_PER_VERTEX

### Type of the formal statement
Theorem

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
For all vertices `v` of the standard dodecahedron, if `v` is a face of the standard dodecahedron and the affine dimension of `v` is 0, then the cardinality of the set of edges `e` of the standard dodecahedron, where `e` is a face of the standard dodecahedron, the affine dimension of `e` is 1, and `v` is a subset of `e`, is equal to 3.

### Informal sketch
* The proof starts with the assumption that `v` is a vertex of the standard dodecahedron and has an affine dimension of 0.
* It then uses the `EDGES_PER_VERTEX_TAC` tactic to show that there are exactly 3 edges `e` of the standard dodecahedron that contain `v`.
* The tactic likely involves using the definitions of `STD_DODECAHEDRON`, `DODECAHEDRON_EDGES`, and `DODECAHEDRON_VERTICES` to derive the desired property.
* The key insight is that each vertex of the standard dodecahedron is incident to exactly 3 edges, which is a fundamental property of the dodecahedron's geometry.

### Mathematical insight
This theorem provides a fundamental property of the standard dodecahedron, which is a regular polyhedron with 12 pentagonal faces. The fact that each vertex is incident to exactly 3 edges is a consequence of the dodecahedron's symmetry and geometry. This property is important in various areas of mathematics, such as geometry, topology, and graph theory.

### Dependencies
* `STD_DODECAHEDRON`
* `DODECAHEDRON_EDGES`
* `DODECAHEDRON_VERTICES`
* `EDGES_PER_VERTEX_TAC`

### Porting notes
When porting this theorem to another proof assistant, it is essential to ensure that the definitions of `STD_DODECAHEDRON`, `DODECAHEDRON_EDGES`, and `DODECAHEDRON_VERTICES` are correctly translated. Additionally, the `EDGES_PER_VERTEX_TAC` tactic may need to be reimplemented or replaced with a similar tactic in the target system. The porting process may also require adjustments to handle differences in binder handling or automation between the source and target systems.

---

## ICOSAHEDRON_EDGES_PER_VERTEX

### Name of formal statement
ICOSAHEDRON_EDGES_PER_VERTEX

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ICOSAHEDRON_EDGES_PER_VERTEX = prove
 (`!v. v face_of std_icosahedron /\ aff_dim(v) = &0
       ==> CARD {e | e face_of std_icosahedron /\ aff_dim(e) = &1 /\
                     v SUBSET e} = 5`,
  EDGES_PER_VERTEX_TAC
    STD_ICOSAHEDRON ICOSAHEDRON_EDGES ICOSAHEDRON_VERTICES)
```

### Informal statement
For all vertices `v` of the `std_icosahedron`, if `v` has an affine dimension of 0, then the number of edges `e` of the `std_icosahedron` with an affine dimension of 1 that contain `v` is equal to 5.

### Informal sketch
* The proof starts with a universal quantification over all vertices `v` of the `std_icosahedron`.
* It then assumes that `v` has an affine dimension of 0, implying `v` is a point.
* The goal is to show that the cardinality of the set of edges `e` that are faces of the `std_icosahedron`, have an affine dimension of 1 (implying they are lines), and contain `v`, is equal to 5.
* The `EDGES_PER_VERTEX_TAC` tactic is used, which likely involves strategic application of geometric properties of the `std_icosahedron`, specifically leveraging `STD_ICOSAHEDRON`, `ICOSAHEDRON_EDGES`, and `ICOSAHEDRON_VERTICES` to derive the conclusion.

### Mathematical insight
This theorem provides insight into the geometric structure of the icosahedron, specifically that each vertex is shared by exactly 5 edges. This is a fundamental property of the icosahedron and is crucial in understanding its symmetry, connectivity, and overall geometric characteristics.

### Dependencies
* `STD_ICOSAHEDRON`
* `ICOSAHEDRON_EDGES`
* `ICOSAHEDRON_VERTICES`
* `EDGES_PER_VERTEX_TAC`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how the new system handles geometric objects and their properties, such as affine dimensions and subset relations. Additionally, the tactic `EDGES_PER_VERTEX_TAC` may need to be reimplemented or replaced with equivalent tactics or strategies available in the target system, potentially involving custom geometric reasoning or automation.

---

## MULTIPLE_COUNTING_LEMMA

### Name of formal statement
MULTIPLE_COUNTING_LEMMA

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT] THEN ARITH_TAC)
```

### Informal statement
For all relations `R` between sets `A` and `B`, and for all finite sets `s` in `A` and `t` in `B`, if for every `x` in `s`, the number of `y` in `t` such that `R x y` is `m`, and for every `y` in `t`, the number of `x` in `s` such that `R x y` is `n`, then `m` times the cardinality of `s` is equal to `n` times the cardinality of `t`.

### Informal sketch
* The proof starts by assuming the premises: `s` and `t` are finite, and the conditions on the relation `R` hold.
* It then applies the `NSUM_NSUM_RESTRICT` theorem, which is specialized for the relation `R`, the constant function `1`, and the sets `s` and `t`.
* The `ASM_SIMP_TAC` tactic is used to simplify the expression, utilizing the `NSUM_CONST` and `FINITE_RESTRICT` theorems.
* Finally, `ARITH_TAC` is applied to perform arithmetic manipulations, leading to the conclusion that `m * CARD s = n * CARD t`.
* The key insight is that the double counting of pairs `(x, y)` where `R x y` holds, once from the perspective of `s` and once from `t`, leads to the equality.

### Mathematical insight
This lemma provides a fundamental principle for counting, relating the number of elements in two sets and the number of relationships between them. It is crucial in various combinatorial and set-theoretic arguments, allowing for the derivation of equalities based on different perspectives of counting the same set of pairs. The lemma's importance lies in its ability to equate two different methods of counting, making it a useful tool in proofs involving finite sets and relations.

### Dependencies
* Theorems:
  * `NSUM_NSUM_RESTRICT`
  * `NSUM_CONST`
  * `FINITE_RESTRICT`
* Definitions:
  * `CARD` (cardinality of a set)
  * `FINITE` (finiteness of a set)

### Porting notes
When translating this lemma into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles finite sets, relations, and cardinalities. Specifically, the translation of `NSUM_NSUM_RESTRICT` and the treatment of `FINITE` and `CARD` will be critical. Additionally, the automation provided by `ARITH_TAC` in HOL Light might need to be manually replicated or replaced with equivalent tactics in the target system.

---

## SIZE_ZERO_DIMENSIONAL_FACES

### Name of formal statement
SIZE_ZERO_DIMENSIONAL_FACES

### Type of the formal statement
Theorem

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
    ASM_SIMP_TAC[FINITE_POLYHEDRON_EXTREME_POINTS] THEN SET_TAC[])
```

### Informal statement
For all sets $s$ in $\mathbb{R}^N$ that are polyhedra, the following statements hold: 
- The cardinality of the set of faces $f$ of $s$ with affine dimension $0$ is equal to the cardinality of the set of extreme points $v$ of $s$.
- The set of faces $f$ of $s$ with affine dimension $0$ is finite if and only if the set of extreme points $v$ of $s$ is finite.
- For all natural numbers $n$, the set of faces $f$ of $s$ with affine dimension $0$ has size $n$ if and only if the set of extreme points $v$ of $s$ has size $n$.

### Informal sketch
* The proof starts by assuming $s$ is a polyhedron and aims to establish three main equivalences between the set of zero-dimensional faces of $s$ and the set of extreme points of $s$.
* It uses a `SUBGOAL_THEN` tactic to establish that the set of zero-dimensional faces of $s$ can be represented as the image of the set of extreme points of $s$ under a function that maps each point to a singleton set containing that point.
* The proof then applies various theorems and tactics, including `SURJECTIVE_IMAGE_EQ`, `CARD_IMAGE_INJ`, `FINITE_IMAGE_INJ_EQ`, and `HAS_SIZE_IMAGE_INJ_EQ`, to establish the desired equivalences regarding cardinality, finiteness, and size.
* Key steps involve rewriting using `AFF_DIM_SING`, `FACE_OF_SING`, `IN_ELIM_THM`, and `AFF_DIM_EQ_0`, and applying `MESON_TAC` to derive conclusions from these rewrites.

### Mathematical insight
This theorem provides a deep connection between the geometric structure of a polyhedron (captured by its faces) and its combinatorial structure (captured by its extreme points). It shows that in a polyhedron, the zero-dimensional faces (which are essentially the vertices) are in a one-to-one correspondence with the extreme points, reflecting a fundamental relationship between geometric and algebraic representations of polyhedra.

### Dependencies
* Theorems:
  - `RIGHT_AND_FORALL_THM`
  - `SURJECTIVE_IMAGE_EQ`
  - `AFF_DIM_SING`
  - `FACE_OF_SING`
  - `IN_ELIM_THM`
  - `AFF_DIM_EQ_0`
  - `CARD_IMAGE_INJ`
  - `FINITE_IMAGE_INJ_EQ`
  - `HAS_SIZE_IMAGE_INJ_EQ`
* Definitions:
  - `polyhedron`
  - `face_of`
  - `aff_dim`
  - `extreme_point_of`
* Other:
  - `FINITE_POLYHEDRON_EXTREME_POINTS`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to how each system handles set comprehensions, image functions, and the interaction between geometric and combinatorial properties of polyhedra. The `SUBGOAL_THEN` and `SUBST1_TAC` tactics may need to be rephrased or restructured to fit the target system's tactic language. Additionally, ensuring that the target system's libraries include or can easily express the required theorems and definitions (e.g., `SURJECTIVE_IMAGE_EQ`, `AFF_DIM_SING`) will be crucial for a successful port.

---

## PLATONIC_SOLIDS_LIMITS

### Name of formal statement
PLATONIC_SOLIDS_LIMITS

### Type of the formal statement
Theorem

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
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC)
```

### Informal statement
For all polytopes `p` in 3-dimensional real space, if `p` has a certain property regarding the number of edges and vertices of its faces, then `p` must be one of five specific types of polyhedra: a tetrahedron, a cube, an octahedron, a dodecahedron, or an icosahedron.

### Informal sketch
* The proof starts with the `EULER_RELATION` theorem, which relates the number of vertices, edges, and faces of a polytope.
* It then applies the `MULTIPLE_COUNTING_LEMMA` to count the number of edges and vertices of the faces of `p`.
* The proof uses various properties of polytopes, such as `POLYTOPE_IMP_POLYHEDRON`, `FINITE_POLYTOPE_FACES`, and `FINITE_RESTRICT`, to establish the relationships between the number of edges, vertices, and faces.
* It also uses arithmetic properties, such as `ARITH_RULE` and `REAL_OF_NUM_EQ`, to perform calculations and establish inequalities.
* The proof then uses case analysis to consider different possibilities for the values of `m` and `n`, which represent the number of edges and vertices of the faces of `p`.
* In each case, the proof uses a combination of logical deductions, arithmetic calculations, and properties of polytopes to establish that `p` must be one of the five specified polyhedra.

### Mathematical insight
The theorem provides a classification of polytopes in 3-dimensional real space based on the number of edges and vertices of their faces. The proof relies on a combination of geometric and arithmetic properties of polytopes, and demonstrates the power of using formal proof assistants to establish complex mathematical results.

### Dependencies
* `EULER_RELATION`
* `MULTIPLE_COUNTING_LEMMA`
* `POLYTOPE_IMP_POLYHEDRON`
* `FINITE_POLYTOPE_FACES`
* `FINITE_RESTRICT`
* `ARITH_RULE`
* `REAL_OF_NUM_EQ`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the corresponding properties and lemmas are defined and proved correctly. In particular, the `EULER_RELATION` and `MULTIPLE_COUNTING_LEMMA` may need to be re-proved or re-defined in the target system. Additionally, the use of arithmetic properties and calculations may require careful attention to ensure that the results are correct and consistent with the target system's arithmetic libraries.

---

## PLATONIC_SOLIDS

### Name of formal statement
PLATONIC_SOLIDS

### Type of the formal statement
Theorem

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
For all integers `m` and `n`, there exists a polytope `p` in 3-dimensional real space such that `p` has affine dimension 3, and for every face `f` of `p` with affine dimension 2, the number of edges of `p` that are subsets of `f` is `m`, and for every vertex `v` of `p` with affine dimension 0, the number of edges of `p` that contain `v` is `n`, if and only if the pair `(m, n)` is one of the following: (3, 3), (4, 3), (3, 4), (5, 3), or (3, 5), which correspond to the tetrahedron, cube, octahedron, dodecahedron, and icosahedron, respectively.

### Informal sketch
* The proof involves showing that for each of the five platonic solids (tetrahedron, cube, octahedron, dodecahedron, and icosahedron), there exists a polytope `p` satisfying the given conditions.
* For each solid, the proof uses `EXISTS_TAC` to introduce a specific polytope (e.g., `std_tetrahedron`, `std_cube`, etc.) and then applies various rewriting and simplification tactics to establish the required properties.
* The `MATCH_MP_TAC` tactic is used to apply the `POLYTOPE_CONVEX_HULL` theorem, which is likely a key property of polytopes.
* The proof also relies on specific theorems about the number of edges per face and vertex for each platonic solid (e.g., `TETRAHEDRON_EDGES_PER_VERTEX`, `CUBE_EDGES_PER_FACE`, etc.).
* The use of `REPEAT GEN_TAC`, `EQ_TAC`, and `STRIP_TAC` suggests that the proof involves a combination of generalization, equivalence reasoning, and case analysis.

### Mathematical insight
This theorem provides a characterization of the platonic solids in terms of their combinatorial properties, specifically the number of edges per face and vertex. The result shows that these five solids are the only ones that satisfy certain simple and intuitive conditions, which makes them unique and important objects in geometry.

### Dependencies
* Theorems:
	+ `POLYTOPE_CONVEX_HULL`
	+ `LEFT_IMP_EXISTS_THM`
	+ `PLATONIC_SOLIDS_LIMITS`
	+ `TETRAHEDRON_EDGES_PER_VERTEX`
	+ `TETRAHEDRON_EDGES_PER_FACE`
	+ `CUBE_EDGES_PER_VERTEX`
	+ `CUBE_EDGES_PER_FACE`
	+ `OCTAHEDRON_EDGES_PER_VERTEX`
	+ `OCTAHEDRON_EDGES_PER_FACE`
	+ `DODECAHEDRON_EDGES_PER_VERTEX`
	+ `DODECAHEDRON_EDGES_PER_FACE`
	+ `ICOSAHEDRON_EDGES_PER_VERTEX`
	+ `ICOSAHEDRON_EDGES_PER_FACE`
* Definitions:
	+ `polytope`
	+ `aff_dim`
	+ `face_of`
	+ `std_tetrahedron`
	+ `std_cube`
	+ `std_octahedron`
	+ `std_dodecahedron`
	+ `std_icosahedron`

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
Two sets `s` and `t` of real-valued vectors are congruent if and only if there exists a constant vector `c` and an orthogonal transformation `f` such that `t` is the image of `s` under the transformation `x |-> c + f(x)`.

### Informal sketch
* The definition of congruence between two sets `s` and `t` involves the existence of a constant vector `c` and an orthogonal transformation `f`.
* The transformation `x |-> c + f(x)` is applied to each vector `x` in `s` to obtain the corresponding vector in `t`.
* The use of `orthogonal_transformation f` ensures that the transformation preserves certain geometric properties, such as lengths and angles.
* The `IMAGE` function is used to compute the image of `s` under the transformation.

### Mathematical insight
This definition captures the idea of two sets being equivalent up to rigid motions (translations and rotations) in Euclidean space. The orthogonal transformation `f` represents a rotation or reflection, while the constant vector `c` represents a translation. This concept is fundamental in geometry and is used to define equivalence classes of geometric objects.

### Dependencies
* `orthogonal_transformation`
* `IMAGE`

### Porting notes
When translating this definition to other proof assistants, care should be taken to ensure that the equivalent of `orthogonal_transformation` is defined and used correctly. Additionally, the `IMAGE` function may need to be replaced with an equivalent construct, such as a set comprehension or a mapping operation. In Lean, for example, the `image` function from the `set` module could be used.

---

## CONGRUENT_SIMPLE

### Name of formal statement
CONGRUENT_SIMPLE

### Type of the formal statement
Theorem

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
  ASM_SIMP_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; MATRIX_VECTOR_MUL_LINEAR])
```

### Informal statement
For all real 3x3 matrices A, if A is an orthogonal matrix and the image of the set s under the linear transformation defined by A is equal to the set t, then the convex hull of s is congruent to the convex hull of t.

### Informal sketch
* The proof begins by assuming the existence of an orthogonal matrix A and sets s and t such that the image of s under A is equal to t.
* It then uses the `CONVEX_HULL_LINEAR_IMAGE` and `MATRIX_VECTOR_MUL_LINEAR` theorems to simplify the expression for the convex hull of s and t.
* The `congruent` relation is then applied to show that the convex hulls are congruent.
* The proof uses the `ORTHOGONAL_TRANSFORMATION_MATRIX` property to establish that A preserves the geometric structure of the sets.
* The `MATRIX_OF_MATRIX_VECTOR_MUL` and `MATRIX_VECTOR_MUL_LINEAR` theorems are used to reason about the linear transformation defined by A.

### Mathematical insight
This theorem establishes a connection between the geometric properties of orthogonal matrices and the convex hulls of sets. It shows that if an orthogonal matrix maps one set to another, then the convex hulls of these sets are congruent, meaning they have the same shape and size. This result has implications for various areas of mathematics and computer science, including geometry, linear algebra, and optimization.

### Dependencies
* Theorems:
  * `CONVEX_HULL_LINEAR_IMAGE`
  * `MATRIX_VECTOR_MUL_LINEAR`
  * `ORTHOGONAL_TRANSFORMATION_MATRIX`
  * `MATRIX_OF_MATRIX_VECTOR_MUL`
  * `MATRIX_VECTOR_MUL_LINEAR`
* Definitions:
  * `orthogonal_matrix`
  * `convex hull`
  * `congruent`

### Porting notes
When translating this theorem to another proof assistant, pay attention to the handling of linear algebra and geometric concepts. The `ORTHOGONAL_TRANSFORMATION_MATRIX` property and the `CONVEX_HULL_LINEAR_IMAGE` theorem may require special care, as they rely on specific mathematical structures and properties. Additionally, the use of `EXISTS_TAC` and `ASM_SIMP_TAC` tactics may need to be adapted to the target system's proof scripting language.

---

## CONGRUENT_SEGMENTS

### Name of formal statement
CONGRUENT_SEGMENTS

### Type of the formal statement
Theorem

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
  ASM_MESON_TAC[LINEAR_SUB])
```

### Informal statement
For all real vectors `a`, `b`, `c`, and `d` in `ℝ^N`, if the distance between `a` and `b` is equal to the distance between `c` and `d`, then the line segment from `a` to `b` is congruent to the line segment from `c` to `d`.

### Informal sketch
* The proof starts by assuming `dist(a, b) = dist(c, d)`, which implies that the lengths of the two segments are equal.
* It then applies the `ORTHOGONAL_TRANSFORMATION_EXISTS` theorem to find an orthogonal transformation `f` that maps `b - a` to `d - c`.
* The transformation `f` is used to define a mapping from the segment `[a, b]` to the segment `[c, d]`.
* The proof then shows that this mapping is a congruence by verifying that it preserves the geometry of the segments, using properties of orthogonal transformations and linear maps.
* Key steps involve using `REWRITE_TAC` to apply definitions, `ASM_SIMP_TAC` to simplify using various theorems, and `AP_TERM_TAC` along with `BINOP_TAC` to reason about the preservation of geometric properties.

### Mathematical insight
This theorem is important because it establishes a fundamental property of geometric congruence in `ℝ^N`: that two line segments are congruent if and only if they have the same length. This property is crucial in geometry and is used extensively in various geometric constructions and proofs.

### Dependencies
* Theorems:
  + `ORTHOGONAL_TRANSFORMATION_EXISTS`
  + `CONVEX_HULL_LINEAR_IMAGE`
  + `SEGMENT_CONVEX_HULL`
  + `IMAGE_o`
  + `CONVEX_HULL_TRANSLATION`
  + `LINEAR_SUB`
* Definitions:
  + `dist`
  + `segment`
  + `congruent`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of vectors and orthogonal transformations. The `ORTHOGONAL_TRANSFORMATION_EXISTS` theorem, in particular, might require a different formulation or proof in other systems. Additionally, the use of `REPEAT STRIP_TAC` and other tactics may need to be adapted to the target system's proof scripting language.

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
               rand(concl dth)
```

### Informal statement
The function `compute_dist` takes two vectors `v1` and `v2` in 3-dimensional real space and computes the distance between them. It does this by first subtracting `v2` from `v1` to obtain a vector `vth`, and then computing the dot product of `vth` with itself. The result of this computation is the square of the distance between `v1` and `v2`.

### Informal sketch
* Define a subtraction operation `mk_sub` for vectors in 3-dimensional real space.
* Define the dot product operation `dot_tm` for vectors in 3-dimensional real space.
* Subtract `v2` from `v1` using `mk_sub` to obtain a vector `vth`.
* Compute the dot product of `vth` with itself using `dot_tm`.
* The result of this computation is the square of the distance between `v1` and `v2`.
Note that the `VECTOR3_SUB_CONV` and `VECTOR3_DOT_CONV` are used to apply the subtraction and dot product operations, respectively.

### Mathematical insight
The `compute_dist` function implements a standard method for computing the distance between two points in 3-dimensional space. The key idea is to use the dot product to compute the square of the distance, which can then be used to obtain the actual distance. This construction is important in many areas of mathematics and computer science, including geometry, physics, and computer graphics.

### Dependencies
* `mk_binop`
* `VECTOR3_SUB_CONV`
* `VECTOR3_DOT_CONV`
* `CONV_RULE`
* `RAND_CONV`
* `AP_TERM`
* `MK_COMB`

### Porting notes
When porting this definition to another proof assistant, note that the `VECTOR3_SUB_CONV` and `VECTOR3_DOT_CONV` may need to be replaced with equivalent constructions in the target system. Additionally, the `CONV_RULE` and `RAND_CONV` tactics may need to be replaced with similar tactics in the target system. The `AP_TERM` and `MK_COMB` functions are likely to have direct equivalents in other proof assistants.

---

## le_rat5

### Name of formal statement
le_rat5

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let le_rat5 =
  let mk_le = mk_binop `(<=):real->real->bool` and t_tm = `T` in
  fun r1 r2 -> rand(concl(REAL_RAT5_LE_CONV(mk_le r1 r2))) = t_tm
```

### Informal statement
The function `le_rat5` takes two real numbers `r1` and `r2` and returns a boolean value indicating whether the conclusion of the conversion `REAL_RAT5_LE_CONV` applied to the binary operation `(<=)` on `r1` and `r2` equals the term `T`, where `T` represents true.

### Informal sketch
* The definition involves creating a binary operation `(<=)` on real numbers, which is then used in the conversion `REAL_RAT5_LE_CONV`.
* This conversion is applied to the terms `r1` and `r2`, and the conclusion of this conversion is compared to the term `T` (representing true).
* The `mk_binop` and `mk_le` functions are used to construct the binary operation, and `rand` and `concl` are used to extract the conclusion from the conversion result.
* The `REAL_RAT5_LE_CONV` conversion is crucial in this definition, as it provides the core logic for comparing `r1` and `r2`.

### Mathematical insight
This definition provides a way to compare two real numbers using a specific conversion `REAL_RAT5_LE_CONV`, which is likely designed to handle rational numbers or a specific subset of real numbers. The comparison is done by applying this conversion and checking if the result equals the term `T`, indicating that the first number is less than or equal to the second.

### Dependencies
* `REAL_RAT5_LE_CONV`
* `mk_binop`
* `rand`
* `concl`

### Porting notes
When translating this definition into another proof assistant, special attention should be given to the `REAL_RAT5_LE_CONV` conversion, as its implementation might differ significantly between systems. Additionally, the handling of binary operations and the extraction of conclusions from conversions might require adjustments to match the target system's syntax and semantics.

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
  | _ -> failwith "three_adjacent_points: no points"
```

### Informal statement
The `three_adjacent_points` function takes a list `s` as input and returns three adjacent points. If the list `s` is non-empty, it selects the first point `x` and computes the distances from `x` to all other points in the list `t`. It then sorts these points based on their distances from `x` using the `le_rat5` comparison function and selects the two points `y` and `z` with the smallest distances. If the list `s` is empty, it raises an error.

### Informal sketch
* The function first checks if the input list `s` is non-empty.
* If `s` is non-empty, it extracts the first point `x` and the rest of the list `t`.
* It then computes the distances from `x` to all points in `t` using the `compute_dist` function and pairs each point with its distance.
* The points are sorted based on their distances using the `sort` function and the `le_rat5` comparison function.
* The function returns the three points `x`, `y`, and `z`, where `y` and `z` are the two points with the smallest distances from `x`.
* If the list `s` is empty, the function raises an error.

### Mathematical insight
The `three_adjacent_points` function is used to select three adjacent points from a list of points. The function uses the `compute_dist` function to compute the distances between points and the `le_rat5` comparison function to compare these distances. The function is likely used in a geometric or spatial context where the proximity of points is important.

### Dependencies
* `compute_dist`
* `le_rat5`
* `sort`
* `map`
* `failwith`

### Porting notes
When porting this definition to another proof assistant, note that the `failwith` function may need to be replaced with a similar error-handling mechanism. Additionally, the `le_rat5` comparison function and the `compute_dist` function may need to be defined or imported separately. The `sort` function and `map` function are likely available in other proof assistants, but may have different names or syntax.

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
           a33,a33_tm] pat_tm
```

### Informal statement
The function `mk_33matrix` takes nine real numbers `a11`, `a12`, `a13`, `a21`, `a22`, `a23`, `a31`, `a32`, `a33` and returns a 3x3 matrix where each element at position (i, j) is assigned the value of `aij`. This is achieved by substituting the input values into a pattern `pat_tm` representing a 3x3 matrix with placeholders for each element.

### Informal sketch
* Define a pattern for a 3x3 matrix with placeholders for each element
* Substitute the input real numbers into the pattern to create a concrete 3x3 matrix
* The `vsubst` function is used to perform the substitution of the input values into the pattern
* The resulting matrix is a `real^3^3` type, indicating a 3x3 matrix of real numbers

### Mathematical insight
This definition provides a way to construct a 3x3 matrix from nine real numbers, which is a fundamental data structure in linear algebra. The use of a pattern with placeholders allows for a concise and expressive definition.

### Dependencies
* `vsubst`
* `vector`
* `real`

### Porting notes
When porting this definition to other proof assistants, note that the `vsubst` function may need to be replaced with a similar substitution mechanism. Additionally, the `vector` type and `real` type may need to be defined or imported from a library. The overall structure of the definition should be preserved, but the specific syntax and tactics may vary depending on the target proof assistant.

---

## MATRIX_VECTOR_MUL_3

### Name of formal statement
MATRIX_VECTOR_MUL_3

### Type of the formal statement
Theorem

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
  REWRITE_TAC[DIMINDEX_3; FORALL_3; SUM_3; VECTOR_3])
```

### Informal statement
The theorem `MATRIX_VECTOR_MUL_3` states that for a 3x3 matrix represented as a vector of vectors `vector[vector[a11;a12;a13]; vector[a21; a22; a23]; vector[a31; a32; a33]]` and a 3-dimensional vector `vector[x1;x2;x3]`, their matrix multiplication is equal to the vector `vector[a11 * x1 + a12 * x2 + a13 * x3; a21 * x1 + a22 * x2 + a23 * x3; a31 * x1 + a32 * x2 + a33 * x3]`.

### Informal sketch
* The proof involves simplifying the expression for matrix-vector multiplication using `SIMP_TAC` with `CART_EQ`, `matrix_vector_mul`, and `LAMBDA_BETA`.
* It then applies `REWRITE_TAC` with several theorems (`DIMINDEX_3`, `FORALL_3`, `SUM_3`, `VECTOR_3`) to further simplify and prove the equality.

### Mathematical insight
This theorem formalizes the standard matrix-vector multiplication in linear algebra, which is a fundamental operation in many mathematical and computational contexts. It's crucial for various applications, including solving systems of linear equations, linear transformations, and more.

### Dependencies
* `CART_EQ`
* `matrix_vector_mul`
* `LAMBDA_BETA`
* `DIMINDEX_3`
* `FORALL_3`
* `SUM_3`
* `VECTOR_3`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles matrix and vector operations, as well as the specific tactics and theorems used for simplification and rewriting. Differences in the underlying logic or the way binders are handled may require adjustments to the proof strategy.

---

## MATRIX_LEMMA

### Name of formal statement
MATRIX_LEMMA

### Type of the formal statement
Theorem

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
  REWRITE_TAC[FORALL_3; DIMINDEX_3; VECTOR_3; SUM_3] THEN REAL_ARITH_TAC)
```

### Informal statement
For all real 3x3 matrices A, the following statements are equivalent: 
1. A times the vector (x1, y1, z1) equals the vector (x2, y2, z2), 
2. the dot product of (x1, y1, z1) with the first row of A equals (x2$1, y2$1, z2$1), 
the dot product of (x1, y1, z1) with the second row of A equals (x2$2, y2$2, z2$2), and 
the dot product of (x1, y1, z1) with the third row of A equals (x2$3, y2$3, z2$3).

### Informal sketch
* The proof starts by applying `SIMP_TAC` to simplify the statement using various theorems such as `CART_EQ`, `transp`, `matrix_vector_mul`, `row`, `VECTOR_3`, and `LAMBDA_BETA`.
* It then applies `REWRITE_TAC` to rewrite the statement using `FORALL_3`, `DIMINDEX_3`, `VECTOR_3`, and `SUM_3`.
* Finally, it uses `REAL_ARITH_TAC` to perform real arithmetic and complete the proof.
* The key steps involve simplifying the matrix-vector multiplication and using properties of vectors and matrices to establish the equivalence.

### Mathematical insight
This theorem provides a way to relate matrix-vector multiplication to the dot product of vectors with rows of the matrix. It is essential in linear algebra and has numerous applications in various fields, including computer graphics, physics, and engineering. The theorem is important because it allows for the decomposition of matrix-vector multiplication into simpler dot product operations, which can be more easily computed and analyzed.

### Dependencies
* Theorems: 
  * `CART_EQ`
  * `transp`
  * `matrix_vector_mul`
  * `row`
  * `VECTOR_3`
  * `LAMBDA_BETA`
  * `FORALL_3`
  * `DIMINDEX_3`
  * `SUM_3`
* Definitions: 
  * `real^3^3` (type of 3x3 real matrices)
  * `vector` (constructor for vectors)
  * `row` (function to extract a row from a matrix)

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of matrix-vector multiplication, vector operations, and real arithmetic. The `SIMP_TAC`, `REWRITE_TAC`, and `REAL_ARITH_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target system. Additionally, the dependencies listed above should be ported or proven in the target system before attempting to port this theorem.

---

## MATRIX_BY_CRAMER_LEMMA

### Name of formal statement
MATRIX_BY_CRAMER_LEMMA

### Type of the formal statement
Theorem

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
  SIMP_TAC[LAMBDA_BETA] THEN REWRITE_TAC[DIMINDEX_3; FORALL_3])
```

### Informal statement
For all real 3x3 matrices A, if the determinant of the matrix formed by vectors x1, y1, and z1 is not zero, then the following equivalence holds: A times x1 equals x2, A times y1 equals y2, and A times z1 equals z2 if and only if A is equal to a specific lambda function that involves the determinants of matrices constructed from x1, y1, z1, x2, y2, and z2.

### Informal sketch
* The proof starts by assuming the determinant of the matrix formed by vectors x1, y1, and z1 is non-zero.
* It then applies the `MATRIX_LEMMA` to rewrite the matrix equations in terms of the lambda function.
* The `CRAMER` rule is used to simplify the expressions involving determinants.
* The proof then uses `CART_EQ` and `row` to manipulate the matrix equations and apply `LAMBDA_BETA` to simplify the lambda function.
* Finally, `DIMINDEX_3` and `FORALL_3` are used to conclude the proof.

### Mathematical insight
This theorem provides a way to express a matrix A in terms of its action on certain vectors, using Cramer's rule to solve a system of linear equations. The key idea is to use the determinants of matrices constructed from the given vectors to define the lambda function that represents the matrix A.

### Dependencies
* Theorems:
  * `MATRIX_LEMMA`
  * `CRAMER`
* Definitions:
  * `CART_EQ`
  * `row`
  * `LAMBDA_BETA`
  * `DIMINDEX_3`
  * `FORALL_3`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of lambda functions and matrix operations. The `CART_EQ` and `row` definitions may need to be adjusted to match the target system's representation of matrices. Additionally, the `CRAMER` rule and `MATRIX_LEMMA` may require reimplementation or replacement with equivalent constructs in the target system.

---

## MATRIX_BY_CRAMER

### Name of formal statement
MATRIX_BY_CRAMER

### Type of the formal statement
Theorem

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
  REWRITE_TAC[FORALL_3; ARITH; VECTOR_3] THEN REWRITE_TAC[CONJ_ACI])
```

### Informal statement
For all real 3x3 matrices `A` and vectors `x1`, `y1`, `z1`, `x2`, `y2`, `z2`, if the determinant `d` of the matrix formed by `x1`, `y1`, `z1` is non-zero, then the following equivalence holds: `A` times `x1` equals `x2`, `A` times `y1` equals `y2`, and `A` times `z1` equals `z2` if and only if the elements of `A` can be expressed as specific rational functions of the components of `x1`, `y1`, `z1`, `x2`, `y2`, `z2`, and `d`. These rational functions involve products and differences of the components, divided by the determinant `d`.

### Informal sketch
* The proof starts by assuming the non-zero determinant condition.
* It then applies various simplification and rewriting tactics, including `GEN_TAC`, `CONV_TAC`, `DISCH_TAC`, `ASM_SIMP_TAC`, `REWRITE_TAC`, and `SIMP_TAC`, to manipulate the expressions and apply relevant lemmas such as `MATRIX_BY_CRAMER_LEMMA`.
* Key steps involve using properties of determinants (`DET_3`), Cartesian equality (`CART_EQ`), lambda beta reduction (`LAMBDA_BETA`), and arithmetic properties (`ARITH`).
* The proof also involves rewriting expressions using `FORALL_3`, `VECTOR_3`, and `CONJ_ACI` to ultimately establish the desired equivalence.

### Mathematical insight
This theorem provides a method for finding the elements of a 3x3 matrix `A` given its action on three vectors `x1`, `y1`, `z1` and their images `x2`, `y2`, `z2`, provided that the determinant of the matrix formed by `x1`, `y1`, `z1` is non-zero. This is essentially an application of Cramer's rule for solving systems of linear equations, adapted to the context of matrix multiplication and vector transformations.

### Dependencies
#### Theorems
* `MATRIX_BY_CRAMER_LEMMA`
#### Definitions
* `DET_3`
* `CART_EQ`
* `LAMBDA_BETA`
* `DIMINDEX_3`
* `ARITH`
* `VECTOR_3`
* `FORALL_3`
* `CONJ_ACI`

---

## CONGRUENT_EDGES_TAC

### Name of formal statement
CONGRUENT_EDGES_TAC

### Type of the formal statement
Theorem/tactic

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
  REWRITE_TAC[]
```

### Informal statement
The tactic `CONGRUENT_EDGES_TAC` takes a set of edges as input and applies a series of rewriting and simplification steps to prove a statement about congruent edges. The steps involve rewriting implications and conjunctions, stripping away unnecessary assumptions, and applying properties of segments, distance, and vector operations.

### Informal sketch
* The proof starts by rewriting implications and conjunctions using `REWRITE_TAC` with `IMP_CONJ` and `RIGHT_FORALL_IMP_THM`.
* It then applies `REWRITE_TAC` with `IMP_IMP` to further simplify the statement.
* The tactic `REWRITE_TAC` is applied again with the input `edges` to incorporate the edge information into the proof.
* The `REPEAT STRIP_TAC` is used to remove any unnecessary assumptions.
* The `ASM_REWRITE_TAC` with `GSYM SEGMENT_CONVEX_HULL` is applied to utilize properties of segment convex hulls.
* The `MATCH_MP_TAC` with `CONGRUENT_SEGMENTS` is used to apply a theorem about congruent segments.
* Further simplifications are made using `REWRITE_TAC` with `DIST_EQ`, `dist`, and `NORM_POW_2` to apply distance and vector properties.
* The `CONV_TAC` with various conversion functions (`VECTOR3_SUB_CONV`, `VECTOR3_DOT_CONV`, `REAL_RAT5_EQ_CONV`) is applied to perform specific conversions and simplifications.
* Finally, a last `REWRITE_TAC` is applied to finalize the proof.

### Mathematical insight
The `CONGRUENT_EDGES_TAC` tactic is designed to prove statements about congruent edges in a geometric context, leveraging properties of segments, distances, and vector operations. This tactic is likely used in geometric or spatial reasoning applications, where proving congruence of edges is a critical step in establishing geometric relationships.

### Dependencies
* Theorems:
  - `IMP_CONJ`
  - `RIGHT_FORALL_IMP_THM`
  - `IMP_IMP`
  - `CONGRUENT_SEGMENTS`
  - `DIST_EQ`
* Definitions:
  - `dist`
  - `NORM_POW_2`
  - `VECTOR3_SUB_CONV`
  - `VECTOR3_DOT_CONV`
  - `REAL_RAT5_EQ_CONV`
  - `SEGMENT_CONVEX_HULL`

### Porting notes
When porting this tactic to another proof assistant, special attention should be given to the conversion functions (`VECTOR3_SUB_CONV`, `VECTOR3_DOT_CONV`, `REAL_RAT5_EQ_CONV`) as they may need to be reimplemented or replaced with equivalent functions in the target system. Additionally, the `REPEAT STRIP_TAC` and `ASM_REWRITE_TAC` may need to be adjusted based on the target system's handling of assumptions and rewriting.

---

## CONGRUENT_FACES_TAC

### Name of formal statement
CONGRUENT_FACES_TAC

### Type of the formal statement
Theorem/Tactic

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
The `CONGRUENT_FACES_TAC` is a tactic that proves a statement about congruent faces of a geometric object, utilizing various rewriting and simplification steps to derive the conclusion. The statement involves the application of several theorems and definitions, including `IMP_CONJ`, `RIGHT_FORALL_IMP_THM`, `IMP_IMP`, and `CONGRUENT_SIMPLE`, among others, to establish the congruence of faces based on certain conditions.

### Informal sketch
* The tactic starts by applying `REWRITE_TAC` with several theorems to simplify the goal.
* It then applies `REPEAT STRIP_TAC` and `ASM_REWRITE_TAC` to further simplify and rearrange the terms.
* The tactic uses a function `W` to apply a series of conversion rules, including `DEPTH_CONV` and `ONCE_DEPTH_CONV`, with various conversion functions such as `REAL_RAT5_MUL_CONV`, `REAL_RAT5_ADD_CONV`, and `REAL_RAT5_EQ_CONV`, to manipulate and simplify the expressions.
* It then uses `MATCH_MP_TAC` with `CONGRUENT_SIMPLE` to establish the congruence of faces, and `EXISTS_TAC` to introduce a matrix `matt` constructed from the terms.
* The tactic concludes by applying `CONJ_TAC` and then two separate branches of rewriting and simplification using `REWRITE_TAC` and `CONV_TAC` with various theorems and conversion functions.

### Mathematical insight
The `CONGRUENT_FACES_TAC` tactic is designed to prove statements about the congruence of faces in geometric objects, which is a fundamental concept in geometry and computer-aided design. The tactic leverages various mathematical theorems and definitions to establish the congruence of faces based on certain conditions, providing a powerful tool for reasoning about geometric objects.

### Dependencies
* Theorems:
  + `IMP_CONJ`
  + `RIGHT_FORALL_IMP_THM`
  + `IMP_IMP`
  + `CONGRUENT_SIMPLE`
  + `MATRIX_BY_CRAMER`
  + `VECTOR_3`
  + `DET_3`
  + `ORTHOGONAL_MATRIX`
  + `CART_EQ`
  + `IMAGE_CLAUSES`
  + `MATRIX_VECTOR_MUL_3`
* Definitions:
  + `three_adjacent_points`
  + `dest_setenum`
  + `mk_33matrix`
* Conversion functions:
  + `REAL_RAT5_MUL_CONV`
  + `REAL_RAT5_ADD_CONV`
  + `REAL_RAT5_EQ_CONV`
  + `let_CONV`

### Porting notes
When porting this tactic to another proof assistant, special attention should be paid to the handling of rewriting and simplification rules, as well as the application of conversion functions. The `W` function and its application of various conversion rules may require careful translation, and the use of `MATCH_MP_TAC` and `EXISTS_TAC` may need to be adapted to the target proof assistant's tactic language. Additionally, the dependencies listed above will need to be ported or reimplemented in the target system.

---

## TETRAHEDRON_CONGRUENT_EDGES

### Name of formal statement
TETRAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TETRAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_tetrahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_tetrahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC TETRAHEDRON_EDGES);;
```

### Informal statement
For all `e1` and `e2`, if `e1` is a face of the standard tetrahedron and the affine dimension of `e1` is 1, and `e2` is a face of the standard tetrahedron and the affine dimension of `e2` is 1, then `e1` is congruent to `e2`.

### Informal sketch
* The proof involves showing that any two edges (`e1` and `e2`) of the standard tetrahedron are congruent.
* It utilizes the `CONGRUENT_EDGES_TAC` tactic, which likely applies a congruence theorem or lemma to establish the congruence of edges based on the properties of the tetrahedron.
* The key step is recognizing that all edges of a regular tetrahedron have the same length, thus any two edges are congruent.
* The use of `TETRAHEDRON_EDGES` suggests that there is a predefined property or theorem about the edges of the tetrahedron being used in the proof.

### Mathematical insight
This theorem is important because it establishes a fundamental property of regular tetrahedra: all their edges have the same length. This property is crucial in geometry and is used in various proofs and constructions involving tetrahedra. The theorem provides a formal guarantee that can be used in more complex geometric arguments.

### Dependencies
* `std_tetrahedron`
* `face_of`
* `aff_dim`
* `congruent`
* `CONGRUENT_EDGES_TAC`
* `TETRAHEDRON_EDGES`

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to how edges and faces of geometric objects are represented and how congruence is defined. The `CONGRUENT_EDGES_TAC` tactic might not have a direct equivalent, so understanding its purpose and replicating its effect using the target system's tactics or lemmas will be necessary. Additionally, ensuring that the standard tetrahedron and its properties are defined and accessible in the new system is crucial.

---

## TETRAHEDRON_CONGRUENT_FACETS

### Name of formal statement
TETRAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TETRAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_tetrahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_tetrahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC TETRAHEDRON_FACETS);;
```

### Informal statement
For all faces `f1` and `f2` of the standard tetrahedron, if `f1` is a face of the standard tetrahedron and has affine dimension 2, and `f2` is a face of the standard tetrahedron and has affine dimension 2, then `f1` is congruent to `f2`.

### Informal sketch
* The proof involves showing that any two 2-dimensional faces `f1` and `f2` of the standard tetrahedron are congruent.
* The `CONGRUENT_FACES_TAC` tactic is used with `TETRAHEDRON_FACETS` to establish this congruence.
* The key idea is to apply the tactic to the faces of the standard tetrahedron, leveraging the properties of these faces to demonstrate congruence.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard tetrahedron, namely that all its 2-dimensional faces are congruent. This is a basic geometric fact that can be used as a building block for more complex proofs about tetrahedra and their properties.

### Dependencies
* `face_of`
* `std_tetrahedron`
* `aff_dim`
* `congruent`
* `CONGRUENT_FACES_TAC`
* `TETRAHEDRON_FACETS`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how faces and congruence are defined and handled. The `CONGRUENT_FACES_TAC` tactic may not have a direct equivalent, so it may be necessary to recreate its functionality using the target system's tactics and rules. Additionally, ensure that the standard tetrahedron and its properties are defined and accessible in the target system.

---

## CUBE_CONGRUENT_EDGES

### Name of formal statement
CUBE_CONGRUENT_EDGES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CUBE_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_cube /\ aff_dim e1 = &1 /\
           e2 face_of std_cube /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC CUBE_EDGES);;
```

### Informal statement
For all `e1` and `e2`, if `e1` is a face of the standard cube and the affine dimension of `e1` is 1, and `e2` is a face of the standard cube and the affine dimension of `e2` is 1, then `e1` is congruent to `e2`.

### Informal sketch
* The proof involves showing that any two edges `e1` and `e2` of the standard cube `std_cube` are congruent, given that both have an affine dimension of 1.
* The `CONGRUENT_EDGES_TAC` tactic is applied to `CUBE_EDGES` to establish this congruence.
* The key insight is recognizing that all edges of a cube are congruent, which is a fundamental geometric property.
* This involves understanding the definition of `face_of`, `aff_dim`, and `congruent` in the context of the `std_cube`.

### Mathematical insight
This theorem captures a basic geometric property of cubes, specifically that all their edges are of equal length and thus congruent. This is crucial in various geometric and topological proofs involving cubes, as it allows for the generalization of properties across all edges without needing to consider each individually.

### Dependencies
* `std_cube`
* `face_of`
* `aff_dim`
* `congruent`
* `CONGRUENT_EDGES_TAC`
* `CUBE_EDGES`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles geometric definitions and proofs, especially regarding congruence and affine dimensions. The tactic `CONGRUENT_EDGES_TAC` might need to be replicated or its functionality achieved through a combination of tactics or built-in support for geometric reasoning in the target system.

---

## CUBE_CONGRUENT_FACETS

### Name of formal statement
CUBE_CONGRUENT_FACETS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CUBE_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_cube /\ aff_dim f1 = &2 /\
           f2 face_of std_cube /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC CUBE_FACETS);;
```

### Informal statement
For all `f1` and `f2`, if `f1` is a face of the standard cube and the affine dimension of `f1` is 2, and `f2` is a face of the standard cube and the affine dimension of `f2` is 2, then `f1` is congruent to `f2`.

### Informal sketch
* The proof starts by assuming `f1` and `f2` are faces of the standard cube with affine dimension 2.
* It then applies the `CONGRUENT_FACES_TAC` tactic with `CUBE_FACETS` to establish the congruence between `f1` and `f2`.
* The key idea is to use the properties of the standard cube and its faces to show that any two 2-dimensional faces are congruent.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard cube, namely that all its 2-dimensional faces are congruent. This property is crucial in various geometric and topological contexts, such as in the study of symmetries and transformations of the cube.

### Dependencies
* `face_of`
* `std_cube`
* `aff_dim`
* `congruent`
* `CONGRUENT_FACES_TAC`
* `CUBE_FACETS`

### Porting notes
When porting this theorem to another proof assistant, note that the `CONGRUENT_FACES_TAC` tactic may not have a direct equivalent. Instead, the porter may need to use a combination of tactics or lemmas to establish the congruence between `f1` and `f2`. Additionally, the definition of `std_cube` and the properties of its faces may need to be adapted to the target system.

---

## OCTAHEDRON_CONGRUENT_EDGES

### Name of formal statement
OCTAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OCTAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_octahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_octahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC OCTAHEDRON_EDGES);;
```

### Informal statement
For all edges `e1` and `e2`, if `e1` is a face of the standard octahedron and the affine dimension of `e1` is 1, and `e2` is a face of the standard octahedron and the affine dimension of `e2` is 1, then `e1` is congruent to `e2`.

### Informal sketch
* The proof involves showing that any two edges of the standard octahedron are congruent.
* It uses the `CONGRUENT_EDGES_TAC` tactic, which suggests a strategy of proving congruence by identifying and applying relevant geometric properties of the octahedron's edges.
* The key step likely involves leveraging the definition of `std_octahedron` and properties of its faces and edges, possibly including the `OCTAHEDRON_EDGES` definition.

### Mathematical insight
This theorem is important because it establishes a fundamental geometric property of the standard octahedron, specifically that all its edges are of equal length, which is a characteristic feature of regular polyhedra. Understanding and proving such properties is crucial in geometry and can have implications for various areas of mathematics and computer science, such as graph theory, combinatorics, and computational geometry.

### Dependencies
* `std_octahedron`
* `face_of`
* `aff_dim`
* `congruent`
* `OCTAHEDRON_EDGES`
* `CONGRUENT_EDGES_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how edges and faces of polyhedra are represented and how congruence between geometric objects is defined and proven. The `CONGRUENT_EDGES_TAC` tactic may not have a direct equivalent, so understanding its purpose and replicating its effect using the target system's tactics or proof strategies will be necessary. Additionally, ensure that the ported version correctly captures the quantification over edges and the conditions imposed by the affine dimension and face membership.

---

## OCTAHEDRON_CONGRUENT_FACETS

### Name of formal statement
OCTAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let OCTAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_octahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_octahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC OCTAHEDRON_FACETS);;
```

### Informal statement
For all faces `f1` and `f2` of the standard octahedron, if `f1` is a face of the standard octahedron and has affine dimension 2, and `f2` is a face of the standard octahedron and has affine dimension 2, then `f1` is congruent to `f2`.

### Informal sketch
* The proof involves showing that any two 2-dimensional faces of the standard octahedron are congruent.
* The `CONGRUENT_FACES_TAC` tactic is used, which suggests that the proof relies on properties of congruent faces, specifically those defined in `OCTAHEDRON_FACETS`.
* The main logical stage is to establish that all faces of the standard octahedron with affine dimension 2 have the same shape and size, hence are congruent.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard octahedron, namely that all its 2-dimensional faces are congruent. This is a key insight in geometry, as it implies that the octahedron has a high degree of symmetry.

### Dependencies
* `face_of`
* `std_octahedron`
* `aff_dim`
* `congruent`
* `OCTAHEDRON_FACETS`
* `CONGRUENT_FACES_TAC`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the notion of congruence and affine dimension are defined and handled correctly. Additionally, the `CONGRUENT_FACES_TAC` tactic may need to be replaced with a similar tactic or a manual proof, depending on the capabilities of the target proof assistant.

---

## DODECAHEDRON_CONGRUENT_EDGES

### Name of formal statement
DODECAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DODECAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_dodecahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_dodecahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC DODECAHEDRON_EDGES);;
```

### Informal statement
For all edges `e1` and `e2`, if `e1` is a face of the standard dodecahedron and the affine dimension of `e1` is 1, and `e2` is a face of the standard dodecahedron and the affine dimension of `e2` is 1, then `e1` is congruent to `e2`.

### Informal sketch
* The proof starts by assuming `e1` and `e2` are edges of the standard dodecahedron with affine dimension 1.
* It then applies the `CONGRUENT_EDGES_TAC` tactic with `DODECAHEDRON_EDGES` to establish the congruence of `e1` and `e2`.
* The key insight is that all edges of a regular dodecahedron are congruent, which is a geometric property that can be leveraged to prove this statement.

### Mathematical insight
This theorem captures a fundamental geometric property of a regular dodecahedron, which is that all its edges are congruent. This property is crucial in geometry and is often used in proofs involving the symmetries and structures of polyhedra.

### Dependencies
* `std_dodecahedron`
* `face_of`
* `aff_dim`
* `congruent`
* `CONGRUENT_EDGES_TAC`
* `DODECAHEDRON_EDGES`

### Porting notes
When porting this theorem to another proof assistant, ensure that the representation of the standard dodecahedron, the notion of face, affine dimension, and congruence are defined and aligned with the target system. The `CONGRUENT_EDGES_TAC` tactic might need to be reimplemented or replaced with an equivalent tactic in the target system, taking into account how that system handles geometric proofs and edge congruence.

---

## DODECAHEDRON_CONGRUENT_FACETS

### Name of formal statement
DODECAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DODECAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_dodecahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_dodecahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC DODECAHEDRON_FACETS);;
```

### Informal statement
For all `f1` and `f2`, if `f1` is a face of the standard dodecahedron and the affine dimension of `f1` is 2, and `f2` is a face of the standard dodecahedron and the affine dimension of `f2` is 2, then `f1` is congruent to `f2`.

### Informal sketch
* The proof involves showing that any two 2-dimensional faces of the standard dodecahedron are congruent.
* The `CONGRUENT_FACES_TAC` tactic is used to establish this congruence, relying on the properties of the `std_dodecahedron` and its faces as defined in `DODECAHEDRON_FACETS`.
* The key step is recognizing that all faces of the standard dodecahedron have the same geometric properties, which allows for the application of `CONGRUENT_FACES_TAC` to prove their congruence.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard dodecahedron, namely that all its 2-dimensional faces are congruent. This property is crucial in geometry and can be used in various proofs and constructions involving the dodecahedron.

### Dependencies
* `std_dodecahedron`
* `face_of`
* `aff_dim`
* `congruent`
* `DODECAHEDRON_FACETS`
* `CONGRUENT_FACES_TAC`

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to the handling of geometric objects and their properties, such as faces and affine dimensions. The `CONGRUENT_FACES_TAC` tactic may not have a direct equivalent, so the underlying mathematical reasoning and geometric properties used in the proof should be carefully translated.

---

## ICOSAHEDRON_CONGRUENT_EDGES

### Name of formal statement
ICOSAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ICOSAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_icosahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_icosahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC ICOSAHEDRON_EDGES);;
```

### Informal statement
For all edges `e1` and `e2`, if `e1` is a face of the standard icosahedron and the affine dimension of `e1` is 1, and `e2` is a face of the standard icosahedron and the affine dimension of `e2` is 1, then `e1` is congruent to `e2`.

### Informal sketch
* The proof starts by assuming `e1` and `e2` are edges of the standard icosahedron with affine dimension 1.
* It then applies the `CONGRUENT_EDGES_TAC` tactic to establish congruence between `e1` and `e2`, utilizing the `ICOSAHEDRON_EDGES` theorem.
* The key logical stage involves recognizing that all edges of the standard icosahedron, by definition, have the same properties and dimensions, which allows for the application of congruence.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard icosahedron, specifically that all its edges are congruent. This property is crucial in geometry and is used in various proofs and constructions involving the icosahedron, showcasing its symmetry and regularity.

### Dependencies
* `std_icosahedron`
* `face_of`
* `aff_dim`
* `congruent`
* `ICOSAHEDRON_EDGES`
* `CONGRUENT_EDGES_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles geometric objects and their properties, such as the definition of the standard icosahedron and the concept of congruence. Additionally, the tactic `CONGRUENT_EDGES_TAC` might need to be replicated or replaced with equivalent tactics or strategies available in the target system.

---

## ICOSAHEDRON_CONGRUENT_FACETS

### Name of formal statement
ICOSAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ICOSAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_icosahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_icosahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC ICOSAHEDRON_FACETS);;
```

### Informal statement
For all faces `f1` and `f2` of the standard icosahedron, if `f1` is a face of the standard icosahedron and has affine dimension 2, and `f2` is also a face of the standard icosahedron with affine dimension 2, then `f1` is congruent to `f2`.

### Informal sketch
* The proof starts by assuming `f1` and `f2` are faces of the `std_icosahedron` with affine dimension 2.
* It then applies the `CONGRUENT_FACES_TAC` tactic with `ICOSAHEDRON_FACETS` to establish the congruence of `f1` and `f2`.
* The key insight is that all faces of the standard icosahedron with affine dimension 2 are congruent, which is facilitated by the `CONGRUENT_FACES_TAC` tactic.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the standard icosahedron, namely that all its two-dimensional faces are congruent. This property is crucial in geometry and can be used in various proofs and constructions involving the icosahedron.

### Dependencies
* `std_icosahedron`
* `face_of`
* `aff_dim`
* `congruent`
* `ICOSAHEDRON_FACETS`
* `CONGRUENT_FACES_TAC`

### Porting notes
When porting this theorem to another proof assistant, ensure that the equivalent of `CONGRUENT_FACES_TAC` is available or can be implemented. Additionally, the representation of the standard icosahedron and its faces may need to be adapted to the target system. Pay attention to how affine dimension and congruence are handled in the target system, as these concepts may be represented differently.

---

