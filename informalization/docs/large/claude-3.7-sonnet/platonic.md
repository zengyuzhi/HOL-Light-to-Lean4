# platonic.ml

## Overview

Number of statements: 91

This file formalizes the proof that exactly five Platonic solids (regular convex polyhedra) exist in three-dimensional Euclidean space. It builds upon the polyhedron theory and cross product operations to establish the necessary conditions for regular polyhedra and proves both the existence of the five classic solids (tetrahedron, cube, octahedron, dodecahedron, and icosahedron) and the impossibility of any others. The file completes a significant result in classical geometry using the formal framework of HOL Light.

## std_tetrahedron

I'll revise the documentation to correct the inaccuracy about the distance from vertices to the origin.

### std_tetrahedron
- `std_tetrahedron`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let std_tetrahedron = new_definition
 `std_tetrahedron =
     convex hull
       {vector[&1;&1;&1],vector[-- &1;-- &1;&1],
        vector[-- &1;&1;-- &1],vector[&1;-- &1;-- &1]}:real^3->bool`;;
```

### Informal statement
The standard tetrahedron `std_tetrahedron` is defined as the convex hull of four points in $\mathbb{R}^3$:
$$\text{std\_tetrahedron} = \text{conv}\{(1,1,1), (-1,-1,1), (-1,1,-1), (1,-1,-1)\}$$

This defines a regular tetrahedron centered at the origin with its vertices at distance $\sqrt{3}$ from the origin.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
The standard tetrahedron is one of the five Platonic solids, characterized by four congruent equilateral triangular faces, four vertices, and six edges. This particular definition places the tetrahedron in a standard position in $\mathbb{R}^3$ with the origin at its center and its vertices equidistant from the origin.

The coordinates are chosen to make the tetrahedron symmetric about the origin. Each vertex has coordinates that are either 1 or -1 in each dimension, and the sum of coordinates for each vertex is either 1 or -1, creating a uniform structure where all vertices are at distance $\sqrt{3}$ from the origin.

This is the first of the five Platonic solids (tetrahedron, cube, octahedron, dodecahedron, and icosahedron) being defined in this section of the formalization.

### Dependencies
- Definitions:
  - No explicit dependencies are listed for the definition itself, though it implicitly depends on:
    - `convex hull`: The operation that creates the convex hull of a set of points
    - `vector`: The constructor for vectors in HOL Light

### Porting notes
When porting this definition to another system:
1. Ensure that the target system has a well-defined notion of convex hulls in Euclidean space
2. Verify that the vector notation in the target system can properly represent the four vertices
3. Some systems might use different syntax for real numbers (e.g., `&1` in HOL Light corresponds to `1` or `1.0` in other systems)
4. The type annotation `:real^3->bool` indicates that the result is a set of vectors in $\mathbb{R}^3$, which may need to be represented differently in other systems

---

## std_cube

### std_cube
- `std_cube`

### Type of the formal statement
- new_definition

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
The standard cube in $\mathbb{R}^3$ is defined as the convex hull of the eight vertices $\{\pm 1, \pm 1, \pm 1\}$, where each vertex has coordinates that are either $1$ or $-1$ in each dimension. Specifically:

$\text{std\_cube} = \text{conv}\{(1,1,1), (1,1,-1), (1,-1,1), (1,-1,-1), (-1,1,1), (-1,1,-1), (-1,-1,1), (-1,-1,-1)\} \subset \mathbb{R}^3$

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
The standard cube is a foundational geometric object in three-dimensional space. It's defined as the convex hull of the eight corners of a cube centered at the origin with side length 2. This representation makes it convenient for studying properties of regular polyhedra and for proving theorems about three-dimensional geometric objects.

The standard cube has several important properties:
- It is centered at the origin
- It has side length 2 (each coordinate ranges from -1 to 1)
- It is a regular polyhedron with 8 vertices, 12 edges, and 6 faces
- It is highly symmetric, exhibiting the full octahedral symmetry group

This definition provides a standard reference object for studying three-dimensional geometry in HOL Light, particularly in the context of convex geometry and polyhedra.

### Dependencies
- Definitions:
  - `convex hull` - The convex hull operation
  - `vector` - Vector construction in HOL Light

### Porting notes
When porting this definition:
- Ensure the target system has a suitable definition of convex hull
- Verify the representation of real numbers and vectors in the target system
- Note that HOL Light uses `&1` for the numeral 1 as a real number, which might be represented differently in other systems
- The type annotation `:real^3->bool` indicates that this is a predicate on three-dimensional vectors

---

## std_octahedron

### std_octahedron
- `std_octahedron`

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
The standard octahedron (`std_octahedron`) is defined as the convex hull of six points in $\mathbb{R}^3$, specifically:
$$\text{std\_octahedron} = \text{conv}\left\{\begin{pmatrix}1 \\ 0 \\ 0\end{pmatrix}, \begin{pmatrix}-1 \\ 0 \\ 0\end{pmatrix}, \begin{pmatrix}0 \\ 0 \\ 1\end{pmatrix}, \begin{pmatrix}0 \\ 0 \\ -1\end{pmatrix}, \begin{pmatrix}0 \\ 1 \\ 0\end{pmatrix}, \begin{pmatrix}0 \\ -1 \\ 0\end{pmatrix}\right\}$$

Where `convex hull` (or $\text{conv}$) of a set of points is the smallest convex set containing those points.

### Informal proof
This is a definition, not a theorem, so no proof is provided.

### Mathematical insight
The standard octahedron is defined by taking the convex hull of six points that lie on the coordinate axes at unit distance from the origin. These six points correspond to the positive and negative unit vectors along each of the three coordinate axes.

The resulting octahedron is a regular polyhedron with 8 triangular faces, 12 edges, and 6 vertices. It is one of the five Platonic solids. The standard octahedron can also be thought of as the dual polyhedron of the standard cube.

This particular representation places the octahedron in a standard position with its vertices at unit distance from the origin along the coordinate axes. This standardized placement makes it convenient for various geometric computations and is often used as a reference configuration when studying properties of octahedra.

### Dependencies
#### Definitions
- `convex hull`: The smallest convex set containing the given set of points

### Porting notes
When porting this definition to other systems:
- Ensure that the system has a definition of convex hull
- Make sure the vector notation in the target system correctly represents 3D vectors
- Note that HOL Light uses `&1` to denote the real number 1, and `--` to denote negation
- Some systems might prefer to define the octahedron through its faces rather than vertices

---

## std_dodecahedron

### std_dodecahedron
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- new_definition

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
The standard dodecahedron is defined as the convex hull of 20 points in $\mathbb{R}^3$ given by:
- The 8 points $(\pm 1, \pm 1, \pm 1)$ with all possible sign combinations
- The 12 points with coordinates that are permutations of $(0, \pm 1/\phi, \pm \phi)$ where $\phi = \frac{1 + \sqrt{5}}{2}$ is the golden ratio

These 20 vertices form the corners of a regular dodecahedron centered at the origin.

### Informal proof
(No proof is required as this is a definition.)

### Mathematical insight
The dodecahedron is one of the five Platonic solids, with 12 regular pentagonal faces, 30 edges, and 20 vertices. This specific definition gives a standard embedding of the dodecahedron in $\mathbb{R}^3$.

The construction uses the golden ratio $\phi = \frac{1 + \sqrt{5}}{2}$, which is intrinsically related to the pentagonal structure of the dodecahedron's faces. The vertices are carefully positioned to create a regular dodecahedron centered at the origin with specific symmetry properties.

This particular coordinate representation places the dodecahedron so that:
- Eight of its vertices are at the corners of a cube (the $(\pm 1, \pm 1, \pm 1)$ points)
- The remaining twelve vertices are positioned using the golden ratio to complete the dodecahedral structure

This representation is valuable for studying the geometric properties of the dodecahedron and its relationship to other Platonic solids.

### Dependencies
#### Definitions
- `convex hull`: The convex hull of a set of points

### Porting notes
When porting this definition:
- Ensure the target system has a compatible definition of convex hull
- Verify that the golden ratio and vector notation translate correctly
- The `:real^3->bool` type annotation indicates this defines a set in 3D space

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
        vector[p; &0; -- &1],vector[--p; &0; -- &1]}:real^3->bool`;;
```

### Informal statement
The standard icosahedron, denoted as $\text{std\_icosahedron}$, is defined as a set of points in $\mathbb{R}^3$ given by:

$\text{std\_icosahedron} = \text{convex hull}(S)$

where $S$ is the set of 12 vertices:
$S = \{(0, 1, p), (0, 1, -p), (0, -1, p), (0, -1, -p),$ 
$\quad (1, p, 0), (1, -p, 0), (-1, p, 0), (-1, -p, 0),$
$\quad (p, 0, 1), (-p, 0, 1), (p, 0, -1), (-p, 0, -1)\}$

and $p = \frac{1 + \sqrt{5}}{2}$ is the golden ratio.

### Informal proof
This is a definition, not a theorem, so no proof is required.

### Mathematical insight
The icosahedron is one of the five Platonic solids, having 20 triangular faces, 30 edges, and 12 vertices. This particular definition constructs the standard icosahedron by specifying its 12 vertices in 3D space and taking their convex hull.

The value $p = \frac{1 + \sqrt{5}}{2} ≈ 1.618$ is the golden ratio, which appears frequently in geometric constructions. This specific choice of vertices places the icosahedron in a standard position centered at the origin with vertices arranged symmetrically.

The vertices are strategically positioned on three orthogonal golden rectangles, giving the icosahedron its highly symmetric structure. Each vertex has five neighbors, and each face is an equilateral triangle.

This standard definition is useful for further analysis of the geometric properties of the icosahedron, such as its symmetry group, duality with the dodecahedron, and various measurements.

### Dependencies
#### Definitions
- `convex hull` - The convex hull operation in $\mathbb{R}^3$
- `vector` - Constructor for vectors in $\mathbb{R}^3$

### Porting notes
When porting to other proof assistants:
1. Ensure the target system has a definition of convex hull operation
2. The golden ratio $\frac{1 + \sqrt{5}}{2}$ should be clearly defined
3. The representation of 3D vectors may differ between systems
4. Some systems might prefer a face-based or edge-based representation instead of a vertex-based one
5. Consider whether the target system has special support for regular polyhedra that could simplify the formalization

---

## REAL_RAT5_OF_RAT_CONV

### REAL_RAT5_OF_RAT_CONV

### Type of the formal statement
Conversion (function definition)

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
This defines a conversion function `REAL_RAT5_OF_RAT_CONV` that transforms a rational constant term into the canonical form $p + 0 \cdot \sqrt{5}$, where $p$ is the original rational. If the input term is not a rational constant, the conversion returns a reflexive theorem (identity theorem).

### Informal proof
The function is defined by:

1. First proving the theorem $p = p + 0 \cdot \sqrt{5}$ using real arithmetic tactics
2. Creating a conversion that rewrites terms according to this theorem
3. Defining a function that applies this conversion only to rational constants (terms for which `is_ratconst` returns true), and returns a reflexive theorem otherwise

The proof of the underlying theorem is straightforward, as adding $0 \cdot \sqrt{5}$ to any real number $p$ does not change its value.

### Mathematical insight
This conversion is part of a system for computation in $\mathbb{Q}[\sqrt{5}]$, the field extension of rational numbers with $\sqrt{5}$.

Numbers in $\mathbb{Q}[\sqrt{5}]$ are canonically represented in one of two forms:
- A rational constant $r$
- An expression $r_1 + r_2 \cdot \sqrt{5}$ where $r_2$ is nonzero

This particular conversion handles the first case by transforming a plain rational $p$ into the standardized form $p + 0 \cdot \sqrt{5}$, which allows for uniform treatment of elements in $\mathbb{Q}[\sqrt{5}]$ in subsequent operations.

The conversion is part of the computational infrastructure for working with quadratic extensions, particularly $\mathbb{Q}[\sqrt{5}]$ which is important in number theory and appears in contexts like the golden ratio.

### Dependencies
None explicitly used in the implementation besides HOL Light's built-in tactics:
- `REAL_ARITH_TAC`
- `REWR_CONV`
- `is_ratconst`
- `REFL`

### Porting notes
When porting this conversion:
1. Ensure that your target system has a way to detect rational constants
2. Define a canonical representation for elements in $\mathbb{Q}[\sqrt{5}]$
3. Implement a similar conversion that maps rational constants to their canonical form in this representation
4. Make sure your system's type for reals can accommodate expressions involving $\sqrt{5}$

The implementation is straightforward but relies on HOL Light's built-in facilities for rewriting and working with real numbers, so you may need to adapt these to the equivalent mechanisms in your target system.

---

## REAL_RAT_OF_RAT5_CONV

### Name of formal statement
REAL_RAT_OF_RAT5_CONV

### Type of formal statement
Conversion function

### Formal Content
```ocaml
let REAL_RAT_OF_RAT5_CONV =
  let pth = prove
   (`p + &0 * sqrt(&5) = p`,
    REAL_ARITH_TAC) in
  GEN_REWRITE_CONV TRY_CONV [pth];;
```

### Informal statement
This is a conversion function that simplifies expressions of the form:
$$p + 0 \cdot \sqrt{5}$$
to just:
$$p$$

where $p$ is a real number.

### Informal proof
The conversion works as follows:

1. First, it proves the theorem:
   $$p + 0 \cdot \sqrt{5} = p$$
   using `REAL_ARITH_TAC`, which is a tactic for solving arithmetic problems over real numbers.

2. Then it creates a conversion that uses this theorem as a rewrite rule with `GEN_REWRITE_CONV TRY_CONV`.

The `TRY_CONV` modifier ensures that the conversion won't fail if the pattern doesn't match - it will just return the original term unchanged.

### Mathematical insight
This conversion is a utility that simplifies expressions in the field $\mathbb{Q}(\sqrt{5})$, where elements are typically represented as $a + b\sqrt{5}$ with $a,b \in \mathbb{Q}$. When $b = 0$, the expression should simplify to just $a$.

This conversion is likely part of a larger framework for algebraic manipulation of expressions involving $\sqrt{5}$, which is important in various mathematical contexts like solving the quintic equation or working with golden ratio calculations.

### Dependencies
- **Tactics**: `REAL_ARITH_TAC`
- **Conversions**: `GEN_REWRITE_CONV`, `TRY_CONV`

### Porting notes
When porting this to other proof assistants:
1. Ensure the target system has a way to represent real numbers and specifically $\sqrt{5}$
2. Create an equivalent lemma for the simplification
3. Implement the simplification as a rewrite rule or conversion that can be applied to terms
4. If the target system doesn't have a direct equivalent to `TRY_CONV` (which suppresses failures), you'll need to implement that behavior explicitly

---

## REAL_RAT5_ADD_CONV

### Name of formal statement
REAL_RAT5_ADD_CONV

### Type of the formal statement
conversion (function that creates a theorem)

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
This conversion handles addition of expressions of the form $a + b \cdot \sqrt{5}$ where $a$ and $b$ are rational numbers. It applies the identity:
$$(a_1 + b_1 \cdot \sqrt{5}) + (a_2 + b_2 \cdot \sqrt{5}) = (a_1 + a_2) + (b_1 + b_2) \cdot \sqrt{5}$$

When given a sum where both terms are of this form, it computes the resulting expression also in the form $a + b \cdot \sqrt{5}$ where $a$ and $b$ are rational numbers.

### Informal proof
The conversion is constructed as follows:

1. First, it proves the theorem that establishes the addition formula for numbers of the form $a + b \cdot \sqrt{5}$:
   $$(a_1 + b_1 \cdot \sqrt{5}) + (a_2 + b_2 \cdot \sqrt{5}) = (a_1 + a_2) + (b_1 + b_2) \cdot \sqrt{5}$$
   
2. Then, it creates a conversion that either:
   - Uses `REAL_RAT_ADD_CONV` directly if both summands are rational constants, or
   - Follows these steps when at least one summand involves $\sqrt{5}$:
     - Converts any pure rational numbers to the form $p + 0 \cdot \sqrt{5}$ using `REAL_RAT5_OF_RAT_CONV`
     - Applies the addition formula from the theorem
     - Computes the addition of rational numbers in the real part
     - Computes the addition of rational numbers in the coefficient of $\sqrt{5}$
     - Simplifies expressions of the form $p + 0 \cdot \sqrt{5}$ back to $p$ using `REAL_RAT_OF_RAT5_CONV`

### Mathematical insight
This conversion implements symbolic computation for adding numbers in the field $\mathbb{Q}[\sqrt{5}]$ - the field extension of rational numbers by $\sqrt{5}$. Such numbers can be written in the form $a + b\sqrt{5}$ where $a,b \in \mathbb{Q}$.

The conversion is part of a suite of computational tools for working with quadratic number fields, which are important in various number theory applications and specifically for calculations involving the golden ratio and related concepts (which involve $\sqrt{5}$).

This kind of specialized arithmetic conversion enables automated simplification of expressions involving $\sqrt{5}$ without requiring manual algebraic manipulation.

### Dependencies
- Conversions:
  - `REAL_RAT_ADD_CONV`: Conversion for adding rational numbers
  - `REAL_RAT5_OF_RAT_CONV`: Conversion for transforming a rational number $p$ into $p + 0 \cdot \sqrt{5}$
  - `REAL_RAT_OF_RAT5_CONV`: Conversion for simplifying $p + 0 \cdot \sqrt{5}$ back to $p$

### Porting notes
When porting this to another system:
- Ensure the target system has good support for field extensions or algebraic numbers
- Consider generalizing this approach for arbitrary quadratic extensions $\mathbb{Q}[\sqrt{d}]$ rather than hardcoding $\sqrt{5}$
- The tactical structure using `THENC` and `ORELSEC` may need to be adapted to the target system's conversion combining operators

---

## REAL_RAT5_SUB_CONV

### Name of formal statement
REAL_RAT5_SUB_CONV

### Type of the formal statement
new_definition (conversion function)

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
This defines a conversion function `REAL_RAT5_SUB_CONV` that simplifies subtraction expressions involving real numbers of the form $a + b \cdot \sqrt{5}$, where $a$ and $b$ are rational numbers. The conversion applies the identity:

$$(a_1 + b_1 \cdot \sqrt{5}) - (a_2 + b_2 \cdot \sqrt{5}) = (a_1 - a_2) + (b_1 - b_2) \cdot \sqrt{5}$$

This conversion handles both standard rationals and numbers in the $a + b \cdot \sqrt{5}$ form.

### Informal proof
The conversion is constructed as follows:

1. First, prove the key identity: $(a_1 + b_1 \cdot \sqrt{5}) - (a_2 + b_2 \cdot \sqrt{5}) = (a_1 - a_2) + (b_1 - b_2) \cdot \sqrt{5}$ using `REAL_ARITH_TAC`.

2. The conversion is defined as a combination of simpler conversions:
   - Try applying `REAL_RAT_SUB_CONV` first (handles standard rational subtraction).
   - If that fails, apply the following sequence:
     - Convert any pure rational numbers to the form $r + 0 \cdot \sqrt{5}$ using `REAL_RAT5_OF_RAT_CONV`
     - Apply the proven identity using `GEN_REWRITE_CONV`
     - Simplify the coefficient subtractions using `REAL_RAT_SUB_CONV`
     - Finally, convert back to the simplest form using `REAL_RAT_OF_RAT5_CONV` (which removes terms with zero coefficients)

The underlying proof of the key identity itself is straightforward algebraic manipulation proven automatically by `REAL_ARITH_TAC`.

### Mathematical insight
This conversion is part of a broader set of arithmetic utilities for manipulating expressions involving $\sqrt{5}$. Such expressions are important in various mathematical contexts, including the study of the golden ratio and related algebraic numbers.

The conversion provides an efficient way to simplify subtraction expressions in the ring $\mathbb{Q}[\sqrt{5}]$ by handling the coefficients of $1$ and $\sqrt{5}$ separately. This approach allows for exact symbolic computation with these algebraic numbers without resorting to floating-point approximations.

The implementation follows the algebraic structure of the number field $\mathbb{Q}(\sqrt{5})$, leveraging the fact that addition, subtraction, and multiplication follow component-wise rules when expressed in the standard basis $\{1, \sqrt{5}\}$.

### Dependencies
- **Conversions:**
  - `REAL_RAT_SUB_CONV`: Conversion for subtracting rational numbers
  - `REAL_RAT5_OF_RAT_CONV`: Converts a rational number `p` to the form `p + &0 * sqrt(&5)`
  - `REAL_RAT_OF_RAT5_CONV`: Simplifies expressions by eliminating zero coefficients (e.g., `p + &0 * sqrt(&5)` to `p`)

### Porting notes
When implementing this in another proof assistant:
1. Ensure you have corresponding operations for your system's conversions (term rewriting strategies)
2. The HOL Light notation `&n` represents numeric injection into the reals
3. Consider how your target system handles algebraic numbers - some systems might have built-in algebraic number structures that could simplify the implementation
4. The composition pattern using `THENC` and `ORELSEC` operators needs to be translated to the target system's term transformation composition mechanisms

---

## REAL_RAT5_MUL_CONV

### REAL_RAT5_MUL_CONV

### Type of the formal statement
Conversion definition (let-binding)

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
`REAL_RAT5_MUL_CONV` is a conversion that simplifies multiplication of expressions of the form $a + b \cdot \sqrt{5}$, where $a$ and $b$ are rational numbers. It computes the resulting expression in the form $c + d \cdot \sqrt{5}$ where $c$ and $d$ are again rational numbers.

The conversion applies the following algebraic identity:
$(a_1 + b_1 \cdot \sqrt{5}) \cdot (a_2 + b_2 \cdot \sqrt{5}) = (a_1 \cdot a_2 + 5 \cdot b_1 \cdot b_2) + (a_1 \cdot b_2 + a_2 \cdot b_1) \cdot \sqrt{5}$

### Informal proof
The proof has two main components:

1. First, we prove the fundamental identity for multiplying expressions of the form $a + b\sqrt{5}$:

   To prove that $(a_1 + b_1 \cdot \sqrt{5}) \cdot (a_2 + b_2 \cdot \sqrt{5}) = (a_1 \cdot a_2 + 5 \cdot b_1 \cdot b_2) + (a_1 \cdot b_2 + a_2 \cdot b_1) \cdot \sqrt{5}$, we:
   
   - Apply the theorem `SQRT_POW_2` instantiated for the number 5, which gives us $(\sqrt{5})^2 = 5$
   - Then use the real field arithmetic procedure (`REAL_FIELD`) to complete the calculation using standard algebraic manipulations
   
2. The conversion itself is constructed as a composite conversion that:
   - First tries `REAL_RAT_MUL_CONV` (for handling purely rational multiplications)
   - Otherwise:
     - Converts any rational constants to the form $p + 0 \cdot \sqrt{5}$ using `REAL_RAT5_OF_RAT_CONV`
     - Applies the proved identity to perform the multiplication
     - Simplifies the rational arithmetic in the resulting expression
     - Finally, uses `REAL_RAT_OF_RAT5_CONV` to simplify expressions of form $p + 0 \cdot \sqrt{5}$ back to $p$

### Mathematical insight
This conversion is part of a family of operations designed to work with quadratic extensions of rational numbers, specifically the extension $\mathbb{Q}[\sqrt{5}]$. This field appears in various number theory contexts, including the study of the golden ratio $(1 + \sqrt{5})/2$.

The conversion provides an automated way to perform symbolic algebra with these extensions, maintaining the canonical form $a + b\sqrt{5}$ throughout computations. This is crucial for reasoning about such number fields in a formal setting.

The implementation demonstrates how a complex algebraic operation can be broken down into smaller conversion steps and combined in HOL Light's conversion combinators to create a powerful simplification tool.

### Dependencies
- `REAL_RAT5_OF_RAT_CONV`: Conversion that transforms a rational constant $p$ to the form $p + 0 \cdot \sqrt{5}$
- `REAL_RAT_OF_RAT5_CONV`: Conversion that simplifies expressions of form $p + 0 \cdot \sqrt{5}$ back to $p$
- `SQRT_POW_2`: Theorem stating $(\sqrt{x})^2 = x$ (used in the proof)
- `REAL_RAT_MUL_CONV`: Conversion for multiplying rational numbers
- `REAL_RAT_ADD_CONV`: Conversion for adding rational numbers

### Porting notes
When porting this to another system:
- Ensure the target system has a way to represent and compute with symbolic expressions containing square roots
- The target system should have good support for combining conversions/tactics to build complex simplification procedures
- In systems with more sophisticated algebraic rewriting (like Lean or Isabelle), it might be possible to achieve similar functionality with simpler tactics using built-in algebraic simplification

---

## REAL_RAT5_INV_CONV

### REAL_RAT5_INV_CONV

### Type of the formal statement
- Conversion (computational function that produces a theorem)

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
This conversion computes the inverse of expressions of the form $a + b\sqrt{5}$ where $a$ and $b$ are rational numbers, provided that $a^2 \neq 5b^2$. 

The conversion uses the formula:
$$\frac{1}{a + b\sqrt{5}} = \frac{a}{a^2 - 5b^2} - \frac{b}{a^2 - 5b^2}\sqrt{5}$$

### Informal proof
The conversion is based on a theorem that establishes the formula for the inverse of $a + b\sqrt{5}$ when $a^2 \neq 5b^2$. 

The proof of this theorem proceeds as follows:
* We need to show that $\frac{1}{a + b\sqrt{5}} = \frac{a}{a^2 - 5b^2} - \frac{b}{a^2 - 5b^2}\sqrt{5}$.
* The key insight is that $a^2 - 5b^2 = (a + b\sqrt{5})(a - b\sqrt{5})$.
  * This is proven using the identity $\sqrt{5}^2 = 5$ and algebraic manipulation.
* The proof then uses real field arithmetic to verify that:
  $(a + b\sqrt{5})(\frac{a}{a^2 - 5b^2} - \frac{b}{a^2 - 5b^2}\sqrt{5}) = 1$
* This confirms that $\frac{a}{a^2 - 5b^2} - \frac{b}{a^2 - 5b^2}\sqrt{5}$ is indeed the inverse of $a + b\sqrt{5}$.

The implementation of the conversion:
1. First tries to apply `REAL_RAT_INV_CONV` (which handles simpler rational inversions).
2. If that fails, it matches the expression against the pattern in the theorem.
3. Verifies that $a^2 \neq 5b^2$ by reducing the expression to `T`.
4. Performs a series of conversion operations to simplify the numerical expressions in the result.

### Mathematical insight
This conversion implements the standard formula for the inverse of a binomial expression involving a quadratic surd, specifically $\sqrt{5}$. The formula is derived using the conjugate method: multiplying both numerator and denominator by the conjugate of the denominator.

The condition $a^2 \neq 5b^2$ is necessary to ensure that the denominator of the resulting expression is non-zero. If $a^2 = 5b^2$, then $a + b\sqrt{5}$ would have a rational multiple of $\sqrt{5} \pm 1$ as a factor, making it impossible to perform the inversion as described.

This conversion is part of a family of arithmetic operations on expressions involving quadratic surds, which are important in number theory and computer algebra systems.

### Dependencies
- Theorem conversions:
  - `REAL_RAT_INV_CONV`: Conversion for computing inverses of rational numbers
  - `REAL_RAT_NEG_CONV`: Conversion for negating rational numbers
  - `REAL_RAT_POW_CONV`: Conversion for computing powers of rational numbers
  - `REAL_RAT_MUL_CONV`: Conversion for multiplying rational numbers
  - `REAL_RAT_SUB_CONV`: Conversion for subtracting rational numbers
  - `REAL_RAT_DIV_CONV`: Conversion for dividing rational numbers
  - `REAL_RAT_REDUCE_CONV`: Conversion for reducing rational expressions

### Porting notes
When porting this to other proof assistants:
1. The implementation relies on HOL Light's conversion mechanism, which might differ in other systems.
2. The proof uses field automation (`CONV_TAC REAL_FIELD`), so alternative field solvers would need to be used in other systems.
3. The nested structure of conversion applications might need to be adapted to match the target system's conversion combinators.
4. Special attention should be paid to ensuring that the condition $a^2 \neq 5b^2$ is properly checked in the target system.

---

## REAL_RAT5_DIV_CONV

### REAL_RAT5_DIV_CONV

### Type of the formal statement
Function definition (HOL Light conversion)

### Formal Content
```ocaml
let REAL_RAT5_DIV_CONV =
  GEN_REWRITE_CONV I [real_div] THENC
  RAND_CONV REAL_RAT5_INV_CONV THENC
  REAL_RAT5_MUL_CONV;;
```

### Informal statement
This defines a conversion function `REAL_RAT5_DIV_CONV` for computing divisions of expressions of the form $a + b\sqrt{5}$, where $a$ and $b$ are rational numbers. The conversion uses the standard definition of division as multiplication by the reciprocal and applies specialized conversions to simplify the result.

### Informal proof
The function is defined through a composition of three conversion steps:

1. First, it rewrites division using the standard definition of real division: $x / y = x \cdot (1/y)$
2. Then it applies `REAL_RAT5_INV_CONV` to the denominator to compute the reciprocal of an expression of form $a + b\sqrt{5}$
3. Finally, it applies `REAL_RAT5_MUL_CONV` to compute the multiplication of the numerator with the reciprocal

This composition is achieved using the conversion combinators `THENC` and `RAND_CONV` which sequence conversions and apply them to the right-hand side of applications, respectively.

### Mathematical insight
This conversion is part of a family of specialized arithmetic functions for manipulating expressions involving the quadratic extension $\mathbb{Q}(\sqrt{5})$. These are particularly useful for formalizing results about the golden ratio and related concepts in number theory.

The key insight is that division in the number field $\mathbb{Q}(\sqrt{5})$ can be performed by:
1. Converting the division to multiplication by reciprocal
2. Computing the reciprocal of $a + b\sqrt{5}$ as $\frac{a - b\sqrt{5}}{a^2 - 5b^2}$ (using the norm in the number field)
3. Multiplication in the field, which follows the standard formula for multiplying expressions with radicals

This gives us an algorithm to perform exact symbolic division in $\mathbb{Q}(\sqrt{5})$.

### Dependencies
- Theorems:
  - `REAL_RAT5_MUL_CONV`: Implements multiplication for expressions of the form $a + b\sqrt{5}$
  - `REAL_RAT5_INV_CONV`: Implements reciprocal computation for expressions of the form $a + b\sqrt{5}$
- Definitions:
  - `real_div`: The standard definition of real division

### Porting notes
When porting to another system:
1. Ensure the target system has a good representation of real numbers and square roots
2. Implement the required arithmetic operations for the quadratic extension $\mathbb{Q}(\sqrt{5})$
3. The conversion-based approach is specific to HOL Light; other systems might use different mechanisms for simplification and computation
4. Consider using type classes or structures to encapsulate the field operations if supported by the target system

---

## REAL_RAT5_LE_CONV

### Name of formal statement
REAL_RAT5_LE_CONV

### Type of the formal statement
Conversion function definition (let-binding)

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
`REAL_RAT5_LE_CONV` is a conversion function that evaluates inequality expressions of the form $a_1 + b_1 \sqrt{5} \leq a_2 + b_2 \sqrt{5}$ where $a_1, b_1, a_2, b_2$ are rational numbers. It reduces such inequalities to equivalent logical combinations of rational inequalities.

The conversion uses the following key logical equivalence:
$(a_1 + b_1 \sqrt{5}) \leq (a_2 + b_2 \sqrt{5})$ if and only if one of these conditions holds:
- $a_1 \leq a_2$ and $b_1 \leq b_2$, or
- $a_2 \leq a_1$ and $b_1 \leq b_2$ and $(a_1 - a_2)^2 \leq 5(b_2 - b_1)^2$, or
- $a_1 \leq a_2$ and $b_2 \leq b_1$ and $5(b_2 - b_1)^2 \leq (a_1 - a_2)^2$

### Informal proof
The proof proceeds in two main steps:

1. First, a lemma is established showing that for any real numbers $x$ and $y$:
   $x \leq y \cdot \sqrt{5}$ if and only if one of these conditions holds:
   - $x \leq 0$ and $0 \leq y$, or
   - $0 \leq x$ and $0 \leq y$ and $x^2 \leq 5y^2$, or
   - $x \leq 0$ and $y \leq 0$ and $5y^2 \leq x^2$

   This lemma is proven by:
   - Using the property $\sqrt{5}^2 = 5$ (from `SQRT_POW_2`)
   - Applying properties of squares and absolute values
   - Using properties of multiplication with positive numbers
   - Completing with real arithmetic reasoning

2. Then, the main theorem is proven:
   $(a_1 + b_1 \sqrt{5}) \leq (a_2 + b_2 \sqrt{5})$ if and only if one of the three conditions listed in the informal statement.

   The proof:
   - First rewrites the inequality to: $a_1 - a_2 \leq (b_2 - b_1) \sqrt{5}$
   - Then applies the lemma from step 1
   - Uses real arithmetic to simplify and complete the proof

The conversion function is constructed by:
- First trying the standard `REAL_RAT_LE_CONV` (for purely rational inequalities)
- If that fails, converting both sides using `REAL_RAT5_OF_RAT_CONV` to express them in the form $a + b\sqrt{5}$
- Applying the main theorem to reduce to a Boolean combination of rational inequalities
- Using `REAL_RAT_REDUCE_CONV` to evaluate those rational inequalities

### Mathematical insight
This conversion function provides a decision procedure for inequalities involving quadratic field extensions of $\mathbb{Q}$ by $\sqrt{5}$ (i.e., the field $\mathbb{Q}(\sqrt{5})$). It's based on the general principle that to compare expressions in such fields, we need to compare both the rational parts and the irrational parts, but additional conditions are needed to handle cases where the coefficients of $\sqrt{5}$ move in opposite directions.

The algorithm effectively reduces a problem in $\mathbb{Q}(\sqrt{5})$ to a problem in $\mathbb{Q}$ by analyzing the relationship between rational and irrational parts. This is a classic technique in algebraic number theory when working with simple field extensions.

This conversion is particularly useful when formalizing mathematics involving the golden ratio $\phi = \frac{1+\sqrt{5}}{2}$ or the regular pentagon, since $\sqrt{5}$ appears naturally in those contexts.

### Dependencies
#### Theorems
- `REAL_RAT5_OF_RAT_CONV`: Conversion for expressing rational numbers as $r + 0 \cdot \sqrt{5}$
- `SQRT_POW_2`: The property that $\sqrt{a}^2 = a$ for positive $a$
- `REAL_LE_MUL_EQ`: Equivalences for inequalities with multiplication
- `SQRT_POS_LT`: The property that $\sqrt{a} > 0$ for $a > 0$

#### Conversions
- `REAL_RAT_LE_CONV`: Decides inequalities between rational numbers
- `REAL_RAT_REDUCE_CONV`: Reduces rational arithmetic expressions

### Porting notes
When porting this to another system:
1. Ensure the target system has a good representation of real numbers and is capable of reasoning about irrational numbers like $\sqrt{5}$.
2. Decision procedures for quadratic field extensions may already exist in some provers - check before implementing from scratch.
3. The conversion is essentially implementing a decision procedure for the theory of real closed fields restricted to expressions involving $\sqrt{5}$.
4. You may need to adjust the approach if your target system doesn't use conversions in the same way as HOL Light.

---

## REAL_RAT5_EQ_CONV

### Name of formal statement
REAL_RAT5_EQ_CONV

### Type of the formal statement
Conversion definition

### Formal Content
```ocaml
let REAL_RAT5_EQ_CONV =
  GEN_REWRITE_CONV I [GSYM REAL_LE_ANTISYM] THENC
  BINOP_CONV REAL_RAT5_LE_CONV THENC
  GEN_REWRITE_CONV I [AND_CLAUSES];;
```

### Informal statement
This is a conversion function that transforms expressions of equality between two terms involving rational numbers and square roots of 5 into an equivalent logical form. It works by:
1. Rewriting the equality using the antisymmetry property of less-than-or-equal-to relation
2. Applying the `REAL_RAT5_LE_CONV` conversion to both sides of the resulting conjunction
3. Normalizing the resulting expression using Boolean simplification

In mathematical terms, it converts an equality $a + b\sqrt{5} = c + d\sqrt{5}$ into a form derived from the conjunction of $a + b\sqrt{5} \leq c + d\sqrt{5}$ and $c + d\sqrt{5} \leq a + b\sqrt{5}$.

### Informal proof
The conversion is defined compositionally with three steps:

1. First, it applies the antisymmetry of $\leq$ to convert an equality $x = y$ into the conjunction $x \leq y \wedge y \leq x$, using `GSYM REAL_LE_ANTISYM`.

2. Then, it applies `REAL_RAT5_LE_CONV` to both sides of this conjunction. From the dependencies, we know that `REAL_RAT5_LE_CONV` transforms expressions of the form $(a_1 + b_1\sqrt{5}) \leq (a_2 + b_2\sqrt{5})$ into equivalent disjunctive normal form:
   - $a_1 \leq a_2 \wedge b_1 \leq b_2$, or
   - $a_2 \leq a_1 \wedge b_1 \leq b_2 \wedge (a_1 - a_2)^2 \leq 5(b_2 - b_1)^2$, or
   - $a_1 \leq a_2 \wedge b_2 \leq b_1 \wedge 5(b_2 - b_1)^2 \leq (a_1 - a_2)^2$

3. Finally, it simplifies the resulting expression using Boolean algebra identities from `AND_CLAUSES`.

### Mathematical insight
This conversion is part of a framework for automated reasoning about expressions involving rational numbers and the square root of 5. Such expressions are important in various contexts, including algebraic number theory related to the golden ratio.

The key insight is recognizing that equality between expressions with $\sqrt{5}$ can be characterized through the antisymmetry of $\leq$, and then using the existing conversion for inequalities to reduce the problem to checking conditions on the rational coefficients.

The conversion effectively breaks down a complex equality involving irrational numbers into a set of inequalities between rational numbers, which are more computationally tractable.

### Dependencies
- `REAL_RAT5_LE_CONV`: Converts inequalities between expressions with rational numbers and $\sqrt{5}$ into equivalent conditions
- `GSYM REAL_LE_ANTISYM`: Theorem stating $x = y \Leftrightarrow x \leq y \wedge y \leq x$
- `AND_CLAUSES`: Collection of theorems about logical conjunction
- `BINOP_CONV`: Higher-order conversion for applying conversions to both operands of a binary operation
- `GEN_REWRITE_CONV`: Generalized rewriting conversion
- `THENC`: Operator for sequential composition of conversions

### Porting notes
When porting this to another proof assistant:
1. Ensure the target system has a corresponding mechanism for conversions or tactical theorem proving
2. First port the dependencies, especially `REAL_RAT5_LE_CONV` which does the heavy lifting
3. The implementation relies on HOL Light's conversion combinators - in other systems, you might need to implement this as a function returning a theorem rather than using conversion combinators

---

## VECTOR3_SUB_CONV

### Name of formal statement
VECTOR3_SUB_CONV

### Type of the formal statement
Conversion function definition

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
This is a conversion function that simplifies subtraction of 3D vectors with specific form, transforming expressions of the form:

$$\text{vector}[x_1; x_2; x_3] - \text{vector}[y_1; y_2; y_3]$$

into the form:

$$\text{vector}[x_1 - y_1; x_2 - y_2; x_3 - y_3]$$

where the coordinates are in $\mathbb{Q}[\sqrt{5}]$ (rational numbers with square root of 5).

### Informal proof
The conversion is constructed as follows:

1. First, a theorem `pth` is established, proving that:
   $$\text{vector}[x_1; x_2; x_3] - \text{vector}[y_1; y_2; y_3] = \text{vector}[x_1 - y_1; x_2 - y_2; x_3 - y_3]$$

   This is proven by:
   - Using `SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3]` to reduce vector equality to equality on all components
   - Using `REWRITE_TAC[VECTOR_3; VECTOR_SUB_COMPONENT]` to apply the definition of vector subtraction component-wise

2. The conversion combines two operations:
   - `GEN_REWRITE_CONV I [pth]`: Applies the theorem to rewrite the vector subtraction
   - `RAND_CONV(LIST_CONV REAL_RAT5_SUB_CONV)`: Applies `REAL_RAT5_SUB_CONV` to each element in the resulting vector, simplifying expressions in $\mathbb{Q}[\sqrt{5}]$

The conversion thus transforms a vector subtraction into component-wise subtraction and then simplifies each component in $\mathbb{Q}[\sqrt{5}]$.

### Mathematical insight
This conversion provides an efficient way to compute the subtraction of 3D vectors whose coordinates are in $\mathbb{Q}[\sqrt{5}]$. This is particularly useful in geometric computations involving regular polyhedra or other constructions where $\sqrt{5}$ appears naturally.

The conversion implements the natural component-wise definition of vector subtraction, but also ensures that the resulting components are simplified within $\mathbb{Q}[\sqrt{5}]$. This maintains a canonical form for vectors, which is essential for automated reasoning about geometric objects.

### Dependencies
- `REAL_RAT5_SUB_CONV`: Conversion for subtracting numbers in $\mathbb{Q}[\sqrt{5}]$
- `CART_EQ`: Equality of cartesian vectors implies equality of components
- `DIMINDEX_3`: The dimension of $\mathbb{R}^3$ is 3
- `FORALL_3`: Universal quantification over 3 elements
- `VECTOR_3`: Definition of 3D vector construction
- `VECTOR_SUB_COMPONENT`: Component-wise definition of vector subtraction

### Porting notes
When porting this conversion to another proof assistant:
1. Ensure that vectors and their component-wise operations are properly defined
2. Implement or port the necessary machinery for handling elements in $\mathbb{Q}[\sqrt{5}]$
3. Be aware of potential differences in how vectors are represented (e.g., as functions from indices, as tuples, or as lists)
4. The component-wise simplification might need different tactics depending on the proof assistant's simplification capabilities

---

## VECTOR3_CROSS_CONV

### VECTOR3_CROSS_CONV

### Type of the formal statement
- Conversion function (HOL Light utility)

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
This is a conversion function (CONV) in HOL Light that computes the cross product of two 3D vectors when they are explicitly represented as `vector[x1;x2;x3]` and `vector[y1;y2;y3]`. The conversion applies the cross product formula and then simplifies the arithmetic expressions involving real numbers and real numbers with terms containing $\sqrt{5}$.

### Informal proof
The conversion works in two steps:

1. First, it uses a theorem `pth` which is proven within the function. This theorem states the explicit formula for the cross product of two 3D vectors:
   ```
   (vector[x1;x2;x3]) cross (vector[y1;y2;y3]) =
     vector[x2 * y3 - x3 * y2; x3 * y1 - x1 * y3; x1 * y2 - x2 * y1]
   ```
   This is proven by rewriting with the definition of `cross` and the `VECTOR_3` theorem.

2. After applying this rewriting, the conversion performs arithmetic simplification on each component of the resulting vector:
   - It uses `RAND_CONV` to focus on the right side of the equation (the explicit vector)
   - It applies `LIST_CONV` to process each of the three components of the vector
   - For each component, it:
     - Uses `BINOP_CONV REAL_RAT5_MUL_CONV` to multiply terms that might involve $\sqrt{5}$
     - Uses `REAL_RAT5_SUB_CONV` to subtract terms that might involve $\sqrt{5}$

The conversion handles vectors whose components may contain terms with $\sqrt{5}$, which is likely important for computations involving regular polyhedra or certain geometric constructions.

### Mathematical insight
This conversion provides an efficient way to compute cross products of 3D vectors in HOL Light, especially for vectors whose components may involve terms with $\sqrt{5}$. The cross product is a fundamental operation in 3D vector algebra, producing a vector perpendicular to the plane containing the two input vectors.

The inclusion of special handling for terms containing $\sqrt{5}$ suggests this conversion is particularly designed for geometric reasoning about regular polyhedra (like the dodecahedron and icosahedron) or other geometric objects where $\sqrt{5}$ appears naturally.

This conversion is part of HOL Light's computational infrastructure, allowing automated simplification and calculation with 3D vectors in formal proofs.

### Dependencies
- **Definitions**:
  - `cross`: Defines the cross product operation for 3D vectors
- **Theorems**:
  - `REAL_RAT5_SUB_CONV`: Conversion for subtraction of real numbers involving $\sqrt{5}$
  - `REAL_RAT5_MUL_CONV`: Conversion for multiplication of real numbers involving $\sqrt{5}$
  - `VECTOR_3`: (Implied but not shown in dependencies) Theorem about 3D vectors

### Porting notes
When porting this to another proof assistant:
1. Ensure the target system has a good representation of 3D vectors
2. Implement the cross product definition
3. If working with regular polyhedra, implement special handling for terms with $\sqrt{5}$
4. Consider whether the target system needs explicit conversion functions like this, or whether its simplification tactics already handle such calculations automatically

Note that some systems might have more powerful automation that makes dedicated conversions like this unnecessary.

---

## VECTOR3_EQ_0_CONV

### Name of formal statement
VECTOR3_EQ_0_CONV

### Type of the formal statement
Conversion function definition

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
`VECTOR3_EQ_0_CONV` is a conversion function that simplifies equations of the form:

$$\text{vector}[x_1;x_2;x_3] = \vec{0}$$

where $\text{vector}[x_1;x_2;x_3]$ represents a 3-dimensional vector with components $x_1, x_2, x_3$, and $\vec{0}$ is the zero vector in $\mathbb{R}^3$. This conversion rewrites such an equation to the conjunction:

$$x_1 = 0 \land x_2 = 0 \land x_3 = 0$$

and attempts to evaluate any rational arithmetic expressions within these components.

### Informal proof
The conversion is defined using a theorem `pth` which establishes that a 3D vector equals the zero vector if and only if all its components equal zero:

$$\text{vector}[x_1;x_2;x_3] = \vec{0} \iff x_1 = 0 \land x_2 = 0 \land x_3 = 0$$

The proof of this theorem proceeds as follows:
- First, it applies `SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3]` which:
  - Uses `CART_EQ` to establish that two vectors are equal if and only if all their components are equal
  - Uses `DIMINDEX_3` to specify that we're working with 3-dimensional vectors
  - Uses `FORALL_3` to convert a universal quantifier over a 3-element domain to a conjunction of three statements
- Then, it applies `REWRITE_TAC[VECTOR_3; VEC_COMPONENT]` to:
  - Use the definition of the `vector` constructor for 3D vectors
  - Use the definition of vector components for the zero vector

The conversion then:
1. Applies the theorem using `GEN_REWRITE_CONV I [pth]`
2. Evaluates any rational arithmetic expressions in the resulting equalities using `DEPTH_BINOP_CONV` with `REAL_RAT5_EQ_CONV`
3. Performs any final simplifications with `REWRITE_CONV[]`

### Mathematical insight
This conversion is a useful utility for working with 3D vectors in HOL Light. It automates the common operation of decomposing a vector equality with the zero vector into its component-wise equalities. This is particularly helpful in geometric proofs where we need to work with individual vector components.

The conversion handles not just the structural rewriting but also attempts to evaluate any rational arithmetic that might appear in the vector components, making it more powerful than a simple rewrite rule.

### Dependencies
- Theorems used in proof:
  - `CART_EQ`: Two vectors are equal iff their corresponding components are equal
  - `DIMINDEX_3`: The dimension of $\mathbb{R}^3$ is 3
  - `FORALL_3`: Transforms a universal quantifier over 3 elements into a conjunction
  - `VECTOR_3`: Definition of the vector constructor for 3D vectors
  - `VEC_COMPONENT`: Definition of components of vectors

- Conversion functions:
  - `GEN_REWRITE_CONV`: Generalized rewriting conversion
  - `DEPTH_BINOP_CONV`: Applies conversions deeply to binary operations
  - `REAL_RAT5_EQ_CONV`: Evaluates equality between real rational expressions
  - `REWRITE_CONV`: Basic rewriting conversion

### Porting notes
When porting to other systems:
- Ensure the target system has equivalent representations for 3D vectors
- The conversion might need to be adjusted based on how the target system handles conversions or simplifications
- The rational arithmetic evaluation might need separate handling depending on the target system's automation capabilities

---

## VECTOR3_DOT_CONV

### Name of formal statement
VECTOR3_DOT_CONV

### Type of the formal statement
Conversion function

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
`VECTOR3_DOT_CONV` is a conversion (rewriting) function that simplifies the dot product of two 3-dimensional vectors. It evaluates the dot product of two vectors `vector[x1;x2;x3]` and `vector[y1;y2;y3]` to the expression `x1*y1 + x2*y2 + x3*y3`.

### Informal proof
The conversion is constructed through the following steps:

1. First, a theorem `pth` is proved that establishes the formula for the dot product of two 3-dimensional vectors:
   ```
   (vector[x1;x2;x3]:real^3) dot (vector[y1;y2;y3]) = x1*y1 + x2*y2 + x3*y3
   ```
   This is proved by applying `REWRITE_TAC` with the theorems `DOT_3` and `VECTOR_3`, which provide the definitions of dot product and vector construction in 3 dimensions.

2. The conversion then applies a sequence of operations:
   * Rewrites using the theorem `pth` to convert the dot product into the sum of products
   * Applies `REAL_RAT5_MUL_CONV` to each multiplication operation in the resulting expression 
   * Applies `REAL_RAT5_ADD_CONV` to simplify the addition operations

The conversion is designed to handle expressions involving both rational numbers and terms with `sqrt(5)`, as indicated by the use of `REAL_RAT5_MUL_CONV` and `REAL_RAT5_ADD_CONV`.

### Mathematical insight
This conversion provides an efficient way to simplify dot product calculations for 3-dimensional vectors in HOL Light. It is particularly useful when working with vectors that have components involving rational numbers and square roots of 5.

The dot product is a fundamental operation in vector algebra, computing the scalar product of two vectors. For 3D vectors, it's defined as the sum of the products of corresponding components. This conversion automates the simplification of such expressions, especially when working with special number formats like those involving `sqrt(5)`.

The implementation shows how general mathematical operations can be efficiently encoded as conversions in HOL Light, combining basic simplification steps into a more powerful composite conversion.

### Dependencies
- **Theorems**:
  - `DOT_3`: Definition of dot product for 3-dimensional vectors
  - `VECTOR_3`: Definition of 3-dimensional vector construction
  - `REAL_RAT5_MUL_CONV`: Conversion for multiplying expressions involving rational numbers and `sqrt(5)`
  - `REAL_RAT5_ADD_CONV`: Conversion for adding expressions involving rational numbers and `sqrt(5)`

### Porting notes
When porting this to another system:
1. Ensure the system has appropriate definitions for 3D vectors and their dot product
2. Implement similar conversions for handling arithmetic with rational numbers and square roots
3. If the target system does not have a direct equivalent to HOL Light's conversion mechanisms, you might need to implement this as a tactic or simplification rule instead

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
The standard dodecahedron in $\mathbb{R}^3$ equals the convex hull of a set of 20 vertices, which consists of:
- The 8 vertices with coordinates $(\pm 1, \pm 1, \pm 1)$
- 12 additional vertices with coordinates containing the golden ratio and its inverse, specifically:
  - $(0, -\frac{1}{2}+\frac{\sqrt{5}}{2}, \frac{1}{2}+\frac{\sqrt{5}}{2})$, $(0, -\frac{1}{2}+\frac{\sqrt{5}}{2}, -\frac{1}{2}-\frac{\sqrt{5}}{2})$
  - $(0, \frac{1}{2}-\frac{\sqrt{5}}{2}, \frac{1}{2}+\frac{\sqrt{5}}{2})$, $(0, \frac{1}{2}-\frac{\sqrt{5}}{2}, -\frac{1}{2}-\frac{\sqrt{5}}{2})$
  - $(-\frac{1}{2}+\frac{\sqrt{5}}{2}, \frac{1}{2}+\frac{\sqrt{5}}{2}, 0)$, $(-\frac{1}{2}+\frac{\sqrt{5}}{2}, -\frac{1}{2}-\frac{\sqrt{5}}{2}, 0)$
  - $(\frac{1}{2}-\frac{\sqrt{5}}{2}, \frac{1}{2}+\frac{\sqrt{5}}{2}, 0)$, $(\frac{1}{2}-\frac{\sqrt{5}}{2}, -\frac{1}{2}-\frac{\sqrt{5}}{2}, 0)$
  - $(\frac{1}{2}+\frac{\sqrt{5}}{2}, 0, -\frac{1}{2}+\frac{\sqrt{5}}{2})$, $(-\frac{1}{2}-\frac{\sqrt{5}}{2}, 0, -\frac{1}{2}+\frac{\sqrt{5}}{2})$
  - $(\frac{1}{2}+\frac{\sqrt{5}}{2}, 0, \frac{1}{2}-\frac{\sqrt{5}}{2})$, $(-\frac{1}{2}-\frac{\sqrt{5}}{2}, 0, \frac{1}{2}-\frac{\sqrt{5}}{2})$

### Informal proof
The proof shows that the standard dodecahedron definition matches the given representation by transforming the original definition into the stated form. Key steps include:

- First, establish that the inverse of the golden ratio $\frac{1+\sqrt{5}}{2}$ equals $-\frac{1}{2}+\frac{\sqrt{5}}{2}$ by proving the lemma:
  $\left(\frac{1+\sqrt{5}}{2}\right)^{-1} = -\frac{1}{2}+\frac{\sqrt{5}}{2}$

- Expand the definition of `std_dodecahedron`, which involves vertices described using the golden ratio $p = \frac{1+\sqrt{5}}{2}$ and its inverse

- Substitute the proven form of the inverse of the golden ratio

- Rewrite expressions of the form $\frac{1+s}{2}$ as $\frac{1}{2}+\frac{s}{2}$

- Simplify negations using the identity: $-(a + b\sqrt{5}) = -a - b\sqrt{5}$

- Perform arithmetic reductions on rational terms

These transformations establish that the two sets of coordinates for the vertices are equivalent, and therefore the definitions are equal.

### Mathematical insight
This theorem provides a standard representation of the dodecahedron, one of the five Platonic solids, using explicit coordinates in $\mathbb{R}^3$. The vertices are expressed using a mixture of integer coordinates (for the 8 vertices of a cube) and coordinates involving the golden ratio $\phi = \frac{1+\sqrt{5}}{2}$ (for the remaining 12 vertices).

The dodecahedron has deep connections to symmetry groups, the golden ratio, and other mathematical structures. This particular representation makes explicit the relationship between the golden ratio and the geometry of the dodecahedron, which is a fundamental feature of this Platonic solid.

The theorem reformulates the original definition into a more standardized form, expressing all irrational components using the pattern $\pm\frac{1}{2}\pm\frac{\sqrt{5}}{2}$, which makes the coordinates more uniform and potentially easier to work with in various applications.

### Dependencies
- **Definitions**:
  - `std_dodecahedron`: The original definition of the standard dodecahedron

### Porting notes
When porting this theorem:
- Ensure that the golden ratio and its transformations are correctly handled
- Vector operations and the convex hull operation should be defined in the target system
- The proof is mostly computational, involving algebraic transformations, so it should be relatively straightforward to port using algebraic simplification tactics in the target system

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
The standard icosahedron in $\mathbb{R}^3$ is equal to the convex hull of the twelve points:
- $\left(0, 1, \frac{1}{2} + \frac{1}{2}\sqrt{5}\right)$
- $\left(0, 1, -\frac{1}{2} - \frac{1}{2}\sqrt{5}\right)$
- $\left(0, -1, \frac{1}{2} + \frac{1}{2}\sqrt{5}\right)$
- $\left(0, -1, -\frac{1}{2} - \frac{1}{2}\sqrt{5}\right)$
- $\left(1, \frac{1}{2} + \frac{1}{2}\sqrt{5}, 0\right)$
- $\left(1, -\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0\right)$
- $\left(-1, \frac{1}{2} + \frac{1}{2}\sqrt{5}, 0\right)$
- $\left(-1, -\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0\right)$
- $\left(\frac{1}{2} + \frac{1}{2}\sqrt{5}, 0, 1\right)$
- $\left(-\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0, 1\right)$
- $\left(\frac{1}{2} + \frac{1}{2}\sqrt{5}, 0, -1\right)$
- $\left(-\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0, -1\right)$

### Informal proof
The proof shows that this definition of the standard icosahedron is equivalent to its original definition in the system. The proof proceeds as follows:

1. We start by rewriting using the original definition of `std_icosahedron`, which defines it as the convex hull of 12 points in $\mathbb{R}^3$ with a parameter $p = \frac{1 + \sqrt{5}}{2}$ (the golden ratio).

2. The let-binding in the original definition is expanded using `let_CONV`.

3. The expression $\frac{1 + \sqrt{5}}{2}$ is rewritten as $\frac{1}{2} + \frac{1}{2}\sqrt{5}$ using basic arithmetic.

4. The negation of sums involving square roots is distributed appropriately: $-(a + b\sqrt{5}) = -a + (-b)\sqrt{5}$.

5. Rational number arithmetic is simplified using `REAL_RAT_REDUCE_CONV`.

This establishes that the given definition is equivalent to the standard definition of the icosahedron.

### Mathematical insight
The icosahedron is one of the five Platonic solids, having 20 triangular faces, 30 edges, and 12 vertices. This theorem presents a canonical representation of the standard icosahedron in $\mathbb{R}^3$. 

The vertices of the standard icosahedron have a specific pattern: they lie on three orthogonal golden rectangles. The coordinates use the golden ratio $\phi = \frac{1 + \sqrt{5}}{2} \approx 1.618$, which appears frequently in regular pentagons and various geometrical constructions.

The representation shown here places the icosahedron symmetrically around the origin, highlighting its geometric regularity and making it easier to work with in formal proofs about its properties.

### Dependencies
- **Definitions**:
  - `std_icosahedron`: The original definition of the standard icosahedron in $\mathbb{R}^3$

### Porting notes
When porting this theorem:
1. Ensure that your target system has support for real arithmetic, including square roots.
2. Verify that the convex hull operation is defined in your target system.
3. The proof relies heavily on term rewriting and conversion tactics that may need different approaches in other proof assistants.
4. Consider establishing lemmas about the golden ratio if working extensively with Platonic solids.

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
Let $f$ be a potential face of the convex hull of a finite set $s$ in $\mathbb{R}^3$. Then $f$ is a 2-dimensional face of $\text{convex hull}(s)$ if and only if:

There exist points $x, y, z \in s$ such that:
- Let $a = (z - x) \times (y - x)$ be the cross product
- $a \neq \vec{0}$
- Let $b = a \cdot x$
- Either all points $w \in s$ satisfy $a \cdot w \leq b$, or all points $w \in s$ satisfy $a \cdot w \geq b$
- $f = \text{convex hull}(s \cap \{x \mid a \cdot x = b\})$

Where $\times$ denotes the cross product, $\cdot$ denotes the dot product, and $\text{aff\_dim}(f) = 2$ indicates that $f$ has affine dimension 2 (i.e., $f$ is a 2-dimensional face).

### Informal proof
This theorem characterizes the 2-dimensional faces of a convex hull in $\mathbb{R}^3$ in terms of supporting hyperplanes.

We prove both directions:

**($\Rightarrow$)** Suppose $f$ is a 2-dimensional face of $\text{convex hull}(s)$:
- By `FACE_OF_CONVEX_HULL_SUBSET`, there exists a subset $t \subseteq s$ such that $f = \text{convex hull}(t)$.
- Since $\text{aff\_dim}(f) = 2$, we know $\text{aff\_dim}(\text{convex hull}(t)) = 2$.
- Applying `AFFINE_BASIS_EXISTS`, there exists an affine basis $u$ for $t$.
- Since the affine dimension is 2, $u$ must have exactly 3 elements (as $\text{aff\_dim}(u) = |u| - 1 = 2$).
- Let these three points be $x, y, z \in s$.
- Define $a = (z - x) \times (y - x)$.
- Since $\{x, y, z\}$ is affinely independent, $a \neq \vec{0}$ (by the contrapositive of `CROSS_EQ_0`).
- Define $b = a \cdot x$.
- We can verify that $a \cdot y = b$ and $a \cdot z = b$ (this follows from vector algebra).
- By the theory of faces of polyhedra (`EXPOSED_FACE_OF_POLYHEDRON`), $f$ must be the intersection of $\text{convex hull}(s)$ with a supporting hyperplane.
- This hyperplane must be of the form $\{x \mid a \cdot x = b\}$.
- Therefore, $f = \text{convex hull}(s) \cap \{x \mid a \cdot x = b\} = \text{convex hull}(s \cap \{x \mid a \cdot x = b\})$.
- All points in $s$ must lie on one side of the hyperplane, giving us the condition that either all $w \in s$ satisfy $a \cdot w \leq b$ or all $w \in s$ satisfy $a \cdot w \geq b$.

**($\Leftarrow$)** Conversely, given $x, y, z \in s$ with the stated properties:
- We first prove that $f = \text{convex hull}(s \cap \{x \mid a \cdot x = b\})$ is a face of $\text{convex hull}(s)$.
- We show that $\text{convex hull}(s \cap \{x \mid a \cdot x = b\}) = \text{convex hull}(s) \cap \{x \mid a \cdot x = b\}$ using properties of convex hulls and hyperplanes.
- If all $w \in s$ satisfy $a \cdot w \leq b$, then by `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE`, $f$ is a face of $\text{convex hull}(s)$.
- If all $w \in s$ satisfy $a \cdot w \geq b$, then by `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`, $f$ is a face of $\text{convex hull}(s)$.
- Finally, we show that $\text{aff\_dim}(f) = 2$:
  * Since $f \subseteq \{x \mid a \cdot x = b\}$, we have $\text{aff\_dim}(f) \leq \text{aff\_dim}(\{x \mid a \cdot x = b\}) = 2$.
  * Since $\{x, y, z\}$ is affinely independent and contained in $f$, $\text{aff\_dim}(f) \geq \text{aff\_dim}(\{x, y, z\}) = 2$.
  * Therefore, $\text{aff\_dim}(f) = 2$.

### Mathematical insight
This theorem provides an explicit computational characterization of the 2-dimensional faces (facets) of a convex polyhedron in $\mathbb{R}^3$ represented as the convex hull of a finite set of points. 

The key insight is that each 2D face can be identified by:
1. Three affinely independent points from the original set
2. The plane passing through these points (defined by the normal vector $a$ and constant $b$)
3. The requirement that all points of the original set lie on one side of this plane

This characterization is particularly useful for computational geometry applications, as it provides a concrete way to enumerate all 2D faces of a polyhedron based on the original set of points. It also illustrates the fundamental relationship between faces of a polyhedron and supporting hyperplanes.

### Dependencies
- **Theorems**:
  - `CROSS_EQ_0`: Relates cross products to collinearity: $x \times y = \vec{0} \iff \text{collinear}\{\vec{0}, x, y\}$
  - `FACE_OF_CONVEX_HULL_SUBSET`
  - `AFFINE_BASIS_EXISTS`
  - `EXPOSED_FACE_OF_POLYHEDRON`
  - `CONVEX_HULL_UNION_NONEMPTY_EXPLICIT`
  - `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE`
  - `FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE`
  - `CONNECTED_IVT_HYPERPLANE`
  - Various affine dimension theorems

- **Definitions**:
  - `cross`: Cross product of two vectors in $\mathbb{R}^3$

### Porting notes
- The proof relies heavily on vector operations in $\mathbb{R}^3$ (cross products) and properties of convex polyhedra.
- Special attention should be paid to the handling of affine dimensions and the characterization of faces through supporting hyperplanes.
- The `VEC3_TAC` tactic is used for reasoning about vector equations in 3D space and might need custom implementation in other proof assistants.
- The proof uses the concept of "exposed faces" which might be defined differently in other systems.

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
For any face $f$, vertex $v$, sets $s$ and $t$ of vectors in $\mathbb{R}^3$, the following are equivalent:

1. There exist $x, y, z \in (v \cup s)$ such that:
   - Let $a = (z - x) \times (y - x)$, where $\times$ denotes the cross product
   - $a \neq \vec{0}$
   - Let $b = a \cdot x$, where $\cdot$ denotes the dot product
   - Either $\forall w \in t, a \cdot w \leq b$ or $\forall w \in t, a \cdot w \geq b$
   - $f = \text{convex hull}(t \cap \{x \mid a \cdot x = b\})$

2. Either:
   - There exist $y, z \in s$ such that:
     - Let $a = (z - v) \times (y - v)$
     - $a \neq \vec{0}$
     - Let $b = a \cdot v$
     - Either $\forall w \in t, a \cdot w \leq b$ or $\forall w \in t, a \cdot w \geq b$
     - $f = \text{convex hull}(t \cap \{x \mid a \cdot x = b\})$
   
   Or:
   
   - There exist $x, y, z \in s$ such that:
     - Let $a = (z - x) \times (y - x)$
     - $a \neq \vec{0}$
     - Let $b = a \cdot x$
     - Either $\forall w \in t, a \cdot w \leq b$ or $\forall w \in t, a \cdot w \geq b$
     - $f = \text{convex hull}(t \cap \{x \mid a \cdot x = b\})$

### Informal proof
This theorem simplifies the conditions for defining a face by analyzing the possible combinations of points from the set $v \cup s$. The proof proceeds as follows:

* First, we rewrite the set notation $v \cup s$ using the HOL Light `IN_INSERT` predicate.

* We then apply a general logical principle (via `MATCH_MP_TAC`) that states:
  - If $Q(x,y,z)$ is symmetric in the sense that $Q(x,y,z) \Rightarrow Q(x,z,y)$ and $Q(x,y,z) \Rightarrow Q(y,x,z)$
  - And $Q(x,x,z)$ is always false
  - Then the condition "there exist $x,y,z$ with $(x=v \vee P(x)) \wedge (y=v \vee P(y)) \wedge (z=v \vee P(z)) \wedge Q(x,y,z)$" is equivalent to "there exist $y,z$ with $P(y) \wedge P(z) \wedge Q(v,y,z)$ OR there exist $x,y,z$ with $P(x) \wedge P(y) \wedge P(z) \wedge Q(x,y,z)$"

* We convert all the let-expressions to prepare for simplification.

* A key step involves using the fact that $\vec{0} \times \vec{v} = \vec{0}$ and $\vec{v} \times \vec{0} = \vec{0}$ for any vector $\vec{v}$ (from `CROSS_0`), so when the two vectors used in the cross product are equal (as in $z-x=0$ when $z=x$), the cross product is zero.

* We use vector identities to handle different arrangements of the cross product:
  - $(z-y) \times (x-y) = -((z-x) \times (y-x))$
  - $(y-x) \times (z-x) = -((z-x) \times (y-x))$

* These identities allow us to standardize the form of the expressions.

* Finally, we use the property that for any vectors $x$, $y$, and $z$, the dot product $((z-x) \times (y-x)) \cdot y = ((z-x) \times (y-x)) \cdot x$, which shows that the plane equation $a \cdot x = b$ is preserved regardless of which point we choose as the reference point among $x$, $y$, and $z$.

* After simplifying negations of inequalities and reorganizing disjunctions, we obtain the desired equivalence.

### Mathematical insight
This theorem is a simplification step in the computation of faces of a convex hull. It characterizes when a subset forms a face by examining the possible combinations of points that define a supporting hyperplane.

The key insight is that when we have a set $v \cup s$, where $v$ is a distinguished vertex, we can categorize the faces based on whether the vertex $v$ is used in defining the supporting hyperplane:
1. Cases where $v$ is one of the three points defining the plane
2. Cases where all three points come from $s$

The theorem shows that from the original complex condition involving points from $v \cup s$, we can derive a cleaner, case-based characterization that separates the role of the vertex $v$.

The supporting hyperplane defined by $a \cdot x = b$ (where $a$ is normal to the plane) divides space such that the convex set lies entirely on one side. The face is then the intersection of the convex hull with this hyperplane.

### Dependencies
#### Theorems:
- `CROSS_0`: States that $\vec{0} \times \vec{v} = \vec{0}$ and $\vec{v} \times \vec{0} = \vec{0}$ for any vector $\vec{v}$

#### Definitions:
- `cross`: Defines the cross product for vectors in $\mathbb{R}^3$ as $a \times b = [a_2 \cdot b_3 - a_3 \cdot b_2, a_3 \cdot b_1 - a_1 \cdot b_3, a_1 \cdot b_2 - a_2 \cdot b_1]$

### Porting notes
When porting this theorem:
1. Ensure that the cross product and dot product operations are properly defined for 3D vectors.
2. The proof makes heavy use of vector identities related to cross products - these should be established first.
3. The let-expressions in HOL Light are used for readability but are immediately expanded in the proof. In other systems, you might need to handle this differently.
4. The proof uses vector pattern matching (via `VEC3_RULE`) which might need different approaches in other systems.
5. The simplification of Boolean expressions with quantifiers might require specific tactics or lemmas in other proof assistants.

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
For any face $f$, vectors $u$, $v$, and set $s$ in $\mathbb{R}^3$, the following statements are equivalent:

There exist $y, z \in \{u\} \cup s$ such that:
- Let $a = (z - v) \times (y - v)$
- $a \neq \vec{0}$
- Let $b = a \cdot v$
- Either $\forall w \in t, a \cdot w \leq b$ or $\forall w \in t, a \cdot w \geq b$
- $f = \text{convex hull}(t \cap \{x \mid a \cdot x = b\})$

if and only if either:

There exists $z \in s$ such that:
- Let $a = (z - v) \times (u - v)$
- $a \neq \vec{0}$
- Let $b = a \cdot v$
- Either $\forall w \in t, a \cdot w \leq b$ or $\forall w \in t, a \cdot w \geq b$
- $f = \text{convex hull}(t \cap \{x \mid a \cdot x = b\})$

Or:

There exist $y, z \in s$ such that:
- Let $a = (z - v) \times (y - v)$
- $a \neq \vec{0}$
- Let $b = a \cdot v$
- Either $\forall w \in t, a \cdot w \leq b$ or $\forall w \in t, a \cdot w \geq b$
- $f = \text{convex hull}(t \cap \{x \mid a \cdot x = b\})$

### Informal proof
This theorem is essentially rewriting the condition involving $y$ and $z$ from $\{u\} \cup s$ into separate cases where either one or neither of $y$ and $z$ equals $u$.

The proof proceeds as follows:

- Begin with universal quantification over $f$, $u$, $v$, and $s$.
- Expand the definition of $\in$ for the INSERT operation.
- Apply a meta-level lemma (via MATCH_MP_TAC) that states the following:
  - If for all $x, y$, we have $Q(x, y) \implies Q(y, x)$ (symmetry),
  - And for all $x$, we have $\neg Q(x, x)$ (irreflexivity),
  - Then $(\exists y, z. (y = u \lor P(y)) \land (z = u \lor P(z)) \land Q(y, z))$ is equivalent to
    $(\exists z. P(z) \land Q(u, z)) \lor (\exists y, z. P(y) \land P(z) \land Q(y, z))$

- The proof then converts let-expressions to their actual meanings.
- We use the property `CROSS_REFL` to establish that $x \times x = \vec{0}$, which helps establish the irreflexivity condition.
- For symmetry, we use a vector identity: $(x - v) \times (y - v) = -((y - v) \times (x - v))$
- We then handle the negation of the cross product and the dot product with a negated vector through appropriate rewrite rules.
- Finally, associative-commutative normalization of disjunction completes the proof.

### Mathematical insight
This theorem is a step in computing faces of a convex hull, specifically dealing with the classification of faces based on normal vectors. The key insight is a case analysis of when points are taken from either the set $s$ or the singleton set $\{u\}$.

The theorem essentially breaks down the original condition where $y$ and $z$ can come from $\{u\} \cup s$ into three cases:
1. Both $y$ and $z$ are equal to $u$ - this case is ruled out because $(u-v) \times (u-v) = \vec{0}$
2. Exactly one of $y$ or $z$ equals $u$ - this corresponds to the first disjunct
3. Neither $y$ nor $z$ equals $u$ - this corresponds to the second disjunct

The vectors $a = (z - v) \times (y - v)$ represent normal vectors to planes, and this theorem helps organize the search for face-defining planes in the computation of convex hulls.

### Dependencies
#### Theorems
- `CROSS_REFL`: For any vector $x$ in $\mathbb{R}^3$, $x \times x = \vec{0}$

#### Definitions
- `cross`: The cross product of two vectors in $\mathbb{R}^3$, defined as $(a \times b) = [a_2 b_3 - a_3 b_2, a_3 b_1 - a_1 b_3, a_1 b_2 - a_2 b_1]$

### Porting notes
When porting this theorem:
1. Ensure your system has a similar cross product definition for 3D vectors
2. The proof relies on case analysis with a meta-level logical argument - you may need to adapt this approach to fit your proof system's mechanisms
3. The let-expressions in HOL Light are used for readability but are expanded in the proof - you'll need to handle similar expressions according to your system's conventions
4. The vector algebra identities, particularly about cross products and dot products with negated vectors, will need appropriate equivalents in your system

---

## COMPUTE_FACES_TAC

### COMPUTE_FACES_TAC

### Type of the formal statement
- theorem (a tactic implementation)

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
`COMPUTE_FACES_TAC` is a specialized HOL Light tactic designed to simplify the task of computing 2-dimensional faces of convex hulls of finite sets in 3D space. This tactic applies the theorem `COMPUTE_FACES_2` and implements a series of simplification steps to systematically compute face representations.

The tactic performs the following operations:
1. Simplifies expressions using `COMPUTE_FACES_2` and finite set properties
2. Applies step-by-step simplifications via `COMPUTE_FACES_2_STEP_1` and `COMPUTE_FACES_2_STEP_2`
3. Performs vector manipulations using specialized conversions like `VECTOR3_SUB_CONV`, `VECTOR3_CROSS_CONV`
4. Evaluates vector dot products and equality tests
5. Simplifies real number inequalities using `REAL_RAT5_LE_CONV`
6. Normalizes set expressions and disjunctions

### Informal proof
This is a tactic definition rather than a theorem, so there is no formal proof to translate. The tactic is constructed as a sequence of simplification steps that:

1. Begins by applying `COMPUTE_FACES_2` which characterizes 2-dimensional faces of convex hulls in terms of supporting hyperplanes defined by three points
2. Simplifies the resulting expression by applying the derived lemmas `COMPUTE_FACES_2_STEP_1` and `COMPUTE_FACES_2_STEP_2` which decompose the case analysis
3. Handles set operations on empty sets
4. Applies specialized vector conversions to compute:
   - Vector subtractions (`VECTOR3_SUB_CONV`)
   - Cross products (`VECTOR3_CROSS_CONV`)
   - Dot products (`VECTOR3_DOT_CONV`)
   - Vector equality tests (`VECTOR3_EQ_0_CONV`)
5. Evaluates inequalities involving $\sqrt{5}$ using `REAL_RAT5_LE_CONV`
6. Performs a series of set-theoretic simplifications using the proved lemma:
   ```
   (x INSERT s) INTER {x | P x} =
     if P x then x INSERT (s INTER {x | P x})
     else s INTER {x | P x}
   ```
7. Normalizes set expressions and logical disjunctions

### Mathematical insight
This tactic implements a computational approach to identifying 2-dimensional faces of polyhedra in 3D space. It leverages the geometric characterization that each face of a convex polyhedron is formed by a supporting hyperplane.

The key mathematical insight is that a 2-dimensional face of a convex hull can be identified by finding three points that define a plane, and then checking whether all other points in the set lie on one side of this plane. The face is then the convex hull of all points that lie exactly on this plane.

The tactic automates this process by handling the combinatorial case analysis (considering different triples of points) and performing the necessary vector calculations (cross products to find normal vectors, dot products to define hyperplanes).

This tactic is particularly useful when working with platonic solids and other polyhedra, as it provides an automated way to enumerate their faces based on their vertex sets.

### Dependencies
- **Theorems**:
  - `COMPUTE_FACES_2`: Characterizes 2D faces of 3D convex hulls
  - `COMPUTE_FACES_2_STEP_1`: Simplifies case analysis for triples of points
  - `COMPUTE_FACES_2_STEP_2`: Further simplifies case analysis for pairs of points
  - `REAL_RAT5_LE_CONV`: Handles inequalities involving $\sqrt{5}$
  - `VECTOR3_SUB_CONV`: Computes vector subtraction in 3D
  - `VECTOR3_CROSS_CONV`: Computes cross products in 3D
  - `VECTOR3_EQ_0_CONV`: Tests if a 3D vector equals zero
  - `VECTOR3_DOT_CONV`: Computes dot products in 3D

### Porting notes
When porting this tactic to another system:

1. The approach relies heavily on dynamic conversions that directly compute vector operations. In systems without conversion-based rewriting, you might need to implement these operations differently.

2. The tactic is heavily specialized for 3D geometry with real-valued coordinates. You'll need equivalent vector operations in the target system.

3. The special treatment of expressions involving $\sqrt{5}$ through `REAL_RAT5_LE_CONV` might require a different approach in other systems. Some systems have better support for deciding expressions involving square roots.

4. The implementation depends on incremental simplification and case analysis. In systems with more powerful automation, some of these steps might be combined or handled differently.

---

## TETRAHEDRON_FACETS

### TETRAHEDRON_FACETS
- TETRAHEDRON_FACETS

### Type of the formal statement
- theorem

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
This theorem characterizes the 2-dimensional faces of the standard tetrahedron. Specifically, it states that for any set $f \subset \mathbb{R}^3$:

$f$ is a face of the standard tetrahedron with affine dimension 2 if and only if $f$ equals one of the following four triangular faces:
- The convex hull of $\{(-1,-1,1), (-1,1,-1), (1,-1,-1)\}$
- The convex hull of $\{(-1,-1,1), (-1,1,-1), (1,1,1)\}$
- The convex hull of $\{(-1,-1,1), (1,-1,-1), (1,1,1)\}$
- The convex hull of $\{(-1,1,-1), (1,-1,-1), (1,1,1)\}$

Here, the standard tetrahedron is defined as the convex hull of the four vertices $\{(1,1,1), (-1,-1,1), (-1,1,-1), (1,-1,-1)\}$ in $\mathbb{R}^3$.

### Informal proof
This theorem is proven by direct computation using the `COMPUTE_FACES_TAC` tactic, which is specifically designed to compute the faces of polyhedra.

In particular:
- We start with the definition of the standard tetrahedron as the convex hull of $\{(1,1,1), (-1,-1,1), (-1,1,-1), (1,-1,-1)\}$
- The `COMPUTE_FACES_TAC` performs a series of computations to determine all faces with affine dimension 2
- This tactic handles set operations, vector operations (dot products, cross products), and logical simplifications
- The computation identifies the four triangular faces that make up the boundary of the tetrahedron

### Mathematical insight
The theorem provides an explicit characterization of all the 2-dimensional faces (facets) of the standard tetrahedron. These facets are triangles, which is expected since a tetrahedron has four triangular faces.

The standard tetrahedron used here is not the regular tetrahedron with vertices at the origin and three points on the coordinate axes. Instead, it uses vertices with coordinates $\pm 1$, positioned symmetrically in 3D space.

This result is part of a broader effort to formalize properties of Platonic solids in HOL Light. The explicit enumeration of faces is particularly useful for proving various geometric properties of polyhedra, as it allows for direct computation and verification of properties face-by-face.

### Dependencies
- **Definitions**:
  - `std_tetrahedron`: Defines the standard tetrahedron as the convex hull of four specific points in $\mathbb{R}^3$
- **Theorems**:
  - `COMPUTE_FACES_TAC`: A complex tactic that computes the faces of polyhedra defined by their vertices

### Porting notes
When porting this theorem to another system:
1. Ensure that the definition of the standard tetrahedron matches exactly
2. Be aware that the proof relies heavily on computational tactics specific to HOL Light
3. In systems without such specialized tactics, you may need to prove this result using more manual reasoning about convex hulls and face relationships
4. The proof might require explicit handling of vector operations and set-theoretic manipulations in other systems
5. Consider whether the target system has libraries for computational geometry or convex polyhedra that could simplify the proof

---

## CUBE_FACETS

### CUBE_FACETS

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
For any set $f$ in $\mathbb{R}^3$, $f$ is a 2-dimensional face of the standard cube if and only if $f$ equals one of the following six convex hulls (which represent the six faces of a cube):
1. $\text{conv}\{(-1,-1,-1), (-1,-1,1), (-1,1,-1), (-1,1,1)\}$
2. $\text{conv}\{(-1,-1,-1), (-1,-1,1), (1,-1,-1), (1,-1,1)\}$
3. $\text{conv}\{(-1,-1,-1), (-1,1,-1), (1,-1,-1), (1,1,-1)\}$
4. $\text{conv}\{(-1,-1,1), (-1,1,1), (1,-1,1), (1,1,1)\}$
5. $\text{conv}\{(-1,1,-1), (-1,1,1), (1,1,-1), (1,1,1)\}$
6. $\text{conv}\{(1,-1,-1), (1,-1,1), (1,1,-1), (1,1,1)\}$

where the standard cube is defined as the convex hull of the eight vertices $\{(\pm 1, \pm 1, \pm 1)\}$ in $\mathbb{R}^3$.

### Informal proof
The proof uses computational methods to enumerate and verify all the 2-dimensional faces of the standard cube:

1. First, we rewrite the term using the definition of `std_cube`, which is defined as the convex hull of the eight vertices $\{(\pm 1, \pm 1, \pm 1)\}$.

2. Then we apply `COMPUTE_FACES_TAC`, which is a tactic that:
   - Uses set-theoretic operations and properties of convex hulls to compute all the faces
   - Performs vector operations (dot products, cross products) to determine face equations
   - Handles the symbolic representation of the faces
   - Simplifies and normalizes the results to obtain the canonical representation of each face

The tactic systematically computes all faces of the cube, verifies which ones have affine dimension 2 (i.e., which ones are facets), and proves that they are exactly the six squares that form the boundary of the cube.

### Mathematical insight
This theorem provides a complete characterization of the 2-dimensional faces (facets) of the standard cube in $\mathbb{R}^3$. The standard cube has exactly six facets, each being a square in one of the coordinate planes.

These facets correspond to the six faces of the cube where one coordinate is fixed at either +1 or -1. Specifically:
1. The face where x = -1 (left face)
2. The face where y = -1 (bottom face)
3. The face where z = -1 (back face)
4. The face where z = 1 (front face)
5. The face where y = 1 (top face)
6. The face where x = 1 (right face)

This result is fundamental for understanding the combinatorial structure of the cube as a convex polytope, which has 8 vertices, 12 edges, and 6 facets, consistent with Euler's formula for polyhedra: V - E + F = 2.

### Dependencies
- **Definitions**:
  - `std_cube`: Definition of the standard cube as the convex hull of the eight vertices $\{(\pm 1, \pm 1, \pm 1)\}$ in $\mathbb{R}^3$.

- **Tactics**:
  - `COMPUTE_FACES_TAC`: A composite tactic that computes the faces of polyhedra.

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the definition of the standard cube as the convex hull of eight specific points is properly translated.
2. The proof heavily relies on computational tactics. In other systems, you may need to:
   - Implement similar computational approaches for face enumeration
   - Or alternatively, prove this result more explicitly by showing that each proposed facet satisfies the face conditions, and that no other 2-dimensional faces exist
3. The representation of vectors and convex hulls may differ between systems, requiring appropriate adaptations.

---

## OCTAHEDRON_FACETS

### OCTAHEDRON_FACETS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
A subset $f$ of $\mathbb{R}^3$ is a 2-dimensional face of the standard octahedron if and only if $f$ is equal to one of the following eight triangular faces:
1. The convex hull of $\{(-1,0,0), (0,-1,0), (0,0,-1)\}$
2. The convex hull of $\{(-1,0,0), (0,-1,0), (0,0,1)\}$
3. The convex hull of $\{(-1,0,0), (0,1,0), (0,0,-1)\}$
4. The convex hull of $\{(-1,0,0), (0,1,0), (0,0,1)\}$
5. The convex hull of $\{(1,0,0), (0,-1,0), (0,0,-1)\}$
6. The convex hull of $\{(1,0,0), (0,-1,0), (0,0,1)\}$
7. The convex hull of $\{(1,0,0), (0,1,0), (0,0,-1)\}$
8. The convex hull of $\{(1,0,0), (0,1,0), (0,0,1)\}$

Where the standard octahedron is defined as the convex hull of the six points $\{(1,0,0), (-1,0,0), (0,0,1), (0,0,-1), (0,1,0), (0,-1,0)\}$.

### Informal proof
This theorem is proved using the custom tactic `COMPUTE_FACES_TAC` which is specifically designed to compute the faces of polyhedra. 

The proof works by:
- Starting with the definition of the standard octahedron as the convex hull of the six points
- Using techniques from convex geometry to identify all 2-dimensional faces
- The tactic performs a series of symbolic computations, including:
  - Computing intersections of sets
  - Computing vector cross products and dot products
  - Simplifying expressions and checking geometric conditions that characterize faces

The fact that the octahedron has exactly eight triangular faces follows from the structure of the standard octahedron, which has vertices at unit distances along the coordinate axes.

### Mathematical insight
The standard octahedron is one of the five Platonic solids. It has 8 faces (all of which are equilateral triangles), 6 vertices, and 12 edges. 

Each face is determined by three vertices. The theorem explicitly enumerates all 8 faces, each being the convex hull of a set of three vertices. These faces can be viewed as triangular pyramids, with each pyramid having three of the octahedron's vertices as its base.

The triangular faces are arranged in a highly symmetric manner. Each face corresponds to a particular choice of sign (positive or negative) for each coordinate axis. This regular structure is what makes the octahedron a Platonic solid - it is vertex-transitive, edge-transitive, and face-transitive.

### Dependencies
- **Definitions**: `std_octahedron` - defines the standard octahedron as the convex hull of six unit vectors along the coordinate axes
- **Theorems**: `COMPUTE_FACES_TAC` - a specialized tactic for computing faces of polyhedra

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that the notion of "face" and "convex hull" are properly defined in the target system
2. The affine dimension (`aff_dim`) should be defined appropriately - in this case, 2-dimensional faces are being characterized
3. The proof might be more straightforward in systems with better support for computational geometry
4. Instead of using the custom tactic, you might need to derive the faces through more explicit geometric arguments in other systems

Assistant systems with built-in support for computational geometry or automated geometric reasoning might be able to simplify this proof significantly.

---

## ICOSAHEDRON_FACETS

### ICOSAHEDRON_FACETS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any set $f \subset \mathbb{R}^3$, the following are equivalent:
- $f$ is a face of the standard icosahedron and has affine dimension 2
- $f$ is one of the 20 triangular facets described by the convex hull of specific triples of vertices

Where the standard icosahedron is defined as the convex hull of 12 vertices in $\mathbb{R}^3$, with coordinates involving $\frac{1}{2} + \frac{1}{2}\sqrt{5}$ and $-\frac{1}{2} - \frac{1}{2}\sqrt{5}$.

### Informal proof
This theorem establishes that the standard icosahedron has exactly 20 triangular facets, each specified by the convex hull of three vertices.

The proof applies computational methods to determine all the faces of the icosahedron:

- The proof uses `COMPUTE_FACES_TAC`, a specialized tactic designed to compute the faces of polyhedral solids
- It applies this tactic to the standard icosahedron definition from `STD_ICOSAHEDRON`
- The tactic works by:
  - Computing all possible combinations of vertices that could form faces
  - Checking which combinations satisfy the geometric conditions for being a face
  - Verifying the affine dimension to identify the 2-dimensional faces (facets)

The computation verifies that exactly the 20 triangular facets listed in the theorem statement are the 2-dimensional faces of the standard icosahedron.

### Mathematical insight
The icosahedron is one of the five Platonic solids, with 20 triangular faces, 30 edges, and 12 vertices. This theorem explicitly characterizes all 20 triangular facets by listing the exact coordinates of their vertices.

The standard icosahedron used here has vertices placed at specific coordinates involving the golden ratio $\phi = \frac{1+\sqrt{5}}{2}$, which appears in the vertex coordinates as $\frac{1}{2} + \frac{1}{2}\sqrt{5}$.

This result is important for:
1. Providing a complete characterization of the icosahedron's faces
2. Enabling further geometric analysis of the icosahedron's properties
3. Serving as a building block for more complex geometric results

The proof demonstrates how computational methods can be used to verify combinatorial properties of geometric objects in a formal proof system.

### Dependencies
- Theorems:
  - `STD_ICOSAHEDRON`: Defines the standard icosahedron as the convex hull of 12 specific vertices
  - `COMPUTE_FACES_TAC`: A tactic for computing faces of polyhedral solids
- Definitions:
  - `std_icosahedron`: The formal definition of the standard icosahedron

### Porting notes
When porting this to other proof assistants:
1. Implement the 12 vertices of the icosahedron first
2. The computation of faces may require specialized tactics in the target system
3. Consider using more efficient representations or symmetry arguments to reduce the computational burden
4. Many systems might struggle with the exact verification of all 20 faces due to the complexity of the computation
5. The use of the golden ratio (appearing as $\frac{1}{2} + \frac{1}{2}\sqrt{5}$) may require special handling in systems with different real number representations

---

## DODECAHEDRON_FACETS

### DODECAHEDRON_FACETS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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

For any set $f \subseteq \mathbb{R}^3$, $f$ is a 2-dimensional face of the standard dodecahedron if and only if $f$ equals one of the 12 specific convex hulls listed in the statement. Each convex hull represents one of the pentagonal faces of the dodecahedron, defined by its 5 vertices.

Specifically, the theorem states:
$$\forall f \subseteq \mathbb{R}^3. (f \text{ face_of } \text{std\_dodecahedron} \land \text{aff\_dim}(f) = 2) \iff f \in \{F_1, F_2, \ldots, F_{12}\}$$

where each $F_i$ is the convex hull of 5 specific vertices of the standard dodecahedron.

### Informal proof

The proof uses the standard definition of the dodecahedron (from `STD_DODECAHEDRON`) and then applies a specialized tactic `COMPUTE_FACES_TAC` to compute all 2-dimensional faces.

The tactic works by:
1. Using geometric computations to determine which sets of vertices form 2-dimensional faces
2. Computing the convex hulls of these vertex sets
3. Verifying that each computed face satisfies the face-of relation and has the correct affine dimension

The complete enumeration of all 12 pentagonal faces is produced by systematically analyzing the combinatorial structure of the dodecahedron's vertex set, and computing which subsets of vertices form proper 2-dimensional faces.

### Mathematical insight

The dodecahedron is one of the five Platonic solids and has 12 pentagonal faces, 30 edges, and 20 vertices. This theorem provides an explicit enumeration of all 12 pentagonal faces in terms of their vertex coordinates in $\mathbb{R}^3$.

The coordinates involve the golden ratio $\varphi = \frac{1 + \sqrt{5}}{2}$, which appears in the standard construction of the dodecahedron. The theorem uses the inverse of the golden ratio ($\frac{-1 + \sqrt{5}}{2}$) in several vertex coordinates, which is a characteristic feature of the dodecahedron's geometry.

This theorem is essential for formal analysis of the dodecahedron's geometric properties and for proving further results about this Platonic solid.

### Dependencies
- Definitions:
  - `std_dodecahedron`: Definition of the standard dodecahedron in terms of the convex hull of 20 specific points in 3D space, related to the golden ratio.
- Theorems:
  - `STD_DODECAHEDRON`: Explicit coordinate representation of the standard dodecahedron.
  - `COMPUTE_FACES_TAC`: A specialized tactic for computing the faces of polyhedra.

### Porting notes
When porting this theorem:
1. Ensure that the definition of the standard dodecahedron using the golden ratio is properly translated.
2. The coordinates involve algebraic numbers (with $\sqrt{5}$), so the target system needs to handle such expressions.
3. The full enumeration of the 12 faces is verbose - consider generating them programmatically if the target system supports it.
4. The proof relies heavily on computational geometry - in another system, you might need different tactics to verify these geometric facts.
5. Alternative approaches might involve using symmetry arguments to reduce the number of cases that need to be directly computed.

---

## COPLANAR_HYPERPLANE_RULE

### COPLANAR_HYPERPLANE_RULE

### Type of the formal statement
Theorem (also functioning as a conversion rule)

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
`COPLANAR_HYPERPLANE_RULE` is a theorem-producing rule that, given a set of points in $\mathbb{R}^3$ represented as a set enumeration, returns a theorem stating that all points in the set lie on the same plane (hyperplane in $\mathbb{R}^3$).

More precisely, given a set $s$ of at least 3 points in $\mathbb{R}^3$, it returns a theorem of the form:

$$\forall x \in \mathbb{R}^3. x \in s \Rightarrow n \cdot x = d$$

where $n$ is a normal vector to the plane and $d$ is a real constant. This equation $n \cdot x = d$ defines the plane containing all points in $s$.

### Informal proof
The rule works as follows:

- First, it defines a helper function `allsets` that produces all subsets of size $m$ from a list $l$.

- For any three points $x$, $y$, and $z$ in $\mathbb{R}^3$, it computes a normal vector to the plane containing them using the cross product: $n = (y-x) \times (z-x)$.

- Given a set of points $s$ with at least 3 elements:
  - It tries to find a subset of 3 points that produces a non-zero normal vector.
  - Using this normal vector $n$ and any point in the set (it takes the first one), it computes the constant $d = n \cdot \text{(first point)}$.
  - It then proves that all points in $s$ satisfy the equation $n \cdot x = d$, showing they all lie on the same plane.

The actual proof is constructed by:
1. Instantiating a template formula `∀x. x ∈ s ⇒ n·x = d` with the computed values.
2. Using set reasoning to expand the formula for each point in the set.
3. Evaluating the dot product for each point and showing it equals $d$.
4. Combining these individual proofs to establish the overall theorem.

### Mathematical insight
This rule embodies a fundamental fact from analytic geometry: a set of points in $\mathbb{R}^3$ is coplanar if and only if they all satisfy a linear equation of the form $n \cdot x = d$, where $n$ is the normal vector to the plane.

The approach uses cross products to find the normal vector to the plane. The cross product $(y-x) \times (z-x)$ gives a vector perpendicular to both $(y-x)$ and $(z-x)$, which are vectors in the plane. This normal vector defines the orientation of the plane, while the constant $d$ determines its position in space.

The rule is particularly useful for geometric reasoning about polyhedra and other 3D objects in HOL Light, as it automatically generates the equation of a plane containing a given set of points.

### Dependencies
- Theorems:
  - `VECTOR3_SUB_CONV`: Conversion for vector subtraction in $\mathbb{R}^3$
  - `VECTOR3_CROSS_CONV`: Conversion for cross product in $\mathbb{R}^3$
  - `VECTOR3_DOT_CONV`: Conversion for dot product in $\mathbb{R}^3$
- Definitions:
  - `cross`: Definition of cross product in $\mathbb{R}^3$

### Porting notes
When porting to other systems:
- Ensure the target system has appropriate vector operations for $\mathbb{R}^3$.
- Consider how the system handles set enumerations and reasoning about membership.
- The approach relies on constructing proofs programmatically, so you'll need equivalent mechanisms in the target system.
- Note that this function assumes the input set has at least 3 non-collinear points (to produce a non-zero normal vector).

---

## COMPUTE_FACES_1

### COMPUTE_FACES_1
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem provides a characterization of 1-dimensional faces of the convex hull of a set in $\mathbb{R}^3$ that lies in a hyperplane.

Given a set $s \subset \mathbb{R}^3$, a normal vector $n \in \mathbb{R}^3$, and a real number $d$, if:
1. Every point $x \in s$ satisfies $n \cdot x = d$ (meaning $s$ lies in a hyperplane)
2. $s$ is finite
3. $n \neq 0$ (the normal vector is non-zero)

Then for any set $f$, the following are equivalent:
- $f$ is a face of the convex hull of $s$ with affine dimension 1
- There exist points $x, y \in s$ such that, setting $a = n \times (y - x)$ and $b = a \cdot x$:
  * $a \neq 0$
  * Either $\forall w \in s, a \cdot w \leq b$ or $\forall w \in s, a \cdot w \geq b$
  * $f = \text{convex hull}(s \cap \{z | a \cdot z = b\})$

### Informal proof
We need to prove the equivalence of two statements about a set $f$ being a 1-dimensional face of the convex hull of $s$. 

**First direction: $\Rightarrow$**
Assume $f$ is a face of $\text{convex hull}(s)$ with $\text{aff_dim}(f) = 1$.

- By `FACE_OF_CONVEX_HULL_SUBSET`, there exists a subset $t \subseteq s$ such that $f = \text{convex hull}(t)$.
- Since $\text{aff_dim}(f) = 1$, applying `AFFINE_BASIS_EXISTS`, there exists an affine basis $u$ for $t$.
- Since $\text{aff_dim}(u) = 1$ and $\text{aff_dim}(u) = \text{CARD}(u) - 1$ for an affine basis, we have $\text{CARD}(u) = 2$.
- So $u$ consists of two distinct points, call them $x$ and $y$.
- Both $x$ and $y$ are in $s$ (since $t \subseteq s$).
- Let $a = n \times (y - x)$ and $b = a \cdot x$.

We know that $n \cdot (y - x) = 0$ since both $x$ and $y$ lie in the hyperplane $\{z | n \cdot z = d\}$. Using the property of cross products, since $n \neq 0$ and $n \perp (y-x)$, we have $a = n \times (y-x) \neq 0$.

Also, $a \cdot y = b$ (can be verified by vector algebra).

By the theory of exposed faces of polyhedra, since $f$ is a face of $\text{convex hull}(s)$, there exist vectors $a'$ and scalar $b'$ such that:
- $f = \text{convex hull}(s) \cap \{z | a' \cdot z = b'\}$
- Either $\forall w \in \text{convex hull}(s), a' \cdot w \leq b'$ or $\forall w \in \text{convex hull}(s), a' \cdot w \geq b'$

Through a series of calculations, we can show that $a' = \lambda a$ for some scalar $\lambda$, and:
- Either $\forall w \in s, a \cdot w \leq b$ or $\forall w \in s, a \cdot w \geq b$
- $f = \text{convex hull}(s \cap \{z | a \cdot z = b\})$

**Second direction: $\Leftarrow$**
Assume there exist points $x, y \in s$ such that with $a = n \times (y-x)$ and $b = a \cdot x$:
- $a \neq 0$
- Either $\forall w \in s, a \cdot w \leq b$ or $\forall w \in s, a \cdot w \geq b$
- $f = \text{convex hull}(s \cap \{z | a \cdot z = b\})$

First, we prove that $f$ is a face of $\text{convex hull}(s)$ by establishing:
- $\text{convex hull}(s \cap \{z | a \cdot z = b\}) = \text{convex hull}(s) \cap \{z | a \cdot z = b\}$
- If $\forall w \in s, a \cdot w \leq b$, then the hyperplane $\{z | a \cdot z = b\}$ is a supporting hyperplane of $\text{convex hull}(s)$ from below.
- If $\forall w \in s, a \cdot w \geq b$, then it's a supporting hyperplane from above.
- In either case, $f$ is the intersection of $\text{convex hull}(s)$ with this supporting hyperplane, making it a face.

Then, we show that $\text{aff_dim}(f) = 1$ by:
- Proving $\text{aff_dim}(f) \leq 1$ using the structure of the intersection of hyperplanes
- Proving $\text{aff_dim}(f) \geq 1$ by showing that the dimension is at least that of $\{x,y\}$, which is 1 since $a \neq 0$ implies $x \neq y$.

### Mathematical insight
This theorem provides an explicit characterization of the 1-dimensional faces (edges) of a convex polytope in $\mathbb{R}^3$ when the polytope lies in a hyperplane. The faces are identified by looking at pairs of points $x,y$ in the original set and computing a cross product involving the normal vector of the hyperplane.

The theorem is particularly useful for computational geometry tasks, as it gives an algorithmic way to identify all edges of a convex polytope by examining pairs of points from the generating set. The condition that either $a \cdot w \leq b$ or $a \cdot w \geq b$ for all $w \in s$ ensures that the hyperplane $\{z | a \cdot z = b\}$ is a supporting hyperplane of the convex hull.

This result is part of a more general theory of faces of convex polytopes, where faces of different dimensions have different characterizations. The 1-dimensional faces (edges) are particularly important as they form the skeleton of the polytope.

### Dependencies
- Theorems:
  - `CROSS_0`: Cross product with zero vector is zero
  - `NORM_AND_CROSS_EQ_0`: Characterizes when two vectors have zero cross product
  - `FACE_OF_CONVEX_HULL_SUBSET`: Relates faces of convex hull to subsets
  - `AFFINE_BASIS_EXISTS`: Ensures existence of affine bases
  - `EXPOSED_FACE_OF_POLYHEDRON`: Characterizes exposed faces of polyhedra
  - `CONVEX_HULL_UNION_NONEMPTY_EXPLICIT`: Describes convex hull of union
  - `FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE/GE`: Characterizes faces using supporting hyperplanes

- Definitions:
  - `cross`: The cross product operation in $\mathbb{R}^3$
  - `face_of`: The face-of relation for convex sets
  - `aff_dim`: Affine dimension

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-defined theory of convex polytopes, including notions of faces and affine dimension.
2. The proof relies heavily on properties of the cross product in 3D space, so ensure these properties are available.
3. The theorem uses supporting hyperplanes to characterize faces, which is a standard approach in convex geometry.
4. Attention should be paid to the handling of sets defined by equalities or inequalities, as different systems may have different syntax for these.
5. The proof makes use of many specific results about convex hulls and faces which would need to be ported first.

---

## COMPUTE_EDGES_CONV

### COMPUTE_EDGES_CONV

### Type of the formal statement
- theorem (conversion)

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
`COMPUTE_EDGES_CONV` is a conversion function in HOL Light that, when applied to a term representing a coplanar set in 3D space, automatically computes a theorem characterizing all the edges (1-dimensional faces) of the convex hull of that set.

Given a term describing points that lie in a plane (with normal vector $n$ and constant $d$), this conversion produces a theorem that explicitly identifies all edges of the convex hull in terms of the cross products of pairs of points.

### Informal proof
The conversion works through the following steps:

- It first applies `COMPUTE_FACES_1` theorem to the input term after establishing that the points are coplanar using `COPLANAR_HYPERPLANE_RULE`.

- The resulting theorem characterizes edges (1-dimensional faces) of the convex hull in terms of points $x$ and $y$ in the set, where the vector $a = n \times (y - x)$ is non-zero, and where either all points $w$ in the set satisfy $a \cdot w \leq b$ or all satisfy $a \cdot w \geq b$, where $b = a \cdot x$.

- It then performs a series of simplification steps:
  * Simplifies finite set conditions
  * Converts vector operations (subtraction, cross product) to explicit formulas
  * Evaluates dot products of 3D vectors
  * Simplifies real number inequalities
  * Handles set-theoretic operations efficiently

- The conversion automates what would otherwise be a tedious manual calculation, making explicit the geometric conditions that define the edges.

### Mathematical insight
This conversion is essential for computational geometry in 3D space, particularly for analyzing polyhedral objects. The key insight is that edges of a convex hull can be identified by examining pairs of points and determining supporting hyperplanes that contain exactly those two points from the original set.

The conversion leverages the fact that for a coplanar set of points, the edges of its convex hull are precisely where supporting hyperplanes intersect the plane containing the points. These supporting hyperplanes are characterized by vectors perpendicular to both the normal of the plane and the direction of the potential edge.

This automated conversion is particularly valuable for analyzing platonic solids and other polyhedra, as it eliminates the need for manual geometric calculations when identifying edges.

### Dependencies
- **Theorems:**
  * `COMPUTE_FACES_1`: Characterizes 1-dimensional faces of convex hulls
  * `REAL_RAT5_LE_CONV`: Conversion for inequalities involving real numbers with $\sqrt{5}$
  * `VECTOR3_SUB_CONV`: Conversion for vector subtraction in 3D space
  * `VECTOR3_CROSS_CONV`: Conversion for cross products of 3D vectors
  * `VECTOR3_EQ_0_CONV`: Conversion for testing if a 3D vector equals zero
  * `VECTOR3_DOT_CONV`: Conversion for dot products of 3D vectors

### Porting notes
When porting this to another proof assistant:

1. Ensure the target system has good support for 3D vector operations, particularly cross products and dot products.

2. The conversion makes heavy use of HOL Light's conversion combinators like `LAND_CONV`, `RAND_CONV`, and `ONCE_DEPTH_CONV`. The target system should have similar tactical infrastructure or pattern-matching capabilities.

3. Special attention should be paid to the handling of real numbers with $\sqrt{5}$, as this may require specific algebraic support in the target system.

4. The conversion relies on efficient set operations, so the target system should have good library support for set theory.

---

## CARD_EQ_LEMMA

### Name of formal statement
CARD_EQ_LEMMA

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
For all elements $x$, sets $s$, and natural numbers $n$, if:
- $0 < n$
- $x \not\in s$
- $s$ has size $(n - 1)$

then $(x \text{ INSERT } s)$, the set obtained by inserting element $x$ into set $s$, has size $n$.

### Informal proof
The proof begins by rewriting the `HAS_SIZE` notation to use its definition (which relates to finite sets and their cardinality).

After applying basic logical manipulations to extract the assumptions, we need to show that the set obtained by inserting $x$ into $s$ has cardinality $n$.

The key step involves:
- Using the `CARD_CLAUSES` theorem, which tells us that for a finite set $s$ and an element $x \not\in s$, we have $\text{CARD}(x \text{ INSERT } s) = \text{CARD}(s) + 1$
- Using the `FINITE_INSERT` theorem to establish that inserting an element into a finite set preserves finiteness

Finally, we apply arithmetic reasoning to conclude that since $\text{CARD}(s) = n-1$, we have $\text{CARD}(x \text{ INSERT } s) = \text{CARD}(s) + 1 = (n-1) + 1 = n$.

### Mathematical insight
This lemma establishes a fundamental property about cardinality: adding a new element to a set increases its size by exactly one. This is often used when constructing sets incrementally and tracking their sizes.

The lemma is particularly useful for inductive arguments about set sizes and, as the comment indicates, can be applied to analyze properties of Platonic solids - specifically for counting edges per face.

### Dependencies
- `HAS_SIZE`: Definition relating to a set having a specific cardinality
- `CARD_CLAUSES`: Theorem about how the cardinality changes when elements are added to sets
- `FINITE_INSERT`: Theorem establishing that inserting an element to a finite set preserves finiteness

### Porting notes
When porting to other systems:
- Ensure that the target system has appropriate libraries for finite sets and cardinality
- Most proof assistants have built-in notions of finite sets and cardinality, though the names and exact formulations may differ
- The arithmetic reasoning used at the end (`ASM_ARITH_TAC`) is straightforward and should be easily reproducible in other systems

---

## EDGES_PER_FACE_TAC

### Name of formal statement
EDGES_PER_FACE_TAC

### Type of the formal statement
tactic

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
The `EDGES_PER_FACE_TAC` is a tactic that establishes the number of edges per face in a polyhedron. It works by:
1. Using a theorem `th` that identifies the specific face `f` in $\mathbb{R}^3$
2. Counting the edges by computing `CARD {e:real^3->bool | e face_of f /\ aff_dim(e) = &1}`
3. Relating this to the specific geometry of the face

Specifically, this tactic proves that the number of edges in a face equals the cardinality of the set of all 1-dimensional faces of that face.

### Informal proof
The tactic implements the following proof strategy:

- Start with standard simplification and stripping of hypotheses
- Use transitivity of equality to restate the goal in terms of the cardinality of the set of 1-dimensional faces of `f`
- The first subgoal shows set equality by extension, using properties of the face-of relation (transitivity and subset properties)
- For the second subgoal:
  - Apply the theorem `th` which identifies the specific face `f`
  - For each possible case of face, compute the edges using `COMPUTE_EDGES_CONV`
  - Express the result in terms of segments (convex hulls of pairs of points)
  - Verify the cardinality of the resulting set by showing it has the expected size
  - For each edge:
    - Apply `CARD_EQ_LEMMA` which helps establish the cardinality incrementally
    - Verify that edges are distinct by showing that their endpoints don't coincide
    - Use vector operations (via `VECTOR3_SUB_CONV` and `VECTOR3_EQ_0_CONV`) to establish this distinctness
  - Complete the proof with numerical computation and basic set reasoning

### Mathematical insight
This tactic plays an important role in verifying combinatorial properties of polyhedra, specifically Platonic solids. It counts edges per face by exploiting the relation between algebraic and geometric properties of faces. The tactic handles the tedious case analysis needed to verify that faces have the expected number of edges.

The key insight is that edges can be characterized as 1-dimensional faces of a face, and by carefully computing these for specific polyhedra, we can verify their combinatorial structure. This is part of a broader approach to formalizing the classification of Platonic solids, where counting the number of edges per face is a critical step.

### Dependencies
- **Theorems**:
  - `CARD_EQ_LEMMA`: Theorem about size of sets with insertions
  - `VECTOR3_SUB_CONV`: Conversion for vector subtraction in 3D
  - `VECTOR3_EQ_0_CONV`: Conversion for testing if a 3D vector equals zero
  - `COMPUTE_EDGES_CONV`: Conversion for computing edges of a face

### Porting notes
When porting this tactic to another proof assistant:
- You'll need equivalent functionality for vector operations in 3D space
- The tactic relies heavily on conversions that compute explicit geometric facts
- The implementation will depend on how set operations and cardinality are handled in the target system
- Be aware that the tactic takes a theorem as an argument and uses it for case analysis, which may require different structuring in other systems

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
For any face $f$ of the standard tetrahedron such that the affine dimension of $f$ is 2, the number of edges that are contained in $f$ is 3. Specifically:

$$\forall f. \text{$f$ face\_of std\_tetrahedron} \land \text{aff\_dim}(f) = 2 \implies |\{e \mid \text{$e$ face\_of std\_tetrahedron} \land \text{aff\_dim}(e) = 1 \land e \subseteq f\}| = 3$$

Here, $\text{std\_tetrahedron}$ is the standard tetrahedron in $\mathbb{R}^3$ defined as the convex hull of the four points $(1,1,1)$, $(-1,-1,1)$, $(-1,1,-1)$, and $(1,-1,-1)$.

### Informal proof
The proof uses the `EDGES_PER_FACE_TAC` tactic applied to the theorem `TETRAHEDRON_FACETS`, which characterizes all the 2-dimensional faces of the standard tetrahedron.

According to `TETRAHEDRON_FACETS`, the standard tetrahedron has exactly four triangular faces, each being the convex hull of three of the four vertices. For each of these triangular faces, we need to count the number of 1-dimensional faces (edges) contained in it.

Since each face is a triangle, it has exactly 3 edges. This is a basic property of triangles: each triangle has 3 edges corresponding to the 3 pairs of vertices. Each edge of the tetrahedron is a 1-dimensional face formed by the convex hull of two vertices.

Therefore, for any 2-dimensional face $f$ of the standard tetrahedron, there are exactly 3 edges contained in $f$.

### Mathematical insight
This theorem verifies a fundamental property of tetrahedra, namely that each face is a triangle and therefore contains exactly 3 edges. This is part of the broader study of polyhedra and their combinatorial properties.

In the context of Euler's formula for polyhedra ($V - E + F = 2$ where $V$, $E$, and $F$ are the numbers of vertices, edges, and faces), this theorem helps establish the structure of the tetrahedron, which has 4 vertices, 6 edges, and 4 faces.

The result is canonical in the study of platonic solids, with the tetrahedron being one of the five regular polyhedra.

### Dependencies
- **Theorems**:
  - `TETRAHEDRON_FACETS`: Characterizes all 2-dimensional faces of the standard tetrahedron
- **Definitions**:
  - `std_tetrahedron`: Defines the standard tetrahedron in $\mathbb{R}^3$ as the convex hull of four specific points

### Porting notes
When porting this theorem:
1. Ensure your system has a representation of convex polytopes, especially the standard tetrahedron
2. Make sure the face relation and affine dimension are well-defined
3. The tactic `EDGES_PER_FACE_TAC` suggests a specialized approach; in other systems, you may need to explicitly count the edges for each face based on their vertex descriptions

---

## CUBE_EDGES_PER_FACE

### CUBE_EDGES_PER_FACE
- `CUBE_EDGES_PER_FACE`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CUBE_EDGES_PER_FACE = prove
 (`!f. f face_of std_cube /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_cube /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 4`,
  EDGES_PER_FACE_TAC CUBE_FACETS);;
```

### Informal statement
The theorem states that for any 2-dimensional face $f$ of the standard cube in $\mathbb{R}^3$, the number of 1-dimensional faces (edges) of the standard cube that are subsets of $f$ is exactly 4.

Formally, for all $f$ such that $f$ is a face of the standard cube and the affine dimension of $f$ is 2, the cardinality of the set $\{e \mid e \text{ face\_of } \text{std\_cube} \land \text{aff\_dim}(e) = 1 \land e \subseteq f\}$ equals 4.

### Informal proof
The proof uses the tactic `EDGES_PER_FACE_TAC` applied to the theorem `CUBE_FACETS`. 

The theorem `CUBE_FACETS` explicitly characterizes all the 2-dimensional faces of the standard cube, showing that there are exactly 6 faces, each being the convex hull of 4 vertices.

The tactic `EDGES_PER_FACE_TAC` likely:
1. Takes each 2-dimensional face characterized in `CUBE_FACETS`
2. Identifies all 1-dimensional faces (edges) of the standard cube that are contained in that 2-dimensional face
3. Counts these edges, verifying that there are exactly 4 for each 2-dimensional face

Since each 2-dimensional face of the standard cube is a square, it has exactly 4 edges, which is what the theorem states.

### Mathematical insight
This theorem formally establishes a basic combinatorial property of the standard cube in $\mathbb{R}^3$: each 2-dimensional face (which is a square) contains exactly 4 edges of the cube.

This result is part of a broader study of the combinatorial structure of polyhedra, particularly the standard cube. It verifies an intuitive geometric fact in a formal setting, which is useful for further analysis of polytopes and their facial structures.

The standard cube has 6 faces (squares), 12 edges, and 8 vertices. This theorem confirms that each face contains exactly 4 of those 12 edges, which aligns with our geometric intuition about cubes.

### Dependencies
- **Theorems**: 
  - `CUBE_FACETS`: Characterizes all 2-dimensional faces of the standard cube
- **Definitions**:
  - `std_cube`: The standard cube in $\mathbb{R}^3$

### Porting notes
When porting this theorem:
- Ensure that the target system has a well-defined notion of faces of a polyhedron and affine dimension
- The proof may require a different approach depending on the automation available in the target system
- The notion of "face_of" relation might need explicit definition in systems where it's not predefined
- The standard cube definition might need to be adjusted based on the coordinate system conventions of the target system

---

## OCTAHEDRON_EDGES_PER_FACE

### OCTAHEDRON_EDGES_PER_FACE
- `OCTAHEDRON_EDGES_PER_FACE`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let OCTAHEDRON_EDGES_PER_FACE = prove
 (`!f. f face_of std_octahedron /\ aff_dim(f) = &2
       ==> CARD {e | e face_of std_octahedron /\ aff_dim(e) = &1 /\
                     e SUBSET f} = 3`,
  EDGES_PER_FACE_TAC OCTAHEDRON_FACETS);;
```

### Informal statement
For any face $f$ of the standard octahedron in $\mathbb{R}^3$ such that the affine dimension of $f$ is 2, the number of edges of the octahedron contained in $f$ is exactly 3.

More precisely, for any set $f \subset \mathbb{R}^3$ such that $f$ is a face of the standard octahedron and $\text{aff\_dim}(f) = 2$, the cardinality of the set
$$\{e \mid e \text{ face\_of } \text{std\_octahedron} \land \text{aff\_dim}(e) = 1 \land e \subset f\}$$
is equal to 3.

### Informal proof
The proof is accomplished by applying a general tactic `EDGES_PER_FACE_TAC` to the theorem `OCTAHEDRON_FACETS`.

The theorem `OCTAHEDRON_FACETS` characterizes all 2-dimensional faces of the standard octahedron as the convex hulls of certain triplets of vectors. Each face is a triangle formed by three vertices of the octahedron.

The tactic `EDGES_PER_FACE_TAC` then automatically verifies that each 2-dimensional face contains exactly 3 edges. This is intuitively clear because each face is a triangle, and a triangle has exactly 3 edges.

### Mathematical insight
This theorem establishes a fundamental combinatorial property of the octahedron - that each face contains exactly 3 edges. This is a direct consequence of the fact that each face of an octahedron is a triangle.

The standard octahedron in $\mathbb{R}^3$ is defined as the convex hull of the six points: $(\pm 1, 0, 0)$, $(0, \pm 1, 0)$, and $(0, 0, \pm 1)$. It has 8 triangular faces, 12 edges, and 6 vertices.

This property is part of the more general Euler characteristic formula for polyhedra, which states that $V - E + F = 2$ where $V$ is the number of vertices, $E$ is the number of edges, and $F$ is the number of faces. For the octahedron, we have $6 - 12 + 8 = 2$.

### Dependencies
- **Theorems:**
  - `OCTAHEDRON_FACETS`: Characterizes all 2-dimensional faces of the standard octahedron as convex hulls of specific triplets of vectors.

- **Definitions:**
  - `std_octahedron`: The standard octahedron in $\mathbb{R}^3$, defined as the convex hull of the six points $(\pm 1, 0, 0)$, $(0, \pm 1, 0)$, and $(0, 0, \pm 1)$.

### Porting notes
When porting this theorem, one should:
1. Ensure the standard octahedron is defined the same way in the target system
2. Verify that face and affine dimension concepts are compatible
3. Implement or adapt the `EDGES_PER_FACE_TAC` tactic for the target system, or develop an alternative proof strategy that counts edges per face

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
For any face $f$ of the standard dodecahedron, if the affine dimension of $f$ is 2, then the number of edges of the standard dodecahedron that are contained in $f$ is 5.

More formally, for all $f$:
$f \text{ face\_of } \text{std\_dodecahedron} \land \text{aff\_dim}(f) = 2 \Rightarrow |\{e \mid e \text{ face\_of } \text{std\_dodecahedron} \land \text{aff\_dim}(e) = 1 \land e \subseteq f\}| = 5$

### Informal proof
The proof uses the tactic `EDGES_PER_FACE_TAC` applied to the theorem `DODECAHEDRON_FACETS`. This tactic likely:

1. Takes the explicit description of all dodecahedron faces from the `DODECAHEDRON_FACETS` theorem
2. For each face described in that theorem, computes the edges that are subsets of that face
3. Verifies that for each face, there are exactly 5 edges that are contained within it

This proof reflects the well-known geometric fact that each face of a dodecahedron is a regular pentagon, which has exactly 5 edges.

### Mathematical insight
This theorem formally establishes a fundamental property of the dodecahedron: each face is bounded by exactly 5 edges. This is a key characteristic that distinguishes the dodecahedron from other Platonic solids. 

The dodecahedron has 12 pentagonal faces, and this theorem confirms that each of these faces contains exactly 5 edges of the polyhedron. Combined with other properties such as its vertex count (20) and total edge count (30), this helps establish the complete combinatorial structure of the dodecahedron.

This property is part of the general Euler characteristic formula for polyhedra: $V - E + F = 2$, where $V$ is the number of vertices, $E$ is the number of edges, and $F$ is the number of faces. For the dodecahedron, we have $20 - 30 + 12 = 2$.

### Dependencies
- Theorems:
  - `DODECAHEDRON_FACETS`: Provides the explicit description of all 12 faces of the standard dodecahedron
- Definitions:
  - `std_dodecahedron`: The standard dodecahedron in 3D space
- Tactics:
  - `EDGES_PER_FACE_TAC`: A specialized tactic that computes and verifies the number of edges per face

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that the dodecahedron is defined using the same coordinates
2. The face and edge relationships might need to be explicitly computed rather than using specialized tactics
3. Depending on how polyhedra are represented in the target system, you may need to define what it means for an edge to be "contained in" a face
4. You may need to prove that each face is a pentagon separately, then use this to establish the edge count

---

## ICOSAHEDRON_EDGES_PER_FACE

### ICOSAHEDRON_EDGES_PER_FACE

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
For any face $f$ of the standard icosahedron such that the affine dimension of $f$ is 2, the cardinality of the set of edges $e$ of the standard icosahedron (where an edge is defined as a face with affine dimension 1) that are subsets of $f$ is exactly 3.

More formally: For all $f$, if $f$ is a face of the standard icosahedron and the affine dimension of $f$ is 2, then:
$$\text{CARD}\{e \mid e \text{ face_of std_icosahedron} \land \text{aff_dim}(e) = 1 \land e \subseteq f\} = 3$$

### Informal proof
The theorem is proven by applying a general tactic called `EDGES_PER_FACE_TAC` to the theorem `ICOSAHEDRON_FACETS`. 

The `ICOSAHEDRON_FACETS` theorem provides an explicit enumeration of all 2-dimensional faces of the standard icosahedron, showing that each face is the convex hull of exactly three vertices.

Since each face of the icosahedron is a triangle (convex hull of three points), it has exactly three edges, which are the line segments connecting pairs of vertices. The tactic `EDGES_PER_FACE_TAC` verifies this by:

1. Using the characterization of faces provided by `ICOSAHEDRON_FACETS`
2. Extracting the faces with affine dimension 1 (edges) that are subsets of each 2-dimensional face
3. Computing the cardinality of this set for each face
4. Proving this cardinality is always 3

### Mathematical insight
This theorem establishes a fundamental combinatorial property of the icosahedron: each of its faces is bounded by exactly three edges. This confirms that all faces of the icosahedron are triangles.

The icosahedron is one of the five Platonic solids, having 20 faces (all equilateral triangles), 30 edges, and 12 vertices. This theorem helps establish part of this combinatorial structure by confirming that each face has exactly 3 edges.

This result is part of a larger collection of theorems that formally characterize the geometry and combinatorics of the Platonic solids in a theorem prover. Such formalization is important for verification of geometric results and can be used in applications ranging from computational geometry to crystallography.

### Dependencies
- Theorems:
  - `ICOSAHEDRON_FACETS`: Provides the explicit characterization of all 2-dimensional faces of the standard icosahedron
- Definitions:
  - `std_icosahedron`: Defines the standard icosahedron as the convex hull of its vertices in 3D space
- Tactics:
  - `EDGES_PER_FACE_TAC`: A specialized tactic used to count the edges per face of a polyhedron

### Porting notes
When porting this theorem to another proof assistant:
1. You'll need to first formalize the definition of the standard icosahedron and its faces
2. Establish the equivalent of `ICOSAHEDRON_FACETS` which enumerates all faces
3. Implement a way to count the number of edges per face
4. The proof approach will likely need to be adapted based on the available automation in the target system
5. In systems with less automation for convex geometry, more explicit reasoning about the structure of faces may be required

---

## POLYTOPE_3D_LEMMA

### POLYTOPE_3D_LEMMA
- `POLYTOPE_3D_LEMMA`

### Type of the formal statement
- theorem

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
The theorem states that for vectors $x, y, z, w$ in $\mathbb{R}^3$ and a set $s \subset \mathbb{R}^3$:

If we define $a = (z - x) \times (y - x)$ (where $\times$ denotes the cross product), and
- $a \neq 0$ (i.e., the cross product is non-zero)
- There exists a vector $w \in s$ such that $a \cdot w \neq a \cdot x$ (where $\cdot$ denotes the dot product)

Then the affine dimension of the convex hull of the set $\{x, y, z\} \cup s$ is 3.

### Informal proof
The proof proceeds by showing that the affine dimension equals 3:

1. First, we show that the affine dimension is at most 3:
   - This follows immediately from the fact that we're working in $\mathbb{R}^3$ and the affine dimension of any subset of $\mathbb{R}^3$ is at most 3.

2. Next, we show the affine dimension is at least 3:
   - We use transitivity of the integer inequality relation to compare with the affine dimension of $\{w, x, y, z\}$.
   - We analyze the affine dimension after inserting $w$ into the set $\{x, y, z\}$.

3. We consider two cases:
   - Case 1: $w$ is in the affine hull of $\{x, y, z\}$.
     - This leads to a contradiction because we know $w$ satisfies $a \cdot w \neq a \cdot x$.
     - The affine hull of $\{x, y, z\}$ is contained in the hyperplane defined by $a \cdot p = a \cdot x$ (where $a$ is the cross product $(z - x) \times (y - x)$).

   - Case 2: $w$ is not in the affine hull of $\{x, y, z\}$.
     - We show that the set $\{w, x, y, z\}$ is affinely independent.
     - This is equivalent to showing that $\{x, y, z\}$ is not collinear, which follows from our assumption that $a = (z - x) \times (y - x) \neq 0$.
     - Since $\{w, x, y, z\}$ has 4 affinely independent points in $\mathbb{R}^3$, its affine dimension is 3.

4. Therefore, the affine dimension of the convex hull of $\{x, y, z\} \cup s$ must be 3.

### Mathematical insight
This lemma is establishing a sufficient condition for a polytope in 3D to be full-dimensional (i.e., to have affine dimension 3). The key insight is:

1. The cross product $(z - x) \times (y - x) \neq 0$ ensures that the points $x$, $y$, and $z$ are not collinear (they form a proper triangle in 3D space).

2. The condition that there exists $w \in s$ with $a \cdot w \neq a \cdot x$ ensures that $w$ is not contained in the plane defined by $x$, $y$, and $z$.

3. Together, these conditions guarantee that we have 4 affinely independent points, which is sufficient to span the entire 3D space.

This result is particularly useful when dealing with Platonic solids or other polyhedra in 3D space, as it provides a clear criterion for determining when such objects are truly three-dimensional.

### Dependencies
- **Theorems**:
  - `CROSS_EQ_0`: The cross product of two vectors is zero if and only if the vectors are collinear with the zero vector.

- **Definitions**:
  - `cross`: The cross product of two 3D vectors.

### Porting notes
When porting to other proof assistants:
1. Ensure that the cross product and dot product operations are properly defined for 3D vectors.
2. The affine dimension concept may be defined differently in other systems - check its definition and properties.
3. The proof makes use of specialized tactics like `VEC3_TAC` for 3D vector reasoning, which may need alternative approaches in other systems.
4. The convex hull operation and its properties regarding affine dimension will be important to have available.

---

## POLYTOPE_FULLDIM_TAC

### Name of formal statement
POLYTOPE_FULLDIM_TAC

### Type of the formal statement
Tactic/Conversion

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
`POLYTOPE_FULLDIM_TAC` is a tactic in HOL Light used to prove that a polytope in 3D space has full dimension (affine dimension 3). It applies the theorem `POLYTOPE_3D_LEMMA` and performs a series of conversion-based simplifications on vector operations in 3D space.

### Informal proof
The tactic implements a proof strategy with the following steps:

1. Apply the theorem `POLYTOPE_3D_LEMMA` which states that if we have vectors $x$, $y$, $z$ and a set $s$ in $\mathbb{R}^3$ such that:
   - The cross product $a = (z - x) \times (y - x)$ is non-zero
   - There exists a point $w \in s$ such that $a \cdot w \neq a \cdot x$
   
   Then the affine dimension of the convex hull of $\{x, y, z\} \cup s$ is 3.

2. Simplify vector subtraction using `VECTOR3_SUB_CONV` to convert expressions of the form:
   $\text{vector}[x_1, x_2, x_3] - \text{vector}[y_1, y_2, y_3] = \text{vector}[x_1-y_1, x_2-y_2, x_3-y_3]$

3. Simplify vector cross products using `VECTOR3_CROSS_CONV` to compute:
   $\text{vector}[x_1, x_2, x_3] \times \text{vector}[y_1, y_2, y_3] = \text{vector}[x_2y_3-x_3y_2, x_3y_1-x_1y_3, x_1y_2-x_2y_1]$

4. Eliminate let-bindings with `let_CONV`

5. Split the proof into two parts with `CONJ_TAC`:
   - First part: Prove $a \neq 0$ by converting the vector equality to component-wise equalities
   - Second part: Prove $\exists w \in s. a \cdot w \neq a \cdot x$ by computing dot products and rational equality tests

### Mathematical insight
This tactic implements a common approach for proving that a polytope has full dimension in 3D space. The key insight is that a polytope has affine dimension 3 if and only if it's not contained in any plane. The mathematical condition:
- The cross product $(z-x) \times (y-x)$ is non-zero (meaning $x$, $y$, and $z$ are not collinear)
- There exists a point $w$ not in the same plane as $x$, $y$, and $z$ 

Captures exactly what's needed for full dimensionality. The tactic automates this proof pattern using specific 3D vector operations and conversions to reduce the generic mathematical statement to concrete calculations with vector components.

### Dependencies
- **Theorems:**
  - `POLYTOPE_3D_LEMMA`: The key theorem establishing that a 3D polytope has full dimension under specific conditions
  - `VECTOR3_SUB_CONV`: Conversion for vector subtraction in 3D
  - `VECTOR3_CROSS_CONV`: Conversion for cross product in 3D
  - `VECTOR3_EQ_0_CONV`: Tests if a 3D vector equals the zero vector
  - `VECTOR3_DOT_CONV`: Conversion for dot product in 3D

### Porting notes
When porting this tactic to another system:
1. Ensure the target system has good support for 3D vector operations
2. The tactic relies heavily on conversions (computations at the term level) which might need to be implemented differently in other systems
3. In systems with stronger automation, this might be handled by a more general dimensionality-checking algorithm
4. Note that rational arithmetic conversions (`REAL_RAT5_EQ_CONV`, etc.) are used implicitly - the target system should have similar capabilities

---

## STD_TETRAHEDRON_FULLDIM

### STD_TETRAHEDRON_FULLDIM

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

Mathematically: $\text{aff\_dim}(\text{std\_tetrahedron}) = 3$

### Informal proof
The proof proceeds in two steps:
- First, we expand the definition of `std_tetrahedron`, which is defined as the convex hull of four points in $\mathbb{R}^3$: $(1,1,1)$, $(-1,-1,1)$, $(-1,1,-1)$, and $(1,-1,-1)$.
- Then, the theorem is proven using the tactic `POLYTOPE_FULLDIM_TAC`, which is designed to automatically prove that a polytope has full dimension when it is defined as the convex hull of a set of points in general position.

The four vertices of the standard tetrahedron are indeed in general position in $\mathbb{R}^3$, meaning they are not all contained in any plane. This ensures that the tetrahedron has the maximum possible affine dimension of 3 in $\mathbb{R}^3$.

### Mathematical insight
This theorem establishes that the standard tetrahedron, one of the Platonic solids, is a full-dimensional object in 3D space. This is expected since the tetrahedron is a proper 3D object, but formally establishing the affine dimension is important for subsequent geometric reasoning.

The affine dimension of a set is the dimension of the smallest affine subspace containing that set. For a tetrahedron in $\mathbb{R}^3$, having affine dimension 3 confirms that it is a "solid" object rather than being degenerate (like a flat triangle).

This result is part of a broader formalization of geometric objects and their properties, and it serves as a foundational fact for more complex geometric theorems about the standard tetrahedron.

### Dependencies
#### Definitions
- `std_tetrahedron`: The standard tetrahedron defined as the convex hull of four specific points in $\mathbb{R}^3$.

#### Tactics
- `POLYTOPE_FULLDIM_TAC`: A specialized tactic for proving that a polytope has full dimension.

### Porting notes
When porting this theorem to other systems:
- Ensure that the definition of the standard tetrahedron uses the same four vertices in $\mathbb{R}^3$.
- The automatic `POLYTOPE_FULLDIM_TAC` may not be available in other systems, so you might need to explicitly prove that the four points are affinely independent, which would establish that their convex hull has affine dimension 3.
- In some systems, you may need to explicitly state that these points are in $\mathbb{R}^3$ rather than relying on implicit typing.

---

## STD_CUBE_FULLDIM

### STD_CUBE_FULLDIM

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let STD_CUBE_FULLDIM = prove
 (`aff_dim std_cube = &3`,
  REWRITE_TAC[std_cube] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
This theorem states that the affine dimension of the standard cube in $\mathbb{R}^3$ is 3.

In mathematical notation:
$$\text{aff\_dim}(\text{std\_cube}) = 3$$

where $\text{std\_cube}$ is the standard cube in $\mathbb{R}^3$ defined as the convex hull of the eight vertices with coordinates $(\pm 1, \pm 1, \pm 1)$.

### Informal proof
The proof is straightforward:

1. We first rewrite the statement using the definition of `std_cube`, which replaces `std_cube` with its definition as the convex hull of the eight vertices with coordinates $(\pm 1, \pm 1, \pm 1)$ in $\mathbb{R}^3$.

2. Then we apply the tactic `POLYTOPE_FULLDIM_TAC`, which is designed to prove that a polytope has full dimension in its ambient space. This tactic automatically shows that the affine dimension of the standard cube equals 3.

The tactic likely works by verifying that there are enough affinely independent points in the definition of the standard cube to span the full 3-dimensional space.

### Mathematical insight
This theorem establishes the basic and expected fact that the standard cube in $\mathbb{R}^3$ is truly three-dimensional. It occupies the full dimension of the ambient space, which is a fundamental property that confirms our geometric intuition.

This result is important because:
1. It verifies that the formal definition of the standard cube properly captures the intended geometric object
2. It serves as a foundation for more complex results about the standard cube
3. It confirms that the cube is not degenerate (i.e., not constrained to a lower-dimensional subspace)

### Dependencies
- **Definitions**:
  - `std_cube`: The standard cube in $\mathbb{R}^3$ defined as the convex hull of the eight vertices with coordinates $(\pm 1, \pm 1, \pm 1)$

- **Tactics**:
  - `POLYTOPE_FULLDIM_TAC`: A specialized tactic for proving that polytopes have full dimension

### Porting notes
When porting this theorem:
- Ensure that the definition of the standard cube matches exactly, with the coordinates $(\pm 1, \pm 1, \pm 1)$ for all eight vertices
- You may need to implement your own version of the `POLYTOPE_FULLDIM_TAC` tactic, which likely proves that a polytope has full dimension by finding a suitable set of affinely independent points
- Alternatively, you could prove this directly by showing that there are 4 affinely independent points among the vertices of the cube

---

## STD_OCTAHEDRON_FULLDIM

### STD_OCTAHEDRON_FULLDIM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let STD_OCTAHEDRON_FULLDIM = prove
 (`aff_dim std_octahedron = &3`,
  REWRITE_TAC[std_octahedron] THEN POLYTOPE_FULLDIM_TAC);;
```

### Informal statement
The affine dimension of the standard octahedron is 3.

Mathematically, this states:
$$\text{aff\_dim}(\text{std\_octahedron}) = 3$$

where $\text{std\_octahedron}$ is defined as the convex hull of the six points $\{(1,0,0), (-1,0,0), (0,0,1), (0,0,-1), (0,1,0), (0,-1,0)\}$ in $\mathbb{R}^3$.

### Informal proof
The proof proceeds in two steps:
1. First, we rewrite the statement using the definition of `std_octahedron`, which expresses it as the convex hull of the six vectors described above.
2. Then, we apply a tactic called `POLYTOPE_FULLDIM_TAC`, which is designed to prove that certain polytopes have full dimension in their ambient space.

This tactic likely works by showing that the set of vertices of the octahedron spans the full 3-dimensional space. Since the standard octahedron has vertices on all three coordinate axes in both positive and negative directions, it clearly has affine dimension 3.

### Mathematical insight
The affine dimension of a set is the dimension of the smallest affine subspace containing it. This theorem confirms that the standard octahedron is a full-dimensional object in 3D space, which is expected since its vertices include points that span all three coordinate directions.

The standard octahedron is one of the five Platonic solids, and understanding its dimensional properties is fundamental in geometric analysis. This result is a basic but important property establishing that the octahedron properly "fills" 3D space rather than being confined to a lower-dimensional subspace.

### Dependencies
#### Definitions
- `std_octahedron`: Defines the standard octahedron as the convex hull of the six points $\{(1,0,0), (-1,0,0), (0,0,1), (0,0,-1), (0,1,0), (0,-1,0)\}$ in $\mathbb{R}^3$.

#### Tactics
- `POLYTOPE_FULLDIM_TAC`: A specialized tactic for proving that polytopes have full dimension.

### Porting notes
When porting this theorem:
1. First ensure the definition of the standard octahedron is established.
2. In most proof assistants, you'll need to explicitly prove that the vertices span the full space, as the specialized `POLYTOPE_FULLDIM_TAC` might not be available.
3. This may involve showing that there exist 4 affinely independent points among the vertices of the octahedron.
4. Alternatively, you could show that the difference vectors between vertices span the 3D space.

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
The affine dimension of the standard dodecahedron is 3.

Formally: $\text{aff\_dim}(\text{std\_dodecahedron}) = 3$

### Informal proof
The proof proceeds by rewriting with the definition of the standard dodecahedron and then applying the `POLYTOPE_FULLDIM_TAC` tactic, which automatically proves that a polytope has full dimension in the appropriate space.

In this case, the standard dodecahedron is defined as the convex hull of 20 vertices in $\mathbb{R}^3$, and the tactic shows that these vertices span a 3-dimensional affine space.

### Mathematical insight
This theorem establishes that the standard dodecahedron is truly a 3-dimensional object that fills its ambient space. In geometric terms, it confirms that the dodecahedron is not degenerate (i.e., it doesn't collapse to a lower-dimensional object like a plane or a line).

This result is important for the theory of Platonic solids, as it verifies that the standard dodecahedron has the expected dimensionality. The affine dimension of a geometric object is a fundamental property that characterizes its spatial extent.

### Dependencies
- **Theorems**:
  - `STD_DODECAHEDRON`: Explicit formula for the standard dodecahedron as the convex hull of 20 specific points in $\mathbb{R}^3$

- **Definitions**:
  - `std_dodecahedron`: Definition of the standard dodecahedron using the golden ratio

### Porting notes
When porting this theorem:
1. Ensure that the definition of the standard dodecahedron using the golden ratio is correctly translated
2. The proof relies on a special tactic (`POLYTOPE_FULLDIM_TAC`) that automatically proves dimensionality of polytopes - you'll need to either implement an equivalent tactic or provide an explicit proof that the vertices span a 3-dimensional space
3. You may need to establish that the convex hull of points that affinely span $\mathbb{R}^3$ also has affine dimension 3

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
The affine dimension of the standard icosahedron is $3$.

Formally, $\text{aff\_dim}(\text{std\_icosahedron}) = 3$.

### Informal proof
The proof consists of two steps:
1. First, we rewrite using the definition `STD_ICOSAHEDRON`, which expresses the standard icosahedron as the convex hull of 12 vertices in $\mathbb{R}^3$.
2. Then, we apply the `POLYTOPE_FULLDIM_TAC` tactic, which is designed to prove that a polytope defined as the convex hull of points in $\mathbb{R}^n$ has affine dimension $n$ when the points are in general position.

The standard icosahedron is defined as the convex hull of 12 vertices in $\mathbb{R}^3$:
- Four vertices with first coordinate 0: $\binom{0}{±1}{±\phi}$
- Four vertices with second coordinate 0: $\binom{±\phi}{0}{±1}$
- Four vertices with third coordinate 0: $\binom{±1}{±\phi}{0}$

where $\phi = \frac{1+\sqrt{5}}{2}$ is the golden ratio.

These vertices are in general position that span the full 3-dimensional space, so the affine dimension equals 3.

### Mathematical insight
This theorem establishes that the standard icosahedron, one of the five Platonic solids, is a full-dimensional object in 3D space. The result is expected since the icosahedron is constructed as the convex hull of 12 vertices specifically arranged in 3D space.

The standard icosahedron has a highly symmetric structure, with the vertices positioned on the vertices of three perpendicular golden rectangles. This particular construction guarantees that the points span the full 3-dimensional space.

The theorem is a fundamental property of the icosahedron that confirms it is a proper 3-dimensional polyhedron rather than being embedded in a lower-dimensional affine subspace.

### Dependencies
- Theorems:
  - `STD_ICOSAHEDRON`: Provides the explicit representation of the standard icosahedron as the convex hull of 12 specific points in 3D space.
- Tactics:
  - `POLYTOPE_FULLDIM_TAC`: A specialized tactic for proving that polytopes defined as convex hulls have the expected affine dimension.

### Porting notes
When porting this theorem:
1. Ensure that the definition of the standard icosahedron using the golden ratio is properly translated.
2. The `POLYTOPE_FULLDIM_TAC` is a specialized tactic - in other systems, you might need to explicitly show that the vertices of the icosahedron affinely span $\mathbb{R}^3$, perhaps by showing that there are 4 affinely independent points among the vertices.
3. Depending on the system, you might need to handle the real number arithmetic and the golden ratio expressions carefully.

---

## COMPUTE_EDGES_TAC

### Name of formal statement
COMPUTE_EDGES_TAC

### Type of the formal statement
theorem (tactic definition)

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
This is a HOL Light tactic specifically designed to compute the edges of a Platonic solid. The tactic takes three parameters:
- `defn`: A definition of a polyhedron `p` in $\mathbb{R}^3$
- `fulldim`: A theorem stating that the affine dimension of the polyhedron is 3
- `facets`: A theorem listing the facets (2-dimensional faces) of the polyhedron

The tactic proves that an edge of the polyhedron can be characterized in two equivalent ways:
1. Directly as a 1-dimensional face of the polyhedron
2. Or as a 1-dimensional face of some 2-dimensional face of the polyhedron

### Informal proof
The tactic works by applying a sequence of proof steps:

1. It begins with a goal of the form:
   ```
   ∀e. e face_of p ∧ aff_dim e = 1 ⟺ ∃f. (f face_of p ∧ aff_dim f = 2) ∧ (e face_of f ∧ aff_dim e = 1)
   ```

2. The proof proceeds by:
   - Applying transitivity of equality
   - Setting up an intermediate statement using the polyhedron definition
   - Proving the equivalence in two directions:
     - Forward direction (⇒): Uses the theorem `FACE_OF_POLYHEDRON_SUBSET_FACET` which states that any proper face of a polyhedron is contained in some facet
     - Backward direction (⇐): Uses transitivity of the `face_of` relation
   - Applying `POLYHEDRON_CONVEX_HULL` to establish that the defined object is indeed a polyhedron
   - Using the provided `facets` theorem to explicitly compute the edges by applying `COMPUTE_EDGES_CONV` to each facet

3. The tactic finally performs some set-theoretic simplifications to clean up the resulting expression.

### Mathematical insight
This tactic is crucial for working with Platonic solids in formal geometry. It establishes the important connection between the edges of a polyhedron defined directly (as 1-dimensional faces) and the edges defined indirectly (as 1-dimensional faces of 2-dimensional facets).

The tactic automates what would otherwise be a tedious manual proof. It specifically:
1. Shows that any edge can be viewed as the intersection of two facets
2. Uses computational conversions to actually derive the explicit list of edges from the list of facets
3. Handles the set-theoretic representation of the polyhedron and its faces

This approach is canonical in computational geometry, where edges are often computed from facets rather than directly from the vertices.

### Dependencies
- **Theorems**:
  - `COMPUTE_EDGES_CONV`: A conversion that computes the edges from the facets
  - `FACE_OF_TRANS`: Transitivity of the face_of relation
  - `FACE_OF_POLYHEDRON_SUBSET_FACET`: A theorem stating that any face of a polyhedron is contained in some facet
  - `POLYHEDRON_CONVEX_HULL`: States that the convex hull of a finite set is a polyhedron
  - `FACE_OF_FACE`: If f is a face of g and g is a face of p, then f is a face of p

### Porting notes
When porting this tactic to other systems:
1. The set-theoretic operations (INSERT, INTER) will need to be translated to their equivalents
2. The computational aspects handled by conversions like `COMPUTE_EDGES_CONV` will likely require a different approach depending on the system's computation capabilities
3. The 3D vector operations and affine dimension calculations are system-specific and will need appropriate translations
4. The tactic makes heavy use of HOL Light's conversion mechanism, which might not have direct equivalents in other systems

---

## TETRAHEDRON_EDGES

### TETRAHEDRON_EDGES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
The theorem characterizes the edges of the standard tetrahedron. Specifically, it states that for any set $e$:

$e$ is a face of the standard tetrahedron with affine dimension 1 if and only if $e$ is equal to one of the following convex hulls:
- $\text{conv}\{(-1,-1,1), (-1,1,-1)\}$
- $\text{conv}\{(-1,-1,1), (1,-1,-1)\}$
- $\text{conv}\{(-1,-1,1), (1,1,1)\}$
- $\text{conv}\{(-1,1,-1), (1,-1,-1)\}$
- $\text{conv}\{(-1,1,-1), (1,1,1)\}$
- $\text{conv}\{(1,-1,-1), (1,1,1)\}$

Where each vector is represented in $\mathbb{R}^3$.

### Informal proof
The proof uses a specialized tactic `COMPUTE_EDGES_TAC` which computes all the edges of the standard tetrahedron. The tactic uses two key facts:

1. The standard tetrahedron is full-dimensional in $\mathbb{R}^3$ (from `STD_TETRAHEDRON_FULLDIM`)
2. The characterization of the facets (2-dimensional faces) of the standard tetrahedron (from `TETRAHEDRON_FACETS`)

The edges of a polytope are the 1-dimensional faces, which can be derived from the higher-dimensional faces using standard results from convex geometry. The tactic analyzes the vertices of the tetrahedron and computes all possible 1-dimensional faces, which are exactly the six edges listed in the theorem statement.

### Mathematical insight
This theorem provides a complete characterization of the edges of the standard tetrahedron. The standard tetrahedron has 4 vertices, and the theorem confirms that it has exactly 6 edges (which is the maximum number of edges possible for a 4-vertex polyhedron).

The edges form the 1-skeleton of the tetrahedron, which is important for various geometric and topological analyses. This characterization is particularly useful for further results about tetrahedra and for computational geometry applications.

The standard tetrahedron in HOL Light is defined as the convex hull of four specific points in $\mathbb{R}^3$, chosen to have a regular structure with coordinates involving only 1 and -1.

### Dependencies
- **Theorems**:
  - `STD_TETRAHEDRON_FULLDIM`: States that the affine dimension of the standard tetrahedron is 3
  - `TETRAHEDRON_FACETS`: Characterizes the 2-dimensional faces (facets) of the standard tetrahedron
- **Definitions**:
  - `std_tetrahedron`: Defines the standard tetrahedron as the convex hull of four specific points in $\mathbb{R}^3$

### Porting notes
When porting this theorem:
1. Ensure the definition of the standard tetrahedron is consistent with HOL Light's definition
2. The tactic `COMPUTE_EDGES_TAC` is a specialized HOL Light tactic - you may need to implement an equivalent computation method in the target system
3. You'll need to establish the supporting theorems about face-of relations and affine dimensions in your target system

---

## CUBE_EDGES

### CUBE_EDGES

### Type of the formal statement
- theorem

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
For any set $e$ in $\mathbb{R}^3$, $e$ is a 1-dimensional face of the standard cube if and only if $e$ is the convex hull of one of the following pairs of vertices:
- $\{\mathbf{v}(-1,-1,-1), \mathbf{v}(-1,-1,1)\}$
- $\{\mathbf{v}(-1,-1,-1), \mathbf{v}(-1,1,-1)\}$
- $\{\mathbf{v}(-1,-1,-1), \mathbf{v}(1,-1,-1)\}$
- $\{\mathbf{v}(-1,-1,1), \mathbf{v}(-1,1,1)\}$
- $\{\mathbf{v}(-1,-1,1), \mathbf{v}(1,-1,1)\}$
- $\{\mathbf{v}(-1,1,-1), \mathbf{v}(-1,1,1)\}$
- $\{\mathbf{v}(-1,1,-1), \mathbf{v}(1,1,-1)\}$
- $\{\mathbf{v}(-1,1,1), \mathbf{v}(1,1,1)\}$
- $\{\mathbf{v}(1,-1,-1), \mathbf{v}(1,-1,1)\}$
- $\{\mathbf{v}(1,-1,-1), \mathbf{v}(1,1,-1)\}$
- $\{\mathbf{v}(1,-1,1), \mathbf{v}(1,1,1)\}$
- $\{\mathbf{v}(1,1,-1), \mathbf{v}(1,1,1)\}$

where $\mathbf{v}(a,b,c)$ denotes the vector $[a,b,c]$ in $\mathbb{R}^3$, and the standard cube is the convex hull of the eight vertices $\mathbf{v}(\pm 1, \pm 1, \pm 1)$.

### Informal proof
This theorem is proven using a special tactic `COMPUTE_EDGES_TAC` which automates the calculation of 1-dimensional faces (edges) of a polytope. The tactic takes three arguments:
- `std_cube`: the standard cube in $\mathbb{R}^3$
- `STD_CUBE_FULLDIM`: a theorem stating that the affine dimension of the standard cube is 3
- `CUBE_FACETS`: a theorem characterizing the 2-dimensional faces (facets) of the standard cube

The tactic works by:
1. Identifying all vertices of the standard cube
2. Computing all pairs of vertices that form valid edges of the cube
3. Verifying that each edge is indeed a 1-dimensional face of the cube

The result is a complete enumeration of all 12 edges of the standard cube, each formed by connecting two adjacent vertices.

### Mathematical insight
This theorem provides a complete characterization of the edges (1-dimensional faces) of the standard cube in $\mathbb{R}^3$. The standard cube has 8 vertices and 12 edges, which are precisely the line segments connecting adjacent vertices.

The edges of a polytope are fundamental to understanding its combinatorial structure. This theorem is part of a broader analysis of the facial structure of the standard cube, complementing `CUBE_FACETS` which characterizes its 2-dimensional faces.

In polyhedral combinatorics, the face lattice (the collection of all faces ordered by inclusion) fully determines the combinatorial type of a polytope. This theorem identifies exactly the rank-1 elements of this lattice for the standard cube.

### Dependencies
- **Theorems**:
  - `CUBE_FACETS`: Characterizes the 2-dimensional faces of the standard cube
  - `STD_CUBE_FULLDIM`: States that the affine dimension of the standard cube is 3
- **Definitions**:
  - `std_cube`: Defines the standard cube as the convex hull of the eight vertices $\mathbf{v}(\pm 1, \pm 1, \pm 1)$

### Porting notes
When porting this theorem:
1. Ensure that the underlying theory of polytopes and faces is available in the target system
2. The proof uses a specialized tactic `COMPUTE_EDGES_TAC` which may need to be reimplemented or replaced with a more general approach
3. Consider using a more declarative proof that starts with the definition of the standard cube, computes its vertices, and then explicitly verifies each edge

---

## OCTAHEDRON_EDGES

### OCTAHEDRON_EDGES
- OCTAHEDRON_EDGES

### Type of the formal statement
- theorem

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
For any set $e$, $e$ is a 1-dimensional face of the standard octahedron if and only if $e$ is equal to the convex hull of one of the following pairs of vertices:
- $\{\text{vector}[-1, 0, 0], \text{vector}[0, -1, 0]\}$
- $\{\text{vector}[-1, 0, 0], \text{vector}[0, 1, 0]\}$
- $\{\text{vector}[-1, 0, 0], \text{vector}[0, 0, -1]\}$
- $\{\text{vector}[-1, 0, 0], \text{vector}[0, 0, 1]\}$
- $\{\text{vector}[1, 0, 0], \text{vector}[0, -1, 0]\}$
- $\{\text{vector}[1, 0, 0], \text{vector}[0, 1, 0]\}$
- $\{\text{vector}[1, 0, 0], \text{vector}[0, 0, -1]\}$
- $\{\text{vector}[1, 0, 0], \text{vector}[0, 0, 1]\}$
- $\{\text{vector}[0, -1, 0], \text{vector}[0, 0, -1]\}$
- $\{\text{vector}[0, -1, 0], \text{vector}[0, 0, 1]\}$
- $\{\text{vector}[0, 1, 0], \text{vector}[0, 0, -1]\}$
- $\{\text{vector}[0, 1, 0], \text{vector}[0, 0, 1]\}$

Where the standard octahedron, denoted as `std_octahedron`, is defined as the convex hull of the six points $\{\text{vector}[1,0,0], \text{vector}[-1,0,0], \text{vector}[0,0,1], \text{vector}[0,0,-1], \text{vector}[0,1,0], \text{vector}[0,-1,0]\}$ in $\mathbb{R}^3$.

### Informal proof
The proof is performed by the tactic `COMPUTE_EDGES_TAC`, which computes all the edges of the octahedron systematically. This tactic:

1. Uses `std_octahedron` as its input polyhedron
2. Uses `STD_OCTAHEDRON_FULLDIM` to establish that the octahedron is a full-dimensional object in $\mathbb{R}^3$
3. Uses `OCTAHEDRON_FACETS` which provides the facets (2-dimensional faces) of the octahedron

The algorithm determines the edges by examining the facets of the octahedron and identifying their 1-dimensional intersections. Since the edges of a polyhedron are precisely the 1-dimensional faces, the tactic computes all possible pairs of vertices that form 1-dimensional faces of the standard octahedron.

The computation results in exactly 12 edges as listed in the theorem statement, which aligns with the combinatorial property that an octahedron has 12 edges connecting its 6 vertices.

### Mathematical insight
This theorem explicitly enumerates all the edges of the standard octahedron in $\mathbb{R}^3$. An octahedron has 6 vertices, 12 edges, and 8 faces, which is verified by this computation. Each vertex of the octahedron is connected to exactly 4 other vertices, forming the 12 edges in total.

The standard octahedron is positioned with vertices at the points $(\pm1,0,0)$, $(0,\pm1,0)$, and $(0,0,\pm1)$, which corresponds to the unit vectors along the coordinate axes in both positive and negative directions. This positioning makes the octahedron highly symmetric with respect to the coordinate planes.

The result is important for various applications in computational geometry, polytope theory, and the study of Platonic solids, as it provides the complete edge structure of an octahedron in a standard reference position.

### Dependencies
- **Theorems**:
  - `OCTAHEDRON_FACETS`: Characterizes the 2-dimensional faces of the standard octahedron
  - `STD_OCTAHEDRON_FULLDIM`: Establishes that the standard octahedron has affine dimension 3

- **Definitions**:
  - `std_octahedron`: Defines the standard octahedron as the convex hull of the six vertices at positions $(\pm1,0,0)$, $(0,\pm1,0)$, and $(0,0,\pm1)$

### Porting notes
When porting this theorem to other systems:
1. Ensure that the convex hull operation is properly defined
2. The face relation (face_of) must be implemented correctly
3. The affine dimension concept needs to match the HOL Light definition
4. The vector notation may need adaptation to the target system's syntax
5. The automated tactic `COMPUTE_EDGES_TAC` would need to be replaced with either:
   - A similar algorithm in the target system
   - A direct proof verifying each edge individually
   - An appropriate automated method for computing combinatorial properties of polyhedra

---

## DODECAHEDRON_EDGES

### DODECAHEDRON_EDGES

### Type of the formal statement
- theorem

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
This theorem provides a complete characterization of the edges of a standard dodecahedron. It states that for any set $e$, $e$ is a face of the standard dodecahedron with affine dimension 1 if and only if $e$ is one of the 30 specific line segments (edges) described in the theorem.

Specifically, the theorem states:

For all sets $e$, $e$ is a face of the standard dodecahedron with affine dimension 1 if and only if $e$ equals one of the 30 convex hulls of pairs of vertices of the standard dodecahedron, where each convex hull represents a line segment connecting two vertices.

### Informal proof
The proof is executed using a specialized tactic `COMPUTE_EDGES_TAC` which computes all the edges of the standard dodecahedron based on:
1. The definition of the standard dodecahedron (`STD_DODECAHEDRON`)
2. The fact that the standard dodecahedron has full affine dimension 3 (`STD_DODECAHEDRON_FULLDIM`)
3. The characterization of the 12 pentagonal facets of the dodecahedron (`DODECAHEDRON_FACETS`)

The computation proceeds by:
- Starting with the known vertices of the standard dodecahedron
- Identifying all pairs of vertices that form an edge in the polytope
- Using the fact that an edge is a 1-dimensional face that is the intersection of at least two 2-dimensional faces (facets)
- Verifying each candidate edge against the facet structure of the dodecahedron

The result is the complete list of 30 edges, which matches the expected number of edges for a regular dodecahedron.

### Mathematical insight
The dodecahedron is one of the five Platonic solids and has 12 pentagonal faces, 30 edges, and 20 vertices. This theorem explicitly identifies all 30 edges of the standard dodecahedron in 3-dimensional space.

The vertices of the dodecahedron involve the golden ratio $\phi = \frac{1+\sqrt{5}}{2}$ and its inverse. This is a characteristic feature of the dodecahedron and is related to its high degree of symmetry.

The result is important for understanding the combinatorial and geometric structure of the dodecahedron. By explicitly listing all edges, it provides a complete characterization of the 1-skeleton of the dodecahedron, which is crucial for various geometric computations and for understanding its symmetry properties.

### Dependencies
- `STD_DODECAHEDRON`: Definition of the standard dodecahedron in terms of the convex hull of 20 specific points in 3D space
- `STD_DODECAHEDRON_FULLDIM`: Theorem stating that the standard dodecahedron has affine dimension 3
- `DODECAHEDRON_FACETS`: Theorem providing a characterization of all 12 pentagonal faces of the standard dodecahedron
- `COMPUTE_EDGES_TAC`: A specialized tactic for computing the edges of a polytope given its vertices and facets

### Porting notes
When porting this theorem to another proof assistant:
1. First ensure that the standard dodecahedron is defined, typically as the convex hull of its 20 vertices.
2. Verify that you have a characterization of the 12 pentagonal facets.
3. The computation of edges can be done by identifying pairs of vertices that lie on at least two common facets.
4. In systems without specialized tactics like `COMPUTE_EDGES_TAC`, you'll need to prove each edge individually or develop a suitable automation strategy.
5. Be aware that handling the expressions involving the golden ratio and square roots might require different approaches in different proof assistants.

---

## ICOSAHEDRON_EDGES

### ICOSAHEDRON_EDGES
- `ICOSAHEDRON_EDGES`

### Type of the formal statement
- theorem

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
The theorem characterizes all the edges of the standard icosahedron in 3D space. It states that a set $e$ is a 1-dimensional face of the standard icosahedron if and only if it equals one of the 30 explicitly listed line segments, where each line segment is described as the convex hull of two vertices of the icosahedron.

Mathematically, for any set $e \subset \mathbb{R}^3$:

$$e \text{ face\_of } \text{std\_icosahedron} \land \text{aff\_dim}(e) = 1 \iff e \in \{e_1, e_2, \ldots, e_{30}\}$$

where each $e_i$ is of the form $\text{convex hull}\{v_j, v_k\}$ for specific vertices $v_j, v_k$ of the standard icosahedron.

### Informal proof
This theorem provides a complete inventory of all edges (1-dimensional faces) of the standard icosahedron. The proof is accomplished using a computational tactic specifically designed for enumeration of edges.

The proof uses the tactic `COMPUTE_EDGES_TAC`, which takes three arguments:
- `STD_ICOSAHEDRON`: The definition of the standard icosahedron
- `STD_ICOSAHEDRON_FULLDIM`: A theorem stating that the affine dimension of the standard icosahedron is 3
- `ICOSAHEDRON_FACETS`: A theorem characterizing all the 2-dimensional faces (facets) of the icosahedron

The tactic algorithmically determines all 1-dimensional faces by examining the 2-dimensional faces and finding their intersections. Since the icosahedron is a convex polytope, each edge is the intersection of exactly two adjacent facets, and the tactic systematically enumerates all such intersections to produce the complete list of edges.

### Mathematical insight
The icosahedron is one of the five Platonic solids, with 12 vertices, 30 edges, and 20 faces (all equilateral triangles). This theorem precisely enumerates all 30 edges, which provides a complete description of the 1-dimensional combinatorial structure of the icosahedron.

The standard icosahedron in this formalization is positioned with vertices at specific coordinates involving the golden ratio (expressed as $\frac{1 + \sqrt{5}}{2}$), which gives it elegant geometric properties and symmetry.

This edge enumeration is crucial for various geometric and topological investigations of the icosahedron, including:
- Computing its Euler characteristic (vertices - edges + faces = 2)
- Analyzing its symmetry group
- Studying its dihedral angles
- Calculating geometric measures like surface area and volume

### Dependencies
- `STD_ICOSAHEDRON`: Definition of the standard icosahedron in 3D space
- `STD_ICOSAHEDRON_FULLDIM`: Theorem stating the standard icosahedron has affine dimension 3
- `ICOSAHEDRON_FACETS`: Theorem characterizing all 2-dimensional faces of the standard icosahedron
- `COMPUTE_EDGES_TAC`: Tactic for algorithmically computing edges of a polyhedron

### Porting notes
When porting this to other proof assistants:
1. A suitable polytope library will be needed with notions of faces, convex hulls, and affine dimensions
2. The standard icosahedron definition needs to be ported first
3. The implementation might require developing a computational procedure similar to `COMPUTE_EDGES_TAC` to automatically derive the edges from facets
4. Some systems might benefit from expressing the theorem in a more compact form, possibly using set comprehension rather than explicit enumeration
5. The coordinates involve square roots and fractions, so appropriate real number handling is needed

---

## COMPUTE_VERTICES_TAC

### COMPUTE_VERTICES_TAC

### Type of the formal statement
- Custom tactic definition

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
This is a custom tactic for computing the vertices of a polyhedron in $\mathbb{R}^3$. The tactic takes three arguments:
- `defn`: A theorem defining the polyhedron `p`
- `fulldim`: A theorem about the affine dimension of the polyhedron
- `edges`: A theorem characterizing the edges of the polyhedron

The tactic establishes an equivalence between two ways of characterizing a vertex `v` of a polyhedron `p`:
1. `v` is a vertex (face of dimension 0) of `p`
2. `v` is a vertex of some edge `e` of `p`, where an edge is a face of dimension 1

### Informal proof
The tactic proves this equivalence using the following approach:

- First, it sets up a goal to show the equivalence between "being a vertex of the polyhedron" and "being a vertex of some edge of the polyhedron"
- The proof then proceeds in two directions:

**Forward direction (vertex of polyhedron ⟹ vertex of some edge):**
- If `v` is a vertex of the polyhedron `p`, then by the theorem `FACE_OF_POLYHEDRON_SUBSET_FACET`, `v` is contained in some facet `f` of `p`
- We establish that `p` is indeed a polyhedron using the definition provided
- We verify that the affine dimensions are appropriate (the polyhedron has full dimension and `v` has dimension 0)
- We then apply `FACE_OF_POLYHEDRON_SUBSET_FACET` again to show that `v` is contained in some face of dimension 1 (an edge) of the facet
- Using transitivity of the face_of relation, we conclude that `v` is a vertex of some edge of the polyhedron

**Reverse direction (vertex of some edge ⟹ vertex of polyhedron):**
- This direction uses properties of faces, particularly that if `v` is a face of an edge `e` and `e` is a face of `p`, then `v` is a face of `p`
- The tactic also uses the characterization of edges and vertices in terms of extreme points of segments
- It rewrites the goal using the definition of edges and properties of affine dimension, segments, and extreme points
- Through a series of logical manipulations, it establishes that a face of dimension 0 of an edge is indeed a vertex of the original polyhedron

### Mathematical insight
This tactic implements a fundamental result about vertices of polyhedra in $\mathbb{R}^3$: a vertex can be characterized either directly (as a 0-dimensional face) or through its relationship with edges (1-dimensional faces).

The key insight is that for polyhedra, vertices can always be accessed by following down the face lattice - specifically, any vertex must be a face of some edge. This provides an alternative way to enumerate all vertices by first enumerating all edges and then collecting their endpoints.

This characterization is particularly useful in computational geometry and for algorithms that need to traverse the face structure of polyhedra. It allows one to compute all vertices by first computing all the edges.

### Dependencies
- **Polyhedron Theorems:**
  - `FACE_OF_POLYHEDRON_SUBSET_FACET`: Relates faces of a polyhedron to facets
  - `POLYHEDRON_CONVEX_HULL`: States that the convex hull of a finite set is a polyhedron
  - `FACE_OF_POLYHEDRON_POLYHEDRON`: States that faces of polyhedra are polyhedra

- **Dimensional Properties:**
  - `AFF_DIM_EMPTY`: The affine dimension of the empty set
  - `AFF_DIM_EQ_0`: Characterization of sets with affine dimension 0

- **Face Relationship Theorems:**
  - `FACE_OF_TRANS`: Transitivity of the face_of relation
  - `FACE_OF_FACE`: Inheritance of face properties

- **Segment and Extreme Point Theorems:**
  - `SEGMENT_CONVEX_HULL`: Representation of a segment as a convex hull
  - `FACE_OF_SING`: Characterization of singleton faces
  - `EXTREME_POINT_OF_SEGMENT`: Characterizes extreme points of a segment

### Porting notes
When porting this tactic to another proof assistant:
1. Ensure that the target system has appropriate theorems about polyhedra, faces, and affine dimensions
2. The tactic makes heavy use of higher-order instantiation and forward reasoning, which might need different approaches in systems like Lean or Isabelle
3. The dimension-specific reasoning (for $\mathbb{R}^3$) might need generalization or specialization depending on the target system's library
4. The logical manipulations using `TAUT` and other conversion operators would need to be translated to equivalent mechanisms in the target system

---

## TETRAHEDRON_VERTICES

### TETRAHEDRON_VERTICES

### Type of the formal statement
- theorem

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
For any set $v$, $v$ is a face of the standard tetrahedron with affine dimension 0 if and only if $v$ is one of the following singleton sets:
- $\{\text{vector}[-1, -1, 1]\}$
- $\{\text{vector}[-1, 1, -1]\}$
- $\{\text{vector}[1, -1, -1]\}$
- $\{\text{vector}[1, 1, 1]\}$

### Informal proof
The proof is performed using the `COMPUTE_VERTICES_TAC` tactic, which is specifically designed to compute the vertices of a polytope. 

This tactic takes three arguments:
1. The polytope (`std_tetrahedron`)
2. A theorem stating that the polytope has full dimension (`STD_TETRAHEDRON_FULLDIM`)
3. A theorem describing the edges of the polytope (`TETRAHEDRON_EDGES`)

The tactic works by computing the vertices as the 0-dimensional faces of the polytope, using the fact that vertices are precisely the 0-dimensional faces of a polytope.

### Mathematical insight
This theorem explicitly characterizes the vertices of the standard tetrahedron in $\mathbb{R}^3$. The standard tetrahedron is defined as the convex hull of four specific points in 3D space.

The vertices of any polytope are precisely its 0-dimensional faces. This theorem confirms that the standard tetrahedron has exactly four vertices, which matches our geometric intuition.

The coordinates of the vertices follow a pattern with all possible combinations of 1 and -1 where an odd number of coordinates are 1. This specific choice of coordinates places the tetrahedron symmetrically in 3D space, making it a "standard" representation.

### Dependencies
- **Definitions**:
  - `std_tetrahedron`: Defines the standard tetrahedron as the convex hull of four specific points in $\mathbb{R}^3$

- **Theorems**:
  - `STD_TETRAHEDRON_FULLDIM`: States that the standard tetrahedron has affine dimension 3
  - `TETRAHEDRON_EDGES`: Characterizes the edges (1-dimensional faces) of the standard tetrahedron

### Porting notes
When porting this theorem:
1. Ensure that your system has a way to represent vectors and sets of vectors
2. Verify that your system has notions of faces of polytopes and affine dimension
3. The `COMPUTE_VERTICES_TAC` is a specialized tactic that may need to be reimplemented or replaced with appropriate reasoning in the target system
4. The statement is straightforward, but the proof might require different techniques depending on what automation is available in the target system

---

## CUBE_VERTICES

### CUBE_VERTICES

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
For any set $v$, the set $v$ is a $0$-dimensional face of the standard cube if and only if $v$ is one of the following single-point sets:
- $\{(-1, -1, -1)\}$
- $\{(-1, -1, 1)\}$
- $\{(-1, 1, -1)\}$
- $\{(-1, 1, 1)\}$
- $\{(1, -1, -1)\}$
- $\{(1, -1, 1)\}$
- $\{(1, 1, -1)\}$
- $\{(1, 1, 1)\}$

Here, the standard cube (`std_cube`) is defined as the convex hull of the eight points listed above, and a $0$-dimensional face corresponds to a vertex of the cube.

### Informal proof
The theorem is proved using a specialized tactic `COMPUTE_VERTICES_TAC` which takes three arguments:
1. `std_cube`: the standard cube in $\mathbb{R}^3$
2. `STD_CUBE_FULLDIM`: a theorem stating that the standard cube has full affine dimension (i.e., $\dim(\text{std\_cube}) = 3$)
3. `CUBE_EDGES`: a theorem characterizing the edges (1-dimensional faces) of the standard cube

The tactic computes the vertices of the cube by:
- Starting with the known edges (1-dimensional faces) of the cube
- Finding the endpoints of these edges, which must be the vertices
- Verifying that these points satisfy the definition of 0-dimensional faces

The proof relies on the mathematical fact that the vertices of a convex polytope are precisely its 0-dimensional faces, and each 0-dimensional face is a singleton set containing exactly one point.

### Mathematical insight
This theorem provides a complete characterization of the vertices of the standard cube in 3D space, positioned with its center at the origin and having side length 2. The vertices are the eight points with coordinates $(\pm 1, \pm 1, \pm 1)$.

In computational geometry and polytope theory, identifying the vertices of a polytope is a fundamental task. For the standard cube, the vertices are particularly simple to describe due to the symmetry of the cube and its standard position in the coordinate system.

This theorem could be used in further results about the standard cube, such as calculating its volume, surface area, or analyzing its symmetry group. It's also useful for proving properties of general regular polytopes by using the standard cube as a reference example.

### Dependencies
- **Definitions**
  - `std_cube`: The standard cube in $\mathbb{R}^3$, defined as the convex hull of the eight points with coordinates $(\pm 1, \pm 1, \pm 1)$

- **Theorems**
  - `STD_CUBE_FULLDIM`: States that the standard cube has affine dimension 3
  - `CUBE_EDGES`: Characterizes all the 1-dimensional faces (edges) of the standard cube

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that the definition of the standard cube is equivalent
2. The representation of vectors might differ in other systems
3. The proof strategy may need to be adapted based on the available tactics
4. The notion of "face_of" and "aff_dim" should be defined in a compatible way
5. Consider using a more direct proof approach if computational tactics like `COMPUTE_VERTICES_TAC` are not available in the target system

---

## OCTAHEDRON_VERTICES

### OCTAHEDRON_VERTICES

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
For any set $v$, $v$ is a face of the standard octahedron with affine dimension 0 if and only if $v$ is one of the following singleton sets:
- $\{\vec{v}_1\}$ where $\vec{v}_1 = (-1, 0, 0)$
- $\{\vec{v}_2\}$ where $\vec{v}_2 = (1, 0, 0)$
- $\{\vec{v}_3\}$ where $\vec{v}_3 = (0, -1, 0)$
- $\{\vec{v}_4\}$ where $\vec{v}_4 = (0, 1, 0)$
- $\{\vec{v}_5\}$ where $\vec{v}_5 = (0, 0, -1)$
- $\{\vec{v}_6\}$ where $\vec{v}_6 = (0, 0, 1)$

Here, a face with affine dimension 0 corresponds to a vertex of the octahedron.

### Informal proof
This theorem is proved using the tactic `COMPUTE_VERTICES_TAC`, which derives all vertices of a polytope from its edges. The proof relies on the following key facts:

- The standard octahedron is full-dimensional in $\mathbb{R}^3$ (by theorem `STD_OCTAHEDRON_FULLDIM`)
- The complete characterization of the edges of the octahedron (by theorem `OCTAHEDRON_EDGES`)

The tactic computes all faces of affine dimension 0 (vertices) by identifying the endpoints of all edges of the octahedron. Since every vertex of a polytope must be the endpoint of at least one edge, and conversely, every endpoint of an edge must be a vertex, this approach ensures all vertices are identified correctly.

### Mathematical insight
This theorem provides a complete characterization of the vertices of the standard octahedron in $\mathbb{R}^3$. The standard octahedron has 6 vertices, each positioned at unit distance from the origin along the coordinate axes.

The vertices form the set $\{(±1,0,0), (0,±1,0), (0,0,±1)\}$, which gives the octahedron its characteristic symmetric shape. Each vertex is connected to 4 other vertices by edges, and these vertices are equidistant from the origin.

This result is part of the broader study of Platonic solids and regular polyhedra in three-dimensional space. The octahedron is dual to the cube, meaning the vertices of the octahedron correspond to the faces of the cube and vice versa.

### Dependencies
- **Theorems**:
  - `STD_OCTAHEDRON_FULLDIM`: Proves that the standard octahedron has affine dimension 3
  - `OCTAHEDRON_EDGES`: Characterizes all edges (faces of affine dimension 1) of the standard octahedron
- **Definitions**:
  - `std_octahedron`: Defines the standard octahedron as the convex hull of the six points at unit distance from the origin along the coordinate axes

### Porting notes
When porting this theorem:
1. Ensure that the corresponding definition for the standard octahedron is in place
2. The proof relies on a specialized tactic for computing vertices from edges; an equivalent approach might need to be developed in the target system
3. The statement uses the notion of faces of a polytope and affine dimension, which may be represented differently in other systems

---

## DODECAHEDRON_VERTICES

### DODECAHEDRON_VERTICES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem characterizes all the vertices of the standard dodecahedron. Specifically, it states that a set $v$ is a 0-dimensional face of the standard dodecahedron if and only if $v$ is a singleton set containing one of the 20 vertices of the dodecahedron.

Formally, for any set $v$:
$v$ is a face of the standard dodecahedron with affine dimension 0 if and only if $v$ is one of the following singleton sets:
- $\{(-\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0, -\frac{1}{2} + \frac{1}{2}\sqrt{5})\}$
- $\{(-\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0, \frac{1}{2} - \frac{1}{2}\sqrt{5})\}$
- $\{(-\frac{1}{2} + \frac{1}{2}\sqrt{5}, -\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0)\}$
- $\{(-\frac{1}{2} + \frac{1}{2}\sqrt{5}, \frac{1}{2} + \frac{1}{2}\sqrt{5}, 0)\}$
- $\{(\frac{1}{2} - \frac{1}{2}\sqrt{5}, -\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0)\}$
- $\{(\frac{1}{2} - \frac{1}{2}\sqrt{5}, \frac{1}{2} + \frac{1}{2}\sqrt{5}, 0)\}$
- $\{(\frac{1}{2} + \frac{1}{2}\sqrt{5}, 0, -\frac{1}{2} + \frac{1}{2}\sqrt{5})\}$
- $\{(\frac{1}{2} + \frac{1}{2}\sqrt{5}, 0, \frac{1}{2} - \frac{1}{2}\sqrt{5})\}$
- $\{(-1, -1, -1)\}$
- $\{(-1, -1, 1)\}$
- $\{(-1, 1, -1)\}$
- $\{(-1, 1, 1)\}$
- $\{(1, -1, -1)\}$
- $\{(1, -1, 1)\}$
- $\{(1, 1, -1)\}$
- $\{(1, 1, 1)\}$
- $\{(0, -\frac{1}{2} + \frac{1}{2}\sqrt{5}, -\frac{1}{2} - \frac{1}{2}\sqrt{5})\}$
- $\{(0, -\frac{1}{2} + \frac{1}{2}\sqrt{5}, \frac{1}{2} + \frac{1}{2}\sqrt{5})\}$
- $\{(0, \frac{1}{2} - \frac{1}{2}\sqrt{5}, -\frac{1}{2} - \frac{1}{2}\sqrt{5})\}$
- $\{(0, \frac{1}{2} - \frac{1}{2}\sqrt{5}, \frac{1}{2} + \frac{1}{2}\sqrt{5})\}$

### Informal proof
This theorem is proved by using the specialized tactic `COMPUTE_VERTICES_TAC`, which computes the vertices of a polyhedron from its edges. The proof logic follows these steps:

- The standard dodecahedron is a 3-dimensional polyhedron (as established by `STD_DODECAHEDRON_FULLDIM`).
- The edges of the dodecahedron have been completely characterized by `DODECAHEDRON_EDGES`.
- The vertices are the 0-dimensional faces, which are precisely the endpoints of the edges.
- The `COMPUTE_VERTICES_TAC` tactic takes these inputs and systematically computes all vertices by examining the endpoints of all edges and determining which ones are distinct.
- The tactic then proves that these 20 vertices are exactly the 0-dimensional faces of the dodecahedron.

### Mathematical insight
This theorem provides the explicit coordinates of all 20 vertices of the standard dodecahedron in 3D space. The vertices form a highly symmetric structure and come in two types:

1. 8 vertices at positions where all coordinates are ±1
2. 12 vertices where one coordinate is 0 and the other two involve the golden ratio φ = (1+√5)/2 or its inverse

The dodecahedron is one of the five Platonic solids and has special geometric properties. It has:
- 20 vertices (proven by this theorem)
- 30 edges (characterized by `DODECAHEDRON_EDGES`)
- 12 pentagonal faces

Understanding the precise coordinates of the vertices is fundamental for further analysis of the dodecahedron's geometric properties and its relationship to other mathematical structures.

### Dependencies
- `STD_DODECAHEDRON`: Definition of the standard dodecahedron as the convex hull of 20 points in 3D space
- `STD_DODECAHEDRON_FULLDIM`: Theorem establishing that the standard dodecahedron has affine dimension 3
- `DODECAHEDRON_EDGES`: Theorem characterizing all the edges (1-dimensional faces) of the standard dodecahedron

### Porting notes
When porting this theorem:
- Ensure the golden ratio φ = (1+√5)/2 and related expressions are correctly defined
- The HOL Light tactic `COMPUTE_VERTICES_TAC` needs to be reimplemented or replaced with an equivalent approach for computing vertices from edges
- The convex-hull representation of polyhedra may need to be adapted to the target system's geometric libraries
- The representation of 0-dimensional faces as singleton sets might need adjustment based on how the target system represents vertices of polyhedra

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
The theorem characterizes all vertices (0-dimensional faces) of the standard icosahedron in $\mathbb{R}^3$. It states that for any set $v$:

$v$ is a face of the standard icosahedron with affine dimension 0 if and only if $v$ is one of the following 12 singleton sets:
- $\{\vec{v}_1\} = \{(-\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0, -1)\}$
- $\{\vec{v}_2\} = \{(-\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0, 1)\}$
- $\{\vec{v}_3\} = \{(\frac{1}{2} + \frac{1}{2}\sqrt{5}, 0, -1)\}$
- $\{\vec{v}_4\} = \{(\frac{1}{2} + \frac{1}{2}\sqrt{5}, 0, 1)\}$
- $\{\vec{v}_5\} = \{(-1, -\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0)\}$
- $\{\vec{v}_6\} = \{(-1, \frac{1}{2} + \frac{1}{2}\sqrt{5}, 0)\}$
- $\{\vec{v}_7\} = \{(1, -\frac{1}{2} - \frac{1}{2}\sqrt{5}, 0)\}$
- $\{\vec{v}_8\} = \{(1, \frac{1}{2} + \frac{1}{2}\sqrt{5}, 0)\}$
- $\{\vec{v}_9\} = \{(0, -1, -\frac{1}{2} - \frac{1}{2}\sqrt{5})\}$
- $\{\vec{v}_{10}\} = \{(0, -1, \frac{1}{2} + \frac{1}{2}\sqrt{5})\}$
- $\{\vec{v}_{11}\} = \{(0, 1, -\frac{1}{2} - \frac{1}{2}\sqrt{5})\}$
- $\{\vec{v}_{12}\} = \{(0, 1, \frac{1}{2} + \frac{1}{2}\sqrt{5})\}$

### Informal proof
The theorem is proven using the `COMPUTE_VERTICES_TAC` tactic, which computes the vertices of a polyhedron given:
1. The polyhedron itself (`STD_ICOSAHEDRON`)
2. A theorem stating that it has full dimension (`STD_ICOSAHEDRON_FULLDIM`)
3. A theorem characterizing its edges (`ICOSAHEDRON_EDGES`)

The approach uses the fact that vertices of a polyhedron are precisely its 0-dimensional faces. The tactic works by:
- Starting with the edges of the icosahedron (1-dimensional faces)
- Computing their intersections with other faces
- Identifying the resulting singleton sets as the vertices

The calculation confirms that these 12 points are exactly the vertices of the standard icosahedron.

### Mathematical insight
This theorem gives an explicit coordinate representation of the 12 vertices of the standard icosahedron in $\mathbb{R}^3$. The standard icosahedron is a regular polyhedron with 20 triangular faces, 30 edges, and 12 vertices. 

The coordinates involve the golden ratio $\phi = \frac{1 + \sqrt{5}}{2}$, which appears frequently in the geometry of regular polyhedra. Notice that the coordinates follow a pattern of permutations and sign changes, reflecting the symmetry of the icosahedron.

Understanding the exact coordinates of the vertices is fundamental for various applications:
- Computing other geometric properties of the icosahedron
- Proving theorems about its symmetries
- Establishing relationships with other Platonic solids

This result is part of a larger formalization of Platonic solids in HOL Light.

### Dependencies
- Theorems:
  - `STD_ICOSAHEDRON`: Defines the standard icosahedron as the convex hull of 12 points
  - `STD_ICOSAHEDRON_FULLDIM`: States that the standard icosahedron has affine dimension 3
  - `ICOSAHEDRON_EDGES`: Characterizes the 30 edges of the standard icosahedron
- Definitions:
  - `std_icosahedron`: Defines the standard icosahedron in terms of the golden ratio

### Porting notes
When porting this theorem:
1. Ensure your target system has a well-developed theory of convex polyhedra with notions of faces and affine dimension
2. The representation of vectors may differ between systems - adapt the coordinate format accordingly
3. The tactic `COMPUTE_VERTICES_TAC` encapsulates complex reasoning about polyhedron vertices - you may need to create a custom tactic or proof strategy in the target system
4. The golden ratio appears implicitly in the vertex coordinates - your target system should have support for algebraic expressions involving square roots

---

## EDGES_PER_VERTEX_TAC

### Name of formal statement
EDGES_PER_VERTEX_TAC

### Type of the formal statement
Tactic function

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
`EDGES_PER_VERTEX_TAC` is a tactic that helps prove the number of edges meeting at each vertex of a polyhedron. It takes three arguments:
- `defn`: A definition/theorem that characterizes a specific polyhedron
- `edges`: A characterization of the edges of the polyhedron
- `verts`: A characterization of the vertices of the polyhedron

The tactic proves that the number of edges meeting at a given vertex equals the cardinality of the set of edges that have the vertex as a face.

### Informal proof
The tactic constructs a proof with the following structure:

- First, it establishes that the number of edges meeting at a vertex equals the cardinality of the set $\{e \mid e \text{ face_of } p \land \text{aff_dim}(e) = 1 \land v \text{ face_of } e\}$, where $p$ is the polyhedron and $v$ is the vertex.

- The tactic then splits the set of edges into those that can be represented as segments between pairs of vertices.

- For each vertex in the polyhedron:
  - It reduces the problem to counting distinct segments connecting the vertex to other vertices.
  - It uses vector algebra to establish that these segments are distinct.
  - It computes the cardinality of this set using `CARD_EQ_LEMMA` repeatedly.

- The proof relies on several key transformations:
  - Converting segments to vector form using `VECTOR3_SUB_CONV`
  - Testing vector equality with `VECTOR3_EQ_0_CONV`
  - Computing the cardinality of sets iteratively

- Finally, it simplifies numerical expressions to complete the proof.

### Mathematical insight
This tactic is designed to automate a common task in polyhedron analysis: counting how many edges meet at each vertex of a polyhedron (also known as the "valence" of a vertex). This value is an important combinatorial property of polyhedra, especially for regular polyhedra where all vertices have the same valence.

The key insight is the representation of the problem in terms of set cardinality and the systematic construction of the set of edges meeting at a vertex. The tactic exploits the structure of polyhedra where edges can be expressed as segments between vertices.

This tactic serves as a building block in the verification of properties of Platonic solids and other regular polyhedra, where the number of edges per vertex is a defining characteristic.

### Dependencies
- **Theorems**:
  - `CARD_EQ_LEMMA`: A theorem about the cardinality of sets with inserted elements
  - `VECTOR3_SUB_CONV`: A conversion for vector subtraction in 3D space
  - `VECTOR3_EQ_0_CONV`: A conversion for testing equality of a 3D vector with the zero vector

### Porting notes
When porting this tactic to another proof assistant:
- Special attention should be paid to how sets and their cardinality are represented
- Vector operations and equality testing may need different implementations
- The conversion-style reasoning used in HOL Light might need to be adapted to the target system's proof style
- The tactic makes heavy use of rewriting and conversions, which might need different implementations in systems with different automation approaches

---

## TETRAHEDRON_EDGES_PER_VERTEX

### TETRAHEDRON_EDGES_PER_VERTEX
- State the exact name of the formal item as it appears in the HOL Light source.

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
For any vertex $v$ that is a face of the standard tetrahedron with affine dimension 0, the number of edges (faces with affine dimension 1) of the standard tetrahedron that contain $v$ is exactly 3.

Formally, for all $v$:
$$v \text{ face_of } \text{std\_tetrahedron} \land \text{aff\_dim}(v) = 0 \Rightarrow$$
$$|\{e \mid e \text{ face_of } \text{std\_tetrahedron} \land \text{aff\_dim}(e) = 1 \land v \subseteq e\}| = 3$$

### Informal proof
This theorem is proved using the general tactic `EDGES_PER_VERTEX_TAC` that computes the number of edges incident to each vertex of a polytope, given the complete characterizations of the edges and vertices.

The proof relies on:
- `TETRAHEDRON_VERTICES`, which provides the complete characterization of the four vertices of the standard tetrahedron
- `TETRAHEDRON_EDGES`, which provides the complete characterization of the six edges of the standard tetrahedron

The tactic counts, for each vertex, the number of edges that contain that vertex. Since the standard tetrahedron is a regular polyhedron, each vertex has the same number of incident edges, namely 3.

### Mathematical insight
This theorem captures a fundamental property of tetrahedra: each vertex is connected to exactly 3 edges. This is a special case of the more general fact that in an n-dimensional simplex, each vertex is connected to exactly n edges.

The standard tetrahedron is the 3-dimensional regular simplex, and this property confirms its combinatorial structure. This is important for analyzing the connectivity and structure of polyhedra, particularly when working with their graph representations.

This result also aligns with the general formula for k-dimensional faces incident to a vertex in an n-dimensional simplex, which is ${n \choose k}$. In this case, we have ${3 \choose 1} = 3$ edges per vertex.

### Dependencies
- **Theorems**:
  - `TETRAHEDRON_EDGES` - Characterizes all edges of the standard tetrahedron
  - `TETRAHEDRON_VERTICES` - Characterizes all vertices of the standard tetrahedron

- **Definitions**:
  - `std_tetrahedron` - The standard tetrahedron defined as the convex hull of four specific points in 3D space

### Porting notes
When porting this theorem to another system:
1. Ensure that the notion of "face_of" and "aff_dim" are appropriately defined
2. The standard tetrahedron should be defined as specified in the dependencies
3. The proof relies on a specialized tactic; in other systems, you may need to verify the counting directly by enumerating all edges incident to each vertex
4. The cardinality calculation might require explicit set theory in some systems

---

## CUBE_EDGES_PER_VERTEX

### CUBE_EDGES_PER_VERTEX
- CUBE_EDGES_PER_VERTEX

### Type of the formal statement
- theorem

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
For any vertex $v$ of the standard cube (i.e., $v$ is a 0-dimensional face of the standard cube), the number of edges (i.e., 1-dimensional faces of the standard cube) containing $v$ is exactly 3.

More formally, for any set $v$ such that $v$ is a face of the standard cube with affine dimension 0, the cardinality of the set of all edges $e$ such that $e$ is a face of the standard cube with affine dimension 1 and $v$ is a subset of $e$ equals 3.

### Informal proof
The proof uses the tactic `EDGES_PER_VERTEX_TAC` with the standard cube and its edges and vertices theorems (`CUBE_EDGES` and `CUBE_VERTICES`).

This tactic handles the calculation automatically, but the mathematical reasoning is as follows:

- From `CUBE_VERTICES`, we know that the standard cube has exactly 8 vertices, which are the points where each coordinate is either -1 or 1.
- From `CUBE_EDGES`, we know that the standard cube has exactly 12 edges, each being the convex hull of two vertices that differ in exactly one coordinate.
- Each vertex in a three-dimensional cube is connected to exactly 3 edges, corresponding to the three possible coordinate directions.
- For any vertex $v$, the set $\{e \mid e \text{ face_of } \text{std_cube} \land \text{aff_dim}(e) = 1 \land v \subset e\}$ contains exactly those edges that have $v$ as an endpoint.
- Since each vertex in a cube is the endpoint of exactly 3 edges (one per coordinate dimension), the cardinality of this set is 3.

### Mathematical insight
This theorem formalizes a basic combinatorial property of the cube: that each vertex is incident to exactly 3 edges. This is a fundamental property of 3-dimensional cubes that follows from their structure as the Cartesian product of three line segments.

The result is part of a larger collection of theorems that characterize the combinatorial structure of regular polytopes. For a cube in 3-dimensional space, each vertex connects to exactly 3 edges because:
1. Each vertex is at the corner of the cube where three faces meet
2. Each face contributes one edge at each of its corners
3. There are three orthogonal directions in 3-dimensional space

This property generalizes to n-dimensional cubes (hypercubes), where each vertex is incident to exactly n edges.

### Dependencies
- `std_cube`: Definition of the standard cube in 3-dimensional space
- `CUBE_EDGES`: Theorem characterizing the 12 edges of the standard cube
- `CUBE_VERTICES`: Theorem characterizing the 8 vertices of the standard cube

### Porting notes
When porting this theorem to other systems:
1. Ensure that the notion of "face_of" and "aff_dim" are properly defined
2. The standard cube definition may vary between systems (some might use [0,1]³ instead of [-1,1]³)
3. The tactics used here are specific to HOL Light; other systems will need different proof approaches, though the mathematical reasoning remains the same

---

## OCTAHEDRON_EDGES_PER_VERTEX

### OCTAHEDRON_EDGES_PER_VERTEX
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- Theorem

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
For every vertex $v$ of the standard octahedron, there are exactly $4$ edges of the standard octahedron that contain $v$.

More precisely, for any set $v$ that is a face of the standard octahedron with affine dimension $0$ (i.e., a vertex), the cardinality of the set of all faces $e$ of the standard octahedron such that $e$ has affine dimension $1$ (i.e., an edge) and $v$ is a subset of $e$ is exactly $4$.

### Informal proof
The proof is completed using the tactic `EDGES_PER_VERTEX_TAC` with the standard octahedron and its characterizations of edges and vertices as arguments.

This tactic applies the following reasoning:
- For each vertex of the standard octahedron (as characterized by `OCTAHEDRON_VERTICES`), it identifies all edges (as characterized by `OCTAHEDRON_EDGES`) that contain that vertex.
- It then counts these edges for each vertex.

From the definitions of the standard octahedron's vertices and edges, we can see that:
- Each vertex is a point in 3D space with exactly one non-zero coordinate (either $1$ or $-1$)
- Each edge is a line segment connecting two vertices where exactly one coordinate changes

By examining the structure, we can verify that each vertex is contained in exactly $4$ edges, which corresponds to the $4$ possible directions in which a single coordinate can change while maintaining the constraints of the octahedron's structure.

### Mathematical insight
This theorem establishes an important combinatorial property of the octahedron: each vertex is incident to exactly $4$ edges. This is a fundamental characteristic of the octahedron as a regular polyhedron.

In general, for regular polyhedra, the number of edges meeting at each vertex is a constant. This property contributes to the overall symmetry and regularity of the polyhedron.

The octahedron is a Platonic solid with $6$ vertices, $12$ edges, and $8$ faces. This theorem confirms the local structure around each vertex, which is a key part of understanding the global structure of the polyhedron.

### Dependencies
- **Theorems**:
  - `OCTAHEDRON_EDGES`: Characterizes all edges of the standard octahedron
  - `OCTAHEDRON_VERTICES`: Characterizes all vertices of the standard octahedron
- **Definitions**:
  - `std_octahedron`: Defines the standard octahedron as the convex hull of six specific points in 3D space

### Porting notes
When porting this theorem to another system, ensure that:
1. The definition of the standard octahedron is properly transferred
2. The characterizations of edges and vertices are available
3. The system has a way to count elements in finite sets
4. The notion of "face_of" relation and affine dimension are properly defined

In systems with strong automation for geometric reasoning, the proof might be achievable through general principles about regular polyhedra rather than through direct enumeration.

---

## DODECAHEDRON_EDGES_PER_VERTEX

### DODECAHEDRON_EDGES_PER_VERTEX
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any vertex $v$ that is a face of the standard dodecahedron with affine dimension 0, the cardinality of the set of edges (faces with affine dimension 1) that contain $v$ is exactly 3.

More precisely, for any $v$ such that $v$ is a face of the standard dodecahedron and the affine dimension of $v$ is 0, the number of edges $e$ satisfying:
- $e$ is a face of the standard dodecahedron
- the affine dimension of $e$ is 1
- $v$ is a subset of $e$

is exactly 3.

### Informal proof
The proof uses a specialized tactic `EDGES_PER_VERTEX_TAC` which utilizes the previously established results about the standard dodecahedron, particularly:

- `STD_DODECAHEDRON`: The definition of the standard dodecahedron in 3D space
- `DODECAHEDRON_EDGES`: The complete enumeration of all edges of the dodecahedron
- `DODECAHEDRON_VERTICES`: The complete enumeration of all vertices of the dodecahedron

This tactic systematically checks for each vertex of the dodecahedron how many edges contain that vertex. The verification process shows that every vertex of the dodecahedron is incident to exactly 3 edges.

### Mathematical insight
This theorem establishes a fundamental property of the dodecahedron: each vertex is incident to exactly 3 edges. This is a key characteristic of the dodecahedron's combinatorial structure.

In general, a regular dodecahedron has 20 vertices, 30 edges, and 12 pentagonal faces. The theorem verifies an important aspect of this structure - the number of edges meeting at each vertex, which is constant for all vertices due to the regularity of the polyhedron.

This property is particularly important in the study of platonic solids and contributes to the verification that the standard dodecahedron construction indeed gives the expected geometric object with the correct combinatorial properties.

### Dependencies
- `STD_DODECAHEDRON`: Definition of the standard dodecahedron
- `DODECAHEDRON_EDGES`: Complete enumeration of the edges of the dodecahedron
- `DODECAHEDRON_VERTICES`: Complete enumeration of the vertices of the dodecahedron

### Porting notes
When porting this theorem to another system:
1. Ensure that the standard dodecahedron is defined in the same way, particularly with respect to its vertices in 3D space
2. The complete characterization of edges and vertices may require significant work to establish in a different proof system
3. The concept of "face of" and "affine dimension" must be properly defined
4. Instead of using the specialized tactic, the proof might need to be reconstructed by explicitly counting the edges for each vertex

---

## ICOSAHEDRON_EDGES_PER_VERTEX

### ICOSAHEDRON_EDGES_PER_VERTEX
- `ICOSAHEDRON_EDGES_PER_VERTEX`

### Type of the formal statement
- theorem

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
For any vertex $v$ of the standard icosahedron (i.e., $v$ is a face of the standard icosahedron with affine dimension 0), there are exactly 5 edges (i.e., faces with affine dimension 1) that contain this vertex.

Formally, for all sets $v$, if $v$ is a face of the standard icosahedron with affine dimension 0, then the cardinality of the set of edges $e$ such that $e$ is a face of the standard icosahedron with affine dimension 1 and $v \subseteq e$ is equal to 5.

### Informal proof
The proof uses a special tactic called `EDGES_PER_VERTEX_TAC` that is designed to count the number of edges incident to each vertex in a polyhedron. The tactic takes three arguments:

1. `STD_ICOSAHEDRON`: The definition of the standard icosahedron as a convex hull of 12 vectors in 3D space
2. `ICOSAHEDRON_EDGES`: A theorem characterizing all 30 edges of the standard icosahedron
3. `ICOSAHEDRON_VERTICES`: A theorem characterizing all 12 vertices of the standard icosahedron

The tactic systematically examines each vertex and counts the number of edges that contain it. Since a regular icosahedron has 12 vertices and 30 edges, with each vertex being incident to exactly 5 edges, the theorem is proven.

### Mathematical insight
This theorem establishes a key combinatorial property of the icosahedron: each vertex has exactly 5 edges connected to it. This is a fundamental characteristic of the icosahedron, which is one of the five Platonic solids.

The result can be derived from Euler's formula for polyhedra: $V - E + F = 2$, where $V$ is the number of vertices, $E$ is the number of edges, and $F$ is the number of faces. For a regular icosahedron:
- $V = 12$ (vertices)
- $F = 20$ (triangular faces)
- $E = 30$ (edges)

Each edge connects exactly 2 vertices, so the sum of vertex degrees equals $2E = 60$. Since the icosahedron is regular, each vertex has the same degree, so each vertex must have degree $60/12 = 5$.

This property is important in various mathematical contexts, including graph theory (where the icosahedron's skeleton is a 5-regular graph), geometric modeling, and the study of symmetry groups.

### Dependencies
- `STD_ICOSAHEDRON`: Defines the standard icosahedron as the convex hull of 12 specific points in 3D space
- `ICOSAHEDRON_EDGES`: Characterizes all 30 edges of the standard icosahedron
- `ICOSAHEDRON_VERTICES`: Characterizes all 12 vertices of the standard icosahedron
- `EDGES_PER_VERTEX_TAC`: A HOL Light tactic for proving the number of edges incident to each vertex

### Porting notes
When porting this theorem to other proof assistants:
1. First establish the definition of the standard icosahedron and prove theorems characterizing its vertices and edges
2. You'll need to create a corresponding tactic or proof strategy to the `EDGES_PER_VERTEX_TAC` in your target system
3. In systems with more advanced automation for finite sets or graphs, you might be able to prove this more directly by constructing the adjacency relation and counting

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
For any relation $R: A \to B \to \text{bool}$ and finite sets $s \subseteq A$ and $t \subseteq B$, if:
- For every $x \in s$, the number of elements $y \in t$ such that $R(x,y)$ holds is equal to $m$
- For every $y \in t$, the number of elements $x \in s$ such that $R(x,y)$ holds is equal to $n$

Then the following equality holds:
$m \cdot |s| = n \cdot |t|$

Where $|s|$ and $|t|$ denote the cardinality of sets $s$ and $t$ respectively.

### Informal proof
The proof uses a double counting argument on the relation $R$.

Let's consider the sum $\sum_{x \in s}\sum_{y \in t} [R(x,y)]$ where $[R(x,y)]$ equals 1 if $R(x,y)$ holds and 0 otherwise.

We can compute this sum in two ways:
- First, for each $x \in s$, we sum over all $y \in t$ such that $R(x,y)$ holds. By the first assumption, there are exactly $m$ such $y$ values for each $x$. So the total sum is $m \cdot |s|$.
- Second, for each $y \in t$, we sum over all $x \in s$ such that $R(x,y)$ holds. By the second assumption, there are exactly $n$ such $x$ values for each $y$. So the total sum is $n \cdot |t|$.

Since these two calculations count the same quantity, we must have $m \cdot |s| = n \cdot |t|$.

In the formal proof, this double counting is implemented using `NSUM_NSUM_RESTRICT` with the constant function $\lambda x. \lambda y. 1$, which computes the number of pairs $(x,y)$ where $R(x,y)$ holds.

### Mathematical insight
This theorem formalizes a fundamental double counting principle that appears throughout combinatorics. It's particularly useful in graph theory (for bipartite graphs) and in counting arguments involving relations.

The lemma can be interpreted as a conservation law: the total number of relationships between elements must be consistent regardless of how we count them. If we count from the perspective of elements in $s$, we get $m \cdot |s|$ relationships. If we count from the perspective of elements in $t$, we get $n \cdot |t|$ relationships. These must be equal.

This result is related to the handshaking lemma in graph theory and can be used to prove many combinatorial identities and constraints.

### Dependencies
- `NSUM_NSUM_RESTRICT`: A theorem for manipulating double sums with restrictions
- `NSUM_CONST`: A theorem for computing the sum of a constant function
- `FINITE_RESTRICT`: A theorem establishing that a restriction of a finite set is finite

### Porting notes
When porting this to other systems:
- Ensure the target system has appropriate library support for finite sets and cardinality operations.
- Double counting arguments like this are common in many mathematical libraries, so similar theorems might already exist.
- The proof is relatively straightforward and should port easily to systems with basic arithmetic and sum manipulation capabilities.

---

## SIZE_ZERO_DIMENSIONAL_FACES

### SIZE_ZERO_DIMENSIONAL_FACES
- STATE_ZERO_DIMENSIONAL_FACES

### Type of the formal statement
- theorem

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
For any polyhedron $s$ in $\mathbb{R}^N$, the following statements hold:
1. The cardinality of the set of 0-dimensional faces of $s$ equals the cardinality of the set of extreme points of $s$:
   $$|\\{f \mid f \text{ face_of } s \land \text{aff_dim}(f) = 0\\}| = |\\{v \mid v \text{ extreme_point_of } s\\}|$$
2. The set of 0-dimensional faces of $s$ is finite if and only if the set of extreme points of $s$ is finite:
   $$\text{FINITE}\\{f \mid f \text{ face_of } s \land \text{aff_dim}(f) = 0\\} \Leftrightarrow \text{FINITE}\\{v \mid v \text{ extreme_point_of } s\\}$$
3. For any natural number $n$, the set of 0-dimensional faces of $s$ has size $n$ if and only if the set of extreme points of $s$ has size $n$:
   $$\forall n.\ \\{f \mid f \text{ face_of } s \land \text{aff_dim}(f) = 0\\} \text{ HAS_SIZE } n \Leftrightarrow \\{v \mid v \text{ extreme_point_of } s\\} \text{ HAS_SIZE } n$$

### Informal proof
The proof establishes a bijection between the sets of 0-dimensional faces and extreme points of a polyhedron.

First, we prove that the set of 0-dimensional faces of $s$ equals the image of the set of extreme points of $s$ under the function that maps each point $v$ to the singleton set $\{v\}$:

$$\{f \mid f \text{ face_of } s \land \text{aff_dim}(f) = 0\} = \{\{v\} \mid v \text{ extreme_point_of } s\}$$

This holds because:
- A singleton set $\{v\}$ is a face of $s$ if and only if $v$ is an extreme point of $s$
- The affine dimension of any singleton $\{v\}$ is 0

With this bijection established, we can prove the three main claims:

1. For the cardinality equality, we use the fact that the function $v \mapsto \{v\}$ is injective (one-to-one), so the cardinality of the image equals the cardinality of the domain.

2. The finiteness equivalence follows directly from the bijection and the property that a set is finite if and only if its image under an injective function is finite.

3. Similarly, for any size $n$, a set has size $n$ if and only if its image under an injective function has size $n$.

### Mathematical insight
This theorem establishes the fundamental correspondence between 0-dimensional faces and extreme points of a polyhedron. In the theory of polyhedra, the extreme points are precisely those that cannot be expressed as a proper convex combination of other points in the polyhedron.

The theorem formally confirms the intuitive idea that 0-dimensional faces are exactly the singletons containing extreme points. This is important because:
1. It connects two different characterizations of the "corners" of a polyhedron
2. It allows properties of extreme points to be derived from properties of faces, and vice versa
3. It serves as the base case for the hierarchy of faces of a polyhedron, which includes 1-dimensional faces (edges), 2-dimensional faces, and so on

This result is a key component in the combinatorial theory of polyhedra, laying groundwork for results like the Euler-Poincaré formula.

### Dependencies
- `FACE_OF_SING`: Characterizes when a singleton is a face of a set
- `AFF_DIM_SING`: States that the affine dimension of a singleton is 0
- `AFF_DIM_EQ_0`: Characterizes sets of affine dimension 0
- `FINITE_POLYHEDRON_EXTREME_POINTS`: States that the set of extreme points of a polyhedron is finite
- `CARD_IMAGE_INJ`: Relates the cardinality of a set and its image under an injective function
- `FINITE_IMAGE_INJ_EQ`: Relates the finiteness of a set and its image under an injective function
- `HAS_SIZE_IMAGE_INJ_EQ`: Relates the size of a set and its image under an injective function
- `SURJECTIVE_IMAGE_EQ`: Characterizes when two sets have the same image under a function

### Porting notes
When porting this theorem:
- Ensure that the definition of `face_of`, `extreme_point_of`, and `aff_dim` are consistent with HOL Light
- Verify that the target system has appropriate theorems about the relationship between singleton sets and extreme points
- Check that the target system has the necessary machinery for handling cardinality and finiteness of sets

---

## PLATONIC_SOLIDS_LIMITS

### PLATONIC_SOLIDS_LIMITS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem characterizes the five Platonic solids by establishing constraints on the number of edges in each face and the number of edges meeting at each vertex.

For any polytope $p$ in $\mathbb{R}^3$ with affine dimension 3:
- Let $m$ be the constant number of edges in each face (where faces are 2-dimensional)
- Let $n$ be the constant number of edges meeting at each vertex (where vertices are 0-dimensional)

Then, the only possible values of $(m,n)$ are:
1. $m = 3$ and $n = 3$ (Tetrahedron)
2. $m = 4$ and $n = 3$ (Cube)
3. $m = 3$ and $n = 4$ (Octahedron)
4. $m = 5$ and $n = 3$ (Dodecahedron)
5. $m = 3$ and $n = 5$ (Icosahedron)

### Informal proof
The proof uses Euler's formula for polyhedra and combinatorial constraints to show that only these five configurations are possible.

1. First, let $V$, $E$, and $F$ denote the number of vertices, edges, and faces of the polytope, respectively.

2. We apply Euler's relation ($V + F - E = 2$) to the polytope $p$.

3. We establish two key counting identities:
   - $m \cdot F = 2E$ (each face has $m$ edges, but each edge is counted twice)
   - $n \cdot V = 2E$ (each vertex connects to $n$ edges, but each edge is counted twice)
   
   These are proven using the `MULTIPLE_COUNTING_LEMMA`, which formalizes double counting arguments.

4. From these equations we can determine that $V + F = E + 2$.

5. We note that any polytope in 3D space must have at least 4 vertices and at least 4 faces.

6. From $V + F = E + 2$ and the minimum conditions, we derive that $E \geq 6$.

7. We establish that $m \geq 3$, since any face must have at least 3 edges to be two-dimensional.

8. We also establish that $n \geq 3$, as a vertex must connect to at least 3 edges to form a proper 3D polytope.

9. From the equations $m \cdot F = 2E$ and $n \cdot V = 2E$, we derive:
   $2E \cdot (m + n) = mn \cdot (V + F) = mn \cdot (E + 2)$

10. This simplifies to: $E \cdot 2(m + n) = mn \cdot (E + 2)$

11. Since $E > 0$, we get: $2(m + n) = mn \cdot (1 + \frac{2}{E})$

12. As $E \geq 6$, we have $1 + \frac{2}{E} \leq \frac{4}{3}$, so $2(m + n) < \frac{4}{3}mn$

13. Rearranging: $(m-2)(n-2) < 4$

14. Since $m, n \geq 3$, we have $m, n \leq 5$

15. Testing all possible combinations of $3 \leq m \leq 5$ and $3 \leq n \leq 5$ against the equation derived in step 10, we find that only the five listed configurations satisfy the constraints.

### Mathematical insight
This theorem provides a rigorous proof of the classical result that there are exactly five Platonic solids (regular polyhedra). The result dates back to Euclid's Elements, but this formulation links it directly to constraints on the structure of vertices and faces.

The key insight is that Euler's formula combined with the regularity conditions (fixed number of edges per face and fixed number of edges per vertex) creates tight constraints that admit only five solutions. Each solution corresponds to one of the Platonic solids:
- Tetrahedron: triangular faces, 3 faces meet at each vertex
- Cube: square faces, 3 faces meet at each vertex
- Octahedron: triangular faces, 4 faces meet at each vertex
- Dodecahedron: pentagonal faces, 3 faces meet at each vertex
- Icosahedron: triangular faces, 5 faces meet at each vertex

This result demonstrates the deep connection between combinatorial properties and geometric structures in three dimensions.

### Dependencies
- `EULER_RELATION`: Euler's formula for polytopes stating that for a 3D polytope, $V + F - E = 2$
- `MULTIPLE_COUNTING_LEMMA`: A general theorem formalizing double counting arguments
- `SIZE_ZERO_DIMENSIONAL_FACES`: Relates zero-dimensional faces of a polyhedron to its extreme points

### Porting notes
This theorem requires a well-developed theory of polyhedra, affine spaces, and combinatorics. When porting:
1. Ensure that the definitions of polytope, face, and affine dimension match across systems
2. The proof relies heavily on combinatorial reasoning and counting arguments, which may need different approaches in systems with different libraries for finite sets
3. The handling of real arithmetic may require different tactics in other systems

---

## PLATONIC_SOLIDS

### PLATONIC_SOLIDS

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
The theorem states that there exist exactly five types of regular polyhedra in 3-dimensional space (the Platonic solids). Specifically, for natural numbers $m$ and $n$, there exists a 3-dimensional polytope $p$ where:
- Each face of $p$ has exactly $m$ edges
- Each vertex of $p$ has exactly $n$ edges meeting at it

if and only if $(m,n)$ is one of the following five pairs:
1. $(3,3)$ - Tetrahedron
2. $(4,3)$ - Cube
3. $(3,4)$ - Octahedron
4. $(5,3)$ - Dodecahedron
5. $(3,5)$ - Icosahedron

More formally, the existence of a polyhedron $p \subset \mathbb{R}^3$ with the following properties:
- $p$ is a polytope with affine dimension 3
- For every face $f$ of $p$ with affine dimension 2, the cardinality of the set of edges $e$ of $p$ that are contained in $f$ is $m$
- For every vertex $v$ of $p$, the cardinality of the set of edges $e$ of $p$ that contain $v$ is $n$

is equivalent to $(m,n)$ being one of the five pairs listed above.

### Informal proof
The proof establishes both directions of the if-and-only-if statement:

**Forward direction**: If such a polytope exists, then $(m,n)$ must be one of the five pairs.

This direction relies on the theorem `PLATONIC_SOLIDS_LIMITS`, which proves that any polytope satisfying the given regularity conditions must have the parameters $(m,n)$ from our list of five pairs. This leverages Euler's polyhedron formula and properties of convex polyhedra.

**Backward direction**: For each of the five pairs $(m,n)$, there exists a polytope with the specified properties.

For each case, we explicitly construct a standard representation of the corresponding Platonic solid:

1. For $(3,3)$ - We use the standard tetrahedron.
   - We verify that it's a polytope using `POLYTOPE_CONVEX_HULL`
   - `TETRAHEDRON_EDGES_PER_FACE` confirms it has 3 edges per face
   - `TETRAHEDRON_EDGES_PER_VERTEX` confirms it has 3 edges per vertex
   - `STD_TETRAHEDRON_FULLDIM` confirms it has dimension 3

2. For $(4,3)$ - We use the standard cube with similar verification.

3. For $(3,4)$ - We use the standard octahedron with similar verification.

4. For $(5,3)$ - We use the standard dodecahedron with similar verification.

5. For $(3,5)$ - We use the standard icosahedron with similar verification.

Each verification uses the corresponding theorems about edges per face, edges per vertex, and affine dimension.

### Mathematical insight
This theorem provides a complete characterization of the Platonic solids, which are the only possible regular convex polyhedra in 3-dimensional Euclidean space.

The existence of exactly five Platonic solids was known to ancient Greek mathematicians and was proven in Euclid's Elements. The proof relies on the topological constraints imposed by Euler's formula for polyhedra ($V - E + F = 2$) combined with the regularity conditions.

The five Platonic solids have remarkable symmetry properties and appear in various contexts in mathematics, crystallography, and other sciences. They are:
1. Tetrahedron (4 triangular faces)
2. Cube (6 square faces)
3. Octahedron (8 triangular faces)
4. Dodecahedron (12 pentagonal faces)
5. Icosahedron (20 triangular faces)

This theorem is fundamental in the study of regular polyhedra and demonstrates that regularity in 3D space is highly constrained, leading to just five possibilities.

### Dependencies
- **Theorems and properties about standard Platonic solids**:
  - `PLATONIC_SOLIDS_LIMITS`: Proves that only the five Platonic solids can exist
  - `STD_TETRAHEDRON_FULLDIM`, `STD_CUBE_FULLDIM`, etc.: Verify the dimensionality
  - `TETRAHEDRON_EDGES_PER_FACE`, `CUBE_EDGES_PER_FACE`, etc.: Count edges per face
  - `TETRAHEDRON_EDGES_PER_VERTEX`, `CUBE_EDGES_PER_VERTEX`, etc.: Count edges per vertex
  - `STD_DODECAHEDRON`, `STD_ICOSAHEDRON`: Descriptions of the dodecahedron and icosahedron

- **Definitions**:
  - `std_tetrahedron`, `std_cube`, `std_octahedron`, `std_dodecahedron`, `std_icosahedron`: Standard constructions of the Platonic solids

- **General polyhedron theory**:
  - `POLYTOPE_CONVEX_HULL`: Shows that the convex hull of a finite set is a polytope

### Porting notes
When porting this theorem:

1. You'll need to implement standard constructions of all five Platonic solids. For the dodecahedron and icosahedron, these involve the golden ratio $\phi = \frac{1 + \sqrt{5}}{2}$.

2. Ensure your system can handle the following key concepts:
   - Affine dimension
   - Faces, edges, and vertices of polyhedra
   - Euler's formula for polyhedra
   - Convex hulls

3. The proof of `PLATONIC_SOLIDS_LIMITS` is likely the most complex part to port, as it involves careful counting and application of Euler's formula.

4. Consider using a more direct approach if your target system has built-in support for polyhedra or graph theory, as Platonic solids can be characterized by their symmetry groups or as regular graphs embedded on a sphere.

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
Two sets $s$ and $t$ in $\mathbb{R}^N$ are congruent, denoted as $s \cong t$, if and only if there exists a vector $c \in \mathbb{R}^N$ and an orthogonal transformation $f$ such that $t = \{c + f(x) \mid x \in s\}$.

In other words, two sets are congruent if one can be obtained from the other by a rigid motion consisting of a rotation and/or reflection (captured by the orthogonal transformation) followed by a translation.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
The concept of congruence captures the geometric notion of "same shape and size" in Euclidean geometry. Two geometric objects are congruent precisely when one can be transformed into the other using an isometry (distance-preserving transformation).

In this formalization, the isometry is explicitly constructed as a composition of:
1. An orthogonal transformation (rotation and/or reflection) that preserves angles and distances
2. A translation by vector $c$

This is a fundamental concept in geometry, as it characterizes when two figures can be considered "the same" in terms of their intrinsic geometric properties, independent of their position and orientation in space.

### Dependencies
#### Definitions
- `orthogonal_transformation` (presumably defines a linear transformation that preserves the inner product)

### Porting notes
When porting this definition to other proof assistants:
- Ensure the target system has a notion of orthogonal transformations or isometries
- You might need to represent the image of a set under a function (IMAGE in HOL Light)
- Some systems might prefer alternative but equivalent formulations of congruence, such as preservation of distances between corresponding points

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
If there exists an orthogonal matrix $A \in \mathbb{R}^{3 \times 3}$ such that $t = \{Ax \mid x \in s\}$ where $s, t \subset \mathbb{R}^3$, then the convex hull of $s$ is congruent to the convex hull of $t$.

Here, two sets $X$ and $Y$ are congruent if there exists a vector $c$ and an orthogonal transformation $f$ such that $Y = \{c + f(x) \mid x \in X\}$.

### Informal proof
We start with the assumption that there exists an orthogonal matrix $A$ such that $t = \{A \cdot x \mid x \in s\}$.

First, we observe that the convex hull commutes with linear transformations, so:
$\text{convex hull}(t) = \text{convex hull}(\{A \cdot x \mid x \in s\}) = \{A \cdot x \mid x \in \text{convex hull}(s)\}$

Now, to prove congruence, we need to find a vector $c$ and an orthogonal transformation $f$ satisfying the definition. We choose:
- $c = \vec{0} \in \mathbb{R}^3$
- $f(x) = A \cdot x$ for all $x \in \mathbb{R}^3$

Since $A$ is an orthogonal matrix, the function $f(x) = A \cdot x$ is an orthogonal transformation. With $c = \vec{0}$, we have:
$\{c + f(x) \mid x \in \text{convex hull}(s)\} = \{A \cdot x \mid x \in \text{convex hull}(s)\} = \text{convex hull}(t)$

Therefore, the convex hulls of $s$ and $t$ are congruent.

### Mathematical insight
This theorem establishes that when two sets in $\mathbb{R}^3$ are related by an orthogonal transformation (a rotation or reflection), their convex hulls are congruent. This is intuitive because orthogonal transformations preserve distances and angles, and adding a translation (although in this specific case, we used a zero translation) preserves the shape as well.

Congruence is an important geometric concept capturing the idea that shapes have the same size and form, just potentially different orientations and positions in space. This theorem shows that convex hulls preserve congruence relationships between sets.

### Dependencies
- **Definitions**:
  - `congruent`: Two sets are congruent if one can be mapped to the other by an orthogonal transformation followed by a translation.

- **Theorems**:
  - `CONVEX_HULL_LINEAR_IMAGE`: The convex hull commutes with linear transformations.
  - `MATRIX_VECTOR_MUL_LINEAR`: Matrix-vector multiplication is a linear transformation.
  - `ORTHOGONAL_TRANSFORMATION_MATRIX`: Characterizes orthogonal transformations as those representable by orthogonal matrices.
  - `MATRIX_OF_MATRIX_VECTOR_MUL`: Relates matrix representation to function application for matrix-vector multiplication.

### Porting notes
When porting this theorem:
1. Ensure your target system has a definition of congruence between sets that matches HOL Light's definition.
2. Verify that linear algebra fundamentals like orthogonal matrices and transformations are properly defined.
3. The proof relies on properties of convex hulls and linear transformations, which should be available in most formal systems with a mathematical library.
4. The specific case deals with $\mathbb{R}^3$, but the result could likely be generalized to arbitrary dimensions with similar proof structure.

---

## CONGRUENT_SEGMENTS

### CONGRUENT_SEGMENTS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any points $a, b, c, d$ in $\mathbb{R}^N$, if $\operatorname{dist}(a,b) = \operatorname{dist}(c,d)$, then the line segment $[a,b]$ is congruent to the line segment $[c,d]$.

Here, two sets $s$ and $t$ are congruent if there exists a vector $c$ and an orthogonal transformation $f$ such that $t = \{c + f(x) \mid x \in s\}$, which means $t$ can be obtained from $s$ by a rigid motion (a composition of a translation and an orthogonal transformation).

### Informal proof
We need to show that if two line segments have the same length, then they are congruent.

1. Given points $a, b, c, d \in \mathbb{R}^N$ with $\operatorname{dist}(a,b) = \operatorname{dist}(c,d)$.

2. First, we observe that $\|b - a\| = \|d - c\|$ (since the distance between points equals the norm of their difference).

3. By the theorem `ORTHOGONAL_TRANSFORMATION_EXISTS`, since $\|b - a\| = \|d - c\|$, there exists an orthogonal transformation $f$ such that $f(b - a) = d - c$.

4. To show that the segments are congruent, we need to find a vector $c'$ and an orthogonal transformation $f$ such that $\operatorname{segment}[c,d] = \{c' + f(x) \mid x \in \operatorname{segment}[a,b]\}$.

5. We choose $c' = c - f(a)$ and use the previously obtained orthogonal transformation $f$.

6. Since $f$ is linear (as all orthogonal transformations are), we can rewrite the mapping $x \mapsto c' + f(x)$ as the composition $(x \mapsto c' + x) \circ f$.

7. Using properties of images under linear transformations and translations:
   - $\operatorname{segment}[a,b]$ can be expressed as the convex hull $\operatorname{conv}\{a,b\}$
   - The image of a convex hull under a linear map is the convex hull of the images
   - The image of a convex hull under a translation is the convex hull of the translated points

8. We need to verify that $f(a) = c$ and $f(b) = d$, which follows from $f(b) - f(a) = f(b-a) = d-c$ and the fact that $f(a) = c$ by our choice of $c'$.

9. Therefore, $\operatorname{segment}[a,b]$ is congruent to $\operatorname{segment}[c,d]$.

### Mathematical insight
This theorem establishes a fundamental property in Euclidean geometry: two line segments are congruent if and only if they have the same length. The proof constructs an explicit rigid motion (a composition of a translation and an orthogonal transformation) that maps one segment to the other.

The key insight is that we can always find an orthogonal transformation that maps one direction vector to another of the same length, and then we can use a translation to align the starting points. This is essentially how congruence works in Euclidean geometry - through rigid motions that preserve distances.

This result is important because it forms the basis for more complex congruence results in Euclidean geometry, such as the congruence of triangles, polygons, and other geometric figures.

### Dependencies
- Definitions:
  - `congruent`: Two sets are congruent if one can be obtained from the other by an orthogonal transformation followed by a translation
  - `segment`: Represents a line segment between two points
  - `dist`: Euclidean distance between points

- Theorems:
  - `ORTHOGONAL_TRANSFORMATION_EXISTS`: For vectors of equal norm, there exists an orthogonal transformation mapping one to the other
  - `ORTHOGONAL_TRANSFORMATION_LINEAR`: Orthogonal transformations are linear maps
  - `CONVEX_HULL_LINEAR_IMAGE`: The image of a convex hull under a linear map is the convex hull of the images
  - `SEGMENT_CONVEX_HULL`: A line segment is the convex hull of its endpoints
  - `CONVEX_HULL_TRANSLATION`: The convex hull of translated points is the translation of the convex hull

### Porting notes
When porting this theorem:
1. Ensure that your system has a suitable definition of orthogonal transformations (isometries that fix the origin)
2. The proof relies on the existence of an orthogonal transformation between vectors of equal norm, which may need to be proven separately
3. The handling of the composition of functions and operations on convex hulls might vary between systems
4. Vector arithmetic tactics like `VECTOR_ARITH_TAC` might need different implementations in other systems

---

## compute_dist

### Name of formal statement
compute_dist

### Type of the formal statement
function definition

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
`compute_dist` is a function that computes the squared Euclidean distance between two 3D vectors in $\mathbb{R}^3$. Given two vectors $v_1$ and $v_2$ in $\mathbb{R}^3$, it calculates $(v_1 - v_2) \cdot (v_1 - v_2)$, which represents the square of the Euclidean distance between these vectors.

### Informal proof
This is a function definition that performs the computation through the following steps:

1. It first defines local terms for vector subtraction (`mk_sub`) and the dot product (`dot_tm`).
2. Given two vectors $v_1$ and $v_2$ in $\mathbb{R}^3$, it:
   - Computes $v_1 - v_2$ using `VECTOR3_SUB_CONV`
   - Applies the dot product to this result: $(v_1 - v_2) \cdot (v_1 - v_2)$ using `VECTOR3_DOT_CONV`
   - Returns the right-hand side of the resulting theorem, which will be the numeric value of the squared distance

The function leverages the conversion theorems `VECTOR3_SUB_CONV` and `VECTOR3_DOT_CONV` to perform symbolic computation of vector operations for 3D vectors.

### Mathematical insight
The function implements the standard formula for the squared Euclidean distance between two points in 3D space. This is a frequently used calculation in computational geometry, computer graphics, and physics simulations.

The implementation is designed for efficient symbolic computation of this distance within the HOL Light theorem prover. By using conversion theorems that understand the structure of 3D vectors, it can compute exact values when the vector components are numeric.

Note that this function returns the squared distance rather than the distance itself (which would involve a square root). Working with squared distances is often preferable in computational settings to avoid unnecessary square root operations when comparing distances.

### Dependencies
- **Theorems**:
  - `VECTOR3_SUB_CONV`: Conversion for computing the subtraction of two 3D vectors
  - `VECTOR3_DOT_CONV`: Conversion for computing the dot product of two 3D vectors

### Porting notes
When porting this function to other proof assistants:
- The implementation details will likely differ significantly based on how the target system handles conversions and symbolic computation.
- In systems with more advanced computation capabilities (like Lean's norm_num tactics or Isabelle's code_simp), a more direct implementation might be possible.
- The function assumes vectors in $\mathbb{R}^3$ with a specific representation. Ensure the target system has an equivalent way to represent and operate on such vectors.

---

## le_rat5

### le_rat5
- `le_rat5`

### Type of the formal statement
- new_definition (function definition)

### Formal Content
```ocaml
let le_rat5 =
  let mk_le = mk_binop `(<=):real->real->bool` and t_tm = `T` in
  fun r1 r2 -> rand(concl(REAL_RAT5_LE_CONV(mk_le r1 r2))) = t_tm;;
```

### Informal statement
This defines a function `le_rat5` that compares two real numbers in the quadratic field $\mathbb{Q}[\sqrt{5}]$. The function takes two real expressions `r1` and `r2` and returns a boolean value indicating whether `r1 ≤ r2`.

Specifically, `le_rat5 r1 r2` evaluates to `true` if and only if `r1 ≤ r2`, where the comparison is performed by applying the conversion `REAL_RAT5_LE_CONV` to the expression `r1 <= r2` and checking if the result is equal to the term `T` (true).

### Informal proof
This is a function definition rather than a theorem, so it does not have a proof. The function works by:

1. Creating a less-than-or-equal comparison expression `r1 <= r2` using `mk_le`
2. Applying the conversion `REAL_RAT5_LE_CONV` to this expression
3. Extracting the right-hand side of the conclusion (using `rand` and `concl`)
4. Checking if this right-hand side equals the term `T` (true)

### Mathematical insight
This function provides a computational implementation for comparing numbers in $\mathbb{Q}[\sqrt{5}]$, which is the field of numbers of the form $a + b\sqrt{5}$ where $a$ and $b$ are rational numbers. 

The implementation relies on the conversion `REAL_RAT5_LE_CONV`, which transforms expressions of the form `a1 + b1 * sqrt(5) <= a2 + b2 * sqrt(5)` into an equivalent boolean expression according to the specific criteria for comparing numbers in this quadratic field.

This function is likely used in the formalization of mathematical results involving the golden ratio or Fibonacci numbers, both of which have strong connections to $\sqrt{5}$.

### Dependencies
- Conversions:
  - `REAL_RAT5_LE_CONV`: Conversion for less-than-or-equal comparisons of real numbers involving $\sqrt{5}$

### Porting notes
When porting this to another system:
- You'll need to implement the equivalent of `REAL_RAT5_LE_CONV` or use the target system's library for comparing numbers in quadratic fields
- Consider whether the target system has built-in support for algebraic numbers or needs explicit representation
- Many systems may have more direct ways to represent and compare elements of $\mathbb{Q}[\sqrt{5}]$

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
Given a non-empty list of points `s`, the function `three_adjacent_points` returns a triple of points `(x, y, z)` such that:
- `x` is the first point in the input list
- `y` is the point in the remaining list that is closest to `x`
- `z` is the second closest point to `x` from the remaining list

If the input list has fewer than 3 elements, the function fails with the error message "three_adjacent_points: no points".

### Informal proof
This is a definition, not a theorem, so it does not have a proof.

### Mathematical insight
This function identifies three key points from a set: a reference point and its two nearest neighbors. This is useful in computational geometry, particularly for algorithms that need to identify proximate points, such as in triangulation, clustering, or nearest neighbor problems.

The implementation:
1. Takes the first point `x` from the list
2. For each remaining point `y` in the list, computes the distance between `x` and `y`
3. Sorts these distances in ascending order
4. Returns the triple consisting of the original point `x`, and the two points that are closest to it

This function is particularly useful when working with point sets where proximity relationships are important.

### Dependencies
No explicit dependencies are listed, but the implementation uses:
- `sort` - Function to sort a list given a comparison function
- `le_rat5` - Likely a predicate for comparing rational numbers
- `compute_dist` - Function to compute distance between two points
- Standard list operations: `map`, pattern matching

### Porting notes
When porting this definition:
1. Ensure the target system has appropriate functions for sorting lists and computing distances between points
2. Check how the target system handles pattern matching, particularly for lists
3. Consider how error handling is implemented in the target system, as this function uses `failwith` for invalid inputs
4. Check if the target system requires explicit type annotations for points and distances

---

## mk_33matrix

### Name of formal statement
mk_33matrix

### Type of the formal statement
Function definition

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
`mk_33matrix` is a function that constructs a $3 \times 3$ matrix as a vector of row vectors in HOL Light. The function takes a list of 9 real numbers and returns a term representing a $3 \times 3$ matrix of type `real^3^3`, where each row is a vector of 3 real numbers.

Specifically, given a list of real values $[a_{11}, a_{12}, a_{13}, a_{21}, a_{22}, a_{23}, a_{31}, a_{32}, a_{33}]$, the function creates a matrix:

$$\begin{pmatrix}
a_{11} & a_{12} & a_{13} \\
a_{21} & a_{22} & a_{23} \\
a_{31} & a_{32} & a_{33}
\end{pmatrix}$$

represented as a vector of row vectors in HOL Light:

$$\text{vector}[\text{vector}[a_{11}; a_{12}; a_{13}]; \text{vector}[a_{21}; a_{22}; a_{23}]; \text{vector}[a_{31}; a_{32}; a_{33}]]$$

### Informal proof
This is a function definition rather than a theorem, so there is no proof. The function works by:

1. Creating term templates for each matrix element (`a11_tm`, `a12_tm`, etc.) as real-valued variables.
2. Defining a pattern term `pat_tm` that represents the structure of a $3 \times 3$ matrix as a vector of row vectors.
3. The function itself takes a list of 9 real values and substitutes them into the corresponding positions in the pattern, creating a concrete matrix term.

The substitution is performed using the `vsubst` function, which replaces each template term with its corresponding actual value.

### Mathematical insight
This function serves as a utility for constructing $3 \times 3$ matrices in HOL Light's term language. In HOL Light, matrices are represented as vectors of row vectors, and this function provides a convenient way to create such matrices from a list of elements.

The function is particularly useful when working with $3 \times 3$ matrices in geometric applications, such as 3D transformations, rotations, or when dealing with systems of linear equations in three variables. It abstracts away the nested vector structure that HOL Light uses for matrices, providing a more natural interface.

### Dependencies
This function uses HOL Light's term manipulation functions:
- `vsubst`: For substituting terms within a pattern

### Porting notes
When porting this to other proof assistants, consider:

1. Different systems may have different ways of representing matrices. For example:
   - Some might use native matrix types
   - Others might use functions from indices to values
   - Others might use nested lists or arrays

2. This function is primarily a syntactic convenience for HOL Light's specific term representation. In systems with more direct matrix support, similar functions might be simpler or unnecessary.

3. In systems with dependent types or more sophisticated type systems, a more generic matrix constructor might be preferable over one specific to $3 \times 3$ matrices.

---

## MATRIX_VECTOR_MUL_3

### MATRIX_VECTOR_MUL_3
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem states that for a $3 \times 3$ matrix $A$ and a $3$-dimensional vector $\vec{x}$, the matrix-vector multiplication $A\vec{x}$ can be calculated explicitly as follows:

$$
\begin{pmatrix} 
a_{11} & a_{12} & a_{13} \\
a_{21} & a_{22} & a_{23} \\
a_{31} & a_{32} & a_{33}
\end{pmatrix}
\begin{pmatrix} 
x_1 \\
x_2 \\
x_3
\end{pmatrix}
=
\begin{pmatrix} 
a_{11}x_1 + a_{12}x_2 + a_{13}x_3 \\
a_{21}x_1 + a_{22}x_2 + a_{23}x_3 \\
a_{31}x_1 + a_{32}x_2 + a_{33}x_3
\end{pmatrix}
$$

Where the matrix is represented as a vector of row vectors in HOL Light.

### Informal proof
The proof is straightforward and consists of the following steps:

1. First, we use `SIMP_TAC[CART_EQ; matrix_vector_mul; LAMBDA_BETA]` which:
   - Applies `CART_EQ` to reduce equality of vectors to componentwise equality
   - Uses the definition of `matrix_vector_mul` which computes matrix-vector multiplication
   - Applies beta-reduction with `LAMBDA_BETA` to simplify lambda expressions

2. Then, `REWRITE_TAC[DIMINDEX_3; FORALL_3; SUM_3; VECTOR_3]` explicitly:
   - Substitutes the fact that the dimension is 3 using `DIMINDEX_3`
   - Expands universal quantification over 3-dimensional vectors with `FORALL_3`
   - Expands the sum notation for a 3-term summation with `SUM_3`
   - Applies the explicit representation of 3D vectors with `VECTOR_3`

This combination of tactics computes the explicit formula for multiplying a 3×3 matrix with a 3D vector.

### Mathematical insight
This theorem provides an explicit computation formula for matrix-vector multiplication in the specific case of a 3×3 matrix and a 3-dimensional vector. While the general definition of matrix-vector multiplication is well-known, having explicit formulas for fixed dimensions can be useful for practical applications and verification.

This result is a special case of the general matrix-vector multiplication, which is defined as:
$$
(A\vec{x})_i = \sum_{j=1}^{n} a_{ij}x_j
$$

The theorem gives the concrete calculation for the 3×3 case, which is particularly useful in 3D geometry, computer graphics, and physics applications.

### Dependencies
The proof relies on several HOL Light theorems:
- `CART_EQ`: Equality of vectors based on componentwise equality
- `matrix_vector_mul`: The definition of matrix-vector multiplication
- `LAMBDA_BETA`: Beta reduction for lambda expressions
- `DIMINDEX_3`: The dimensionality constant for 3D vectors
- `FORALL_3`: Universal quantification over 3D vectors
- `SUM_3`: Summation over 3 terms
- `VECTOR_3`: Explicit representation of 3D vectors

### Porting notes
When porting to another system:
- Ensure that the target system has a similar representation for matrices (as vectors of row vectors)
- Check how the target system handles component access in vectors and matrices
- The proof is mostly computational, so automation for this type of calculation might differ across systems
- In some systems, this might be provable with a single simplification step or computation tactic

---

## MATRIX_LEMMA

### MATRIX_LEMMA

### Type of the formal statement
- theorem

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
For any matrix $A \in \mathbb{R}^{3 \times 3}$ and vectors $x_1, y_1, z_1, x_2, y_2, z_2 \in \mathbb{R}^3$, the following statements are equivalent:

$$A \cdot x_1 = x_2 \text{ and } A \cdot y_1 = y_2 \text{ and } A \cdot z_1 = z_2$$

if and only if

$$\begin{align}
\begin{pmatrix} x_1 \\ y_1 \\ z_1 \end{pmatrix} \cdot \text{row}_1(A) &= \begin{pmatrix} (x_2)_1 \\ (y_2)_1 \\ (z_2)_1 \end{pmatrix} \\
\begin{pmatrix} x_1 \\ y_1 \\ z_1 \end{pmatrix} \cdot \text{row}_2(A) &= \begin{pmatrix} (x_2)_2 \\ (y_2)_2 \\ (z_2)_2 \end{pmatrix} \\
\begin{pmatrix} x_1 \\ y_1 \\ z_1 \end{pmatrix} \cdot \text{row}_3(A) &= \begin{pmatrix} (x_2)_3 \\ (y_2)_3 \\ (z_2)_3 \end{pmatrix}
\end{align}$$

where $(v)_i$ represents the $i$-th component of vector $v$, and $\text{row}_i(A)$ represents the $i$-th row of matrix $A$.

### Informal proof
The proof proceeds by simplifying both sides of the equivalence and showing they are equivalent:

1. First, we apply `CART_EQ` to ensure vector equality is treated component-wise.
2. Apply `transp`, `matrix_vector_mul`, and `row` to expand the matrix-vector multiplication operations.
3. Use `VECTOR_3` and `LAMBDA_BETA` to handle the specific vector dimensions and evaluate lambda expressions.
4. Apply `FORALL_3` and `DIMINDEX_3` to handle the 3D case specifically.
5. Use `SUM_3` to expand the summations in the matrix-vector multiplications.
6. Finally, `REAL_ARITH_TAC` completes the proof by showing that the resulting arithmetic expressions are equivalent.

The essence of the proof is showing that the matrix-vector multiplications on the left side expand to the same component-wise equations as expressed on the right side, which follows directly from the definition of matrix-vector multiplication.

### Mathematical insight
This lemma establishes an alternative way to view matrix-vector multiplication in $\mathbb{R}^3$. Specifically:

- The left side represents three separate matrix-vector products with the same matrix $A$ applied to different vectors $x_1$, $y_1$, and $z_1$.
- The right side reformulates this in terms of dot products between rows of $A$ and a matrix whose columns are $x_1$, $y_1$, and $z_1$.

This reformulation is useful when analyzing linear transformations in 3D space, particularly when considering how a matrix transforms multiple vectors simultaneously. It essentially provides a "transposed" view of the same operation, which can simplify certain proofs and computations in linear algebra, especially those involving matrices applied to a set of basis vectors.

### Dependencies
- `CART_EQ`: Vector equality is component-wise equality
- `transp`: Matrix transpose
- `matrix_vector_mul`: Matrix-vector multiplication definition
- `row`: Extracts a row from a matrix
- `VECTOR_3`: Properties of 3D vectors
- `LAMBDA_BETA`: Beta-reduction for lambda expressions
- `FORALL_3`: Universal quantification over 3D vectors
- `DIMINDEX_3`: Dimension of 3-dimensional vectors
- `SUM_3`: Summation over indices 1 to 3
- `REAL_ARITH_TAC`: Real arithmetic tactical

### Porting notes
When porting to other systems:
- Ensure that the destination system has appropriate matrix and vector libraries with explicit operations for extracting rows from matrices.
- The notation may differ in other systems - for example, the `$` operator used to access vector components might be represented differently.
- Some proof assistants might require more explicit type annotations or conversions when working with matrices and vectors.

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
For any $3 \times 3$ matrix $A$ with real entries, if the determinant of the matrix formed by vectors $x_1, y_1, z_1$ (denoted as $\det([x_1, y_1, z_1])$) is nonzero, then the following are equivalent:

1. $A x_1 = x_2$ and $A y_1 = y_2$ and $A z_1 = z_2$

2. For all indices $m, k \in \{1,2,3\}$, the matrix entry $A_{mk}$ equals:
   $$A_{mk} = \frac{\det(M_{mk})}{\det([x_1, y_1, z_1])}$$
   where $M_{mk}$ is the matrix obtained from $[x_1, y_1, z_1]$ by replacing its $k$-th column with the vector $[x_2(m), y_2(m), z_2(m)]^T$.

### Informal proof
This theorem applies Cramer's rule to a matrix equation system. The proof proceeds as follows:

* First, we use `MATRIX_LEMMA` to rewrite the left-hand side of the equivalence. This lemma establishes that the system of equations $Ax_1 = x_2$, $Ay_1 = y_2$, $Az_1 = z_2$ is equivalent to certain row-vector relations.

* Then, we apply Cramer's rule (via the `CRAMER` theorem) to solve for the matrix $A$ given our assumptions. Cramer's rule provides an explicit formula for each entry $A_{mk}$ in terms of determinants.

* The proof is completed by ensuring equality of vectors through `CART_EQ`, and handling the appropriate indices with `DIMINDEX_3` and `FORALL_3`.

### Mathematical insight
This lemma provides an explicit solution for a matrix $A$ given that it maps three linearly independent vectors $x_1, y_1, z_1$ to vectors $x_2, y_2, z_2$ respectively. The formula given is a matrix form of Cramer's rule.

The key insight is that when we have three linearly independent vectors (ensured by the non-zero determinant condition), a matrix mapping them to three other vectors is uniquely determined. The formula provides the explicit entries of this unique matrix using determinants.

This result is particularly useful in computer graphics, coordinate transformations, and solutions to systems of linear equations.

### Dependencies
- Theorems:
  - `MATRIX_LEMMA`: Relates matrix-vector products to row-vector products
  - `CRAMER`: Implementation of Cramer's rule for solving linear systems

### Porting notes
When porting this to another system, pay attention to:
1. The notation for matrices and vectors may differ
2. The indexing convention (HOL Light uses 1-indexed vectors)
3. The handling of determinants and matrix operations
4. How Cramer's rule is formulated in the target system

The theorem is specialized to $3 \times 3$ matrices, which makes it more concrete but potentially less general than a version for arbitrary dimensions.

---

## MATRIX_BY_CRAMER

### MATRIX_BY_CRAMER

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
For any $3 \times 3$ real matrix $A$ and vectors $x_1, y_1, z_1, x_2, y_2, z_2 \in \mathbb{R}^3$, if $d = \det([x_1, y_1, z_1])$ (where $[x_1, y_1, z_1]$ is the matrix formed by these column vectors) and $d \neq 0$, then:

$A \cdot x_1 = x_2 \land A \cdot y_1 = y_2 \land A \cdot z_1 = z_2$ if and only if the entries of matrix $A$ are given by Cramer's rule formulas:

$A_{11} = \frac{x_{21} \cdot y_{12} \cdot z_{13} + x_{12} \cdot y_{13} \cdot z_{21} + x_{13} \cdot y_{21} \cdot z_{12} - x_{21} \cdot y_{13} \cdot z_{12} - x_{12} \cdot y_{21} \cdot z_{13} - x_{13} \cdot y_{12} \cdot z_{21}}{d}$

$A_{12} = \frac{x_{11} \cdot y_{21} \cdot z_{13} + x_{21} \cdot y_{13} \cdot z_{11} + x_{13} \cdot y_{11} \cdot z_{21} - x_{11} \cdot y_{13} \cdot z_{21} - x_{21} \cdot y_{11} \cdot z_{13} - x_{13} \cdot y_{21} \cdot z_{11}}{d}$

$A_{13} = \frac{x_{11} \cdot y_{12} \cdot z_{21} + x_{12} \cdot y_{21} \cdot z_{11} + x_{21} \cdot y_{11} \cdot z_{12} - x_{11} \cdot y_{21} \cdot z_{12} - x_{12} \cdot y_{11} \cdot z_{21} - x_{21} \cdot y_{12} \cdot z_{11}}{d}$

$A_{21} = \frac{x_{22} \cdot y_{12} \cdot z_{13} + x_{12} \cdot y_{13} \cdot z_{22} + x_{13} \cdot y_{22} \cdot z_{12} - x_{22} \cdot y_{13} \cdot z_{12} - x_{12} \cdot y_{22} \cdot z_{13} - x_{13} \cdot y_{12} \cdot z_{22}}{d}$

$A_{22} = \frac{x_{11} \cdot y_{22} \cdot z_{13} + x_{22} \cdot y_{13} \cdot z_{11} + x_{13} \cdot y_{11} \cdot z_{22} - x_{11} \cdot y_{13} \cdot z_{22} - x_{22} \cdot y_{11} \cdot z_{13} - x_{13} \cdot y_{22} \cdot z_{11}}{d}$

$A_{23} = \frac{x_{11} \cdot y_{12} \cdot z_{22} + x_{12} \cdot y_{22} \cdot z_{11} + x_{22} \cdot y_{11} \cdot z_{12} - x_{11} \cdot y_{22} \cdot z_{12} - x_{12} \cdot y_{11} \cdot z_{22} - x_{22} \cdot y_{12} \cdot z_{11}}{d}$

$A_{31} = \frac{x_{23} \cdot y_{12} \cdot z_{13} + x_{12} \cdot y_{13} \cdot z_{23} + x_{13} \cdot y_{23} \cdot z_{12} - x_{23} \cdot y_{13} \cdot z_{12} - x_{12} \cdot y_{23} \cdot z_{13} - x_{13} \cdot y_{12} \cdot z_{23}}{d}$

$A_{32} = \frac{x_{11} \cdot y_{23} \cdot z_{13} + x_{23} \cdot y_{13} \cdot z_{11} + x_{13} \cdot y_{11} \cdot z_{23} - x_{11} \cdot y_{13} \cdot z_{23} - x_{23} \cdot y_{11} \cdot z_{13} - x_{13} \cdot y_{23} \cdot z_{11}}{d}$

$A_{33} = \frac{x_{11} \cdot y_{12} \cdot z_{23} + x_{12} \cdot y_{23} \cdot z_{11} + x_{23} \cdot y_{11} \cdot z_{12} - x_{11} \cdot y_{23} \cdot z_{12} - x_{12} \cdot y_{11} \cdot z_{23} - x_{23} \cdot y_{12} \cdot z_{11}}{d}$

where $x_{ij}$ denotes the $j$-th component of vector $x_i$.

### Informal proof
The proof utilizes Cramer's rule for explicitly computing the entries of a matrix that satisfies a given linear system.

First, we convert the statement into a form that can be handled by `MATRIX_BY_CRAMER_LEMMA`, which relates the linear system $A \cdot x_1 = x_2$, $A \cdot y_1 = y_2$, and $A \cdot z_1 = z_2$ to a matrix formula using determinants.

The lemma states that when $\det([x_1, y_1, z_1]) \neq 0$, the matrix $A$ satisfies the system if and only if:

$A = \lambda m k. \frac{\det(M_{mk})}{\det([x_1, y_1, z_1])}$

where $M_{mk}$ is the matrix obtained by replacing the $k$-th column of $[x_1, y_1, z_1]$ with the column vector $[x_{2m}, y_{2m}, z_{2m}]$.

After applying this lemma, we compute the determinants explicitly using the formula for a $3 \times 3$ determinant:

$\det(M) = M_{11}(M_{22}M_{33} - M_{23}M_{32}) - M_{12}(M_{21}M_{33} - M_{23}M_{31}) + M_{13}(M_{21}M_{32} - M_{22}M_{31})$

For each entry $A_{ij}$, we substitute the appropriate values into the determinant formula, resulting in the expressions shown in the theorem statement.

The proof checks that these explicit formulas are equivalent to the determinant-based formula from Cramer's rule.

### Mathematical insight
This theorem provides explicit formulas for the entries of a $3 \times 3$ matrix $A$ that maps three given linearly independent vectors to three other vectors. The result is a direct application of Cramer's rule to the matrix equation $A[x_1, y_1, z_1] = [x_2, y_2, z_2]$.

In linear algebra, this represents the solution to the matrix equation $AX = Y$ where $X$ and $Y$ are $3 \times 3$ matrices and $X$ is invertible. The solution is given by $A = YX^{-1}$, which can be computed element-wise using Cramer's rule.

The formulas might appear complex, but they're just the explicit expansions of determinants in Cramer's rule for the specific case of $3 \times 3$ matrices. Each formula gives the ratio of two determinants: the numerator is the determinant of the matrix obtained by replacing a column of $[x_1, y_1, z_1]$ with elements from $x_2$, $y_2$, or $z_2$, and the denominator is the determinant of $[x_1, y_1, z_1]$.

This theorem is particularly useful for computer graphics, robotics, and other applications where explicit formulas for matrix transformations are needed.

### Dependencies
- `MATRIX_BY_CRAMER_LEMMA`: The key lemma that relates the matrix equation to Cramer's rule using determinants
- `DET_3`: Formula for the determinant of a $3 \times 3$ matrix
- `CART_EQ`: Equality of cartesian vectors
- `LAMBDA_BETA`: Beta reduction for lambda expressions
- `DIMINDEX_3`: The dimension of $\mathbb{R}^3$
- `VECTOR_3`: Operations on 3D vectors

### Porting notes
When porting to other proof assistants:
1. The explicit calculations for determinants may be handled differently in other systems.
2. The notation for vector and matrix indexing varies across systems - ensure consistent indexing.
3. The proof uses HOL Light's let-expressions which may need different handling in other systems.
4. The formulas involve extensive algebraic manipulations - other systems might benefit from automation to verify these expressions.
5. Consider using a matrix library that might simplify some of the calculations rather than working with explicit component formulas.

---

## CONGRUENT_EDGES_TAC

### CONGRUENT_EDGES_TAC
- CONGRUENT_EDGES_TAC

### Type of the formal statement
- tactic definition

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
`CONGRUENT_EDGES_TAC` is a tactic in HOL Light that takes a theorem `edges` as input and helps prove that certain edges (segments) are congruent. It does this by:

1. Simplifying implications and quantifiers in the goal
2. Applying the theorem `edges` to rewrite the goal
3. Stripping assumptions and using them to rewrite the goal with the segment-convex hull relationship
4. Using the `CONGRUENT_SEGMENTS` theorem to convert the congruence of segments to equality of distances
5. Performing a series of conversions using `VECTOR3_SUB_CONV`, `VECTOR3_DOT_CONV`, and `REAL_RAT5_EQ_CONV` to simplify vector operations in 3D space

### Informal proof
This is a tactic definition rather than a theorem, so it doesn't have a proof in the traditional sense. However, the tactic implements a proof strategy that:

1. First simplifies the logical structure of the goal by converting implications and conjunctions to a more manageable form using `REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]` and `REWRITE_TAC[IMP_IMP]`.

2. Applies the provided `edges` theorem to rewrite the goal, effectively using known edge relationships.

3. Extracts and uses assumptions with `REPEAT STRIP_TAC` and then applies them with `ASM_REWRITE_TAC`.

4. Rewrites segments as convex hulls using `GSYM SEGMENT_CONVEX_HULL`.

5. Uses the theorem `CONGRUENT_SEGMENTS` which states that if two segments have the same length, they are congruent.

6. Converts the distance equality to norm equality using `DIST_EQ` and then further to the squared norm using `NORM_POW_2`.

7. Applies a sequence of conversions to simplify vector operations in three-dimensional space:
   - `VECTOR3_SUB_CONV` to compute vector differences
   - `VECTOR3_DOT_CONV` to compute dot products
   - `REAL_RAT5_EQ_CONV` to simplify rational equalities

### Mathematical insight
This tactic is specialized for proving congruence of edges (line segments) in three-dimensional geometric figures, likely polytopes or specifically platonic solids (given its location in the "platonic.ml" file).

The key insight is that two segments are congruent if and only if they have the same length, which can be verified by calculating the squared distance between endpoints. In the context of vectors in 3D space, this involves vector subtraction and dot product calculations.

The tactic automates a proof pattern that would otherwise need to be repeated many times when establishing properties of regular polyhedra, where many edges have the same length.

### Dependencies
- **Theorems**:
  - `CONGRUENT_SEGMENTS`: Proves that segments with the same distance between endpoints are congruent
  - `VECTOR3_SUB_CONV`: Conversion for vector subtraction in 3D
  - `VECTOR3_DOT_CONV`: Conversion for dot products in 3D

### Porting notes
When porting to another system:
- You'll need equivalent theorems for vector operations in 3D space
- This tactic makes heavy use of HOL Light's conversion combinators, which may need to be reimplemented in other systems
- The approach relies on conversions for rational arithmetic (`REAL_RAT5_EQ_CONV`, etc.), so similar facilities for computational reflection may be needed
- The specificity to 3D vectors suggests this is part of a larger development for 3D geometry, so porting should consider the broader context

---

## CONGRUENT_FACES_TAC

### CONGRUENT_FACES_TAC

### Type of the formal statement
- HOL Light tactic (function)

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
`CONGRUENT_FACES_TAC` is a tactic designed to prove that two geometric faces are congruent. Given a theorem `facets` that describes faces of a polyhedron, this tactic:

1. Restructures implications in the goal
2. Applies the given `facets` theorem 
3. Identifies three adjacent points from each of the two faces
4. Constructs an orthogonal transformation matrix that maps the first face to the second
5. Proves that this transformation preserves the structure, demonstrating congruence

The tactic operates by finding an orthogonal matrix that maps three points from one face to three points of the other face, then proving that this matrix defines a congruent mapping between the faces.

### Informal proof
The tactic implements the following proof strategy:

1. First, it simplifies implications in the goal using standard logical rewrites.
2. It applies the given `facets` theorem to introduce information about the polyhedron's faces.
3. It extracts three adjacent points from each of the two faces being compared: $(x_1, y_1, z_1)$ from the first face and $(x_2, y_2, z_2)$ from the second face.
4. It applies `MATRIX_BY_CRAMER` to find a matrix $A$ that satisfies:
   $A \cdot x_1 = x_2$, $A \cdot y_1 = y_2$, and $A \cdot z_1 = z_2$.
5. It performs several algebraic simplifications using specialized conversion tactics for real numbers involving $\sqrt{5}$ (typical in calculations involving Platonic solids):
   - `REAL_RAT5_MUL_CONV`
   - `REAL_RAT5_ADD_CONV`
   - `REAL_RAT5_SUB_CONV`
   - `REAL_RAT5_DIV_CONV`
   - `REAL_RAT5_EQ_CONV`
6. It constructs a $3×3$ matrix from the computed values.
7. It proves that this matrix is orthogonal by showing $A^T \cdot A = I$ (the identity matrix).
8. It applies `CONGRUENT_SIMPLE` to establish that the convex hulls of the two faces are congruent, based on the orthogonal transformation.
9. It completes the proof by showing that the matrix maps the points of the first face to those of the second face.

### Mathematical insight
This tactic implements a fundamental geometric principle: two shapes in 3D space are congruent if one can be mapped to the other by an orthogonal transformation (a rotation and/or reflection). The key insight is that if three non-collinear points from one shape can be mapped to three corresponding points of another, then the entire shapes are congruent if they are defined by those points (e.g., as convex hulls).

The tactic specifically deals with expressions involving $\sqrt{5}$, which suggests it was designed for working with regular polyhedra (particularly the dodecahedron and icosahedron, which involve the golden ratio and thus $\sqrt{5}$).

The implementation uses Cramer's rule to find the transformation matrix, which is a standard technique in linear algebra for solving systems of linear equations when a unique solution exists.

### Dependencies
- **Theorems**:
  - `MATRIX_BY_CRAMER`: Provides formulas for matrix entries that map three 3D points to another three 3D points
  - `CONGRUENT_SIMPLE`: States that shapes related by an orthogonal transformation are congruent
  - `MATRIX_VECTOR_MUL_3`: Explicit formula for 3×3 matrix multiplication with vectors
  - `REAL_RAT5_ADD_CONV`, `REAL_RAT5_SUB_CONV`, `REAL_RAT5_MUL_CONV`: Conversion rules for arithmetic with expressions involving $\sqrt{5}$

### Porting notes
When implementing this in another system:
1. You'll need robust support for linear algebra, particularly orthogonal matrices and transformations
2. Special care must be taken with the arithmetic involving $\sqrt{5}$ - you may need to develop appropriate simplification strategies
3. The tactic uses HOL Light's tactical programming extensively - you'll need to identify the corresponding proof automation mechanisms in your target system
4. The tactic relies on the `three_adjacent_points` function which isn't shown but presumably extracts three adjacent vertices from a face representation - you'll need an equivalent

The tactic is specialized for working with regular polyhedra, particularly those involving the golden ratio. In systems with strong geometric libraries, you might find more direct ways to establish congruence.

---

## TETRAHEDRON_CONGRUENT_EDGES

### TETRAHEDRON_CONGRUENT_EDGES

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TETRAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_tetrahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_tetrahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC TETRAHEDRON_EDGES);;
```

### Informal statement
For any two edges $e_1$ and $e_2$ of the standard tetrahedron (where an edge is defined as a 1-dimensional face), $e_1$ is congruent to $e_2$.

More precisely, for any sets $e_1, e_2 \subset \mathbb{R}^3$, if $e_1$ is a face of the standard tetrahedron with affine dimension 1, and $e_2$ is also a face of the standard tetrahedron with affine dimension 1, then $e_1$ is congruent to $e_2$.

Here, "congruent" means that there exists a vector $c \in \mathbb{R}^3$ and an orthogonal transformation $f$ such that $e_2 = \{c + f(x) \mid x \in e_1\}$.

### Informal proof
The proof uses a tactic `CONGRUENT_EDGES_TAC` applied to the theorem `TETRAHEDRON_EDGES`.

The theorem `TETRAHEDRON_EDGES` characterizes all the edges of the standard tetrahedron. It states that a set $e$ is a 1-dimensional face of the standard tetrahedron if and only if $e$ is one of the six line segments connecting pairs of vertices of the tetrahedron.

The tactic `CONGRUENT_EDGES_TAC` likely checks that all these edges have the same length and are therefore congruent to each other. This is expected because the standard tetrahedron is a regular tetrahedron, which has all edges of equal length.

The standard tetrahedron is defined with vertices at $\{(1,1,1), (-1,-1,1), (-1,1,-1), (1,-1,-1)\}$. By examining the coordinates, we can verify that the distance between any two vertices is $2\sqrt{2}$, confirming that all edges have the same length and are congruent.

### Mathematical insight
This theorem establishes an important property of the standard tetrahedron: all of its edges are congruent. This is a characteristic property of regular polyhedra in general, and the regular tetrahedron in particular.

The standard tetrahedron is defined with vertices at specific coordinates chosen to make it a regular tetrahedron centered at the origin. This regularity ensures that all edges have the same length, all faces are congruent equilateral triangles, and the tetrahedron has full symmetry.

This result is part of a broader family of theorems establishing the regularity properties of Platonic solids, which are fundamental objects in geometry and group theory.

### Dependencies
- Definitions:
  - `std_tetrahedron`: The standard tetrahedron in $\mathbb{R}^3$ defined as the convex hull of the points $\{(1,1,1), (-1,-1,1), (-1,1,-1), (1,-1,-1)\}$
  - `congruent`: Two sets are congruent if one can be obtained from the other by a rigid motion (an orthogonal transformation plus a translation)
  
- Theorems:
  - `TETRAHEDRON_EDGES`: Characterization of all edges (1-dimensional faces) of the standard tetrahedron

### Porting notes
When porting this theorem:
1. Ensure your system has a definition of the standard tetrahedron with the same vertices
2. Verify that your definition of congruence matches HOL Light's (involving orthogonal transformations and translations)
3. The automated tactic used in HOL Light may need to be replaced with a more explicit proof in other systems, showing that all edges have the same length

---

## TETRAHEDRON_CONGRUENT_FACETS

### TETRAHEDRON_CONGRUENT_FACETS

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let TETRAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_tetrahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_tetrahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC TETRAHEDRON_FACETS);;
```

### Informal statement
For any two faces $f_1$ and $f_2$ of the standard tetrahedron in $\mathbb{R}^3$, if both $f_1$ and $f_2$ have affine dimension 2 (i.e., they are 2-dimensional faces or facets), then $f_1$ and $f_2$ are congruent.

Here, the standard tetrahedron is defined as the convex hull of the set $\{\text{vector}[1,1,1], \text{vector}[-1,-1,1], \text{vector}[-1,1,-1], \text{vector}[1,-1,-1]\}$ in $\mathbb{R}^3$, and congruence between two sets means that one can be transformed into the other through an orthogonal transformation (rotation+reflection) followed by a translation.

### Informal proof
This theorem is proved using a specialized tactic `CONGRUENT_FACES_TAC` applied to `TETRAHEDRON_FACETS`. 

The proof works as follows:

- First, we recall that `TETRAHEDRON_FACETS` provides a complete characterization of all 2-dimensional faces of the standard tetrahedron. It states that a set $f$ is a 2-dimensional face of the standard tetrahedron if and only if it equals one of the four triangular faces:
  - $\text{convex hull }\{\text{vector}[-1,-1,1], \text{vector}[-1,1,-1], \text{vector}[1,-1,-1]\}$
  - $\text{convex hull }\{\text{vector}[-1,-1,1], \text{vector}[-1,1,-1], \text{vector}[1,1,1]\}$
  - $\text{convex hull }\{\text{vector}[-1,-1,1], \text{vector}[1,-1,-1], \text{vector}[1,1,1]\}$
  - $\text{convex hull }\{\text{vector}[-1,1,-1], \text{vector}[1,-1,-1], \text{vector}[1,1,1]\}$

- The `CONGRUENT_FACES_TAC` applies this characterization to show that any two faces $f_1$ and $f_2$ satisfying the hypothesis must both be one of these four triangular faces.

- Since the standard tetrahedron is a regular tetrahedron, all of its triangular faces are equilateral triangles with the same dimensions. Therefore, any two faces can be transformed into each other through an orthogonal transformation and translation, which is precisely the definition of congruence.

### Mathematical insight
This theorem establishes an important property of the standard tetrahedron: all of its facets (2-dimensional faces) are congruent. 

This result aligns with the fact that the standard tetrahedron is a regular tetrahedron, which is characterized by having all faces as congruent equilateral triangles. This property is one of the defining features of regular polyhedra, where all faces are congruent regular polygons and all vertices are symmetric.

The theorem contributes to the formal verification of the geometric properties of Platonic solids, of which the tetrahedron is the simplest example having only 4 vertices, 6 edges, and 4 faces. The congruence of faces is fundamental to establishing the symmetry and regularity of Platonic solids.

### Dependencies
- **Theorems:**
  - `TETRAHEDRON_FACETS`: Characterizes all 2-dimensional faces of the standard tetrahedron.
  
- **Definitions:**
  - `std_tetrahedron`: Defines the standard tetrahedron as the convex hull of four specific points in 3D space.
  - `congruent`: Defines when two sets are congruent via orthogonal transformations and translation.
  - `face_of`: Relation indicating when a set is a face of a convex set (from geometry library).
  - `aff_dim`: Function that gives the affine dimension of a set (from geometry library).

### Porting notes
When porting this theorem:
1. Ensure that the definition of the standard tetrahedron uses the same specific vertices.
2. Make sure your system has a compatible definition of congruence for geometric objects.
3. The proof relies on a specialized tactic (`CONGRUENT_FACES_TAC`), which you may need to implement differently in other systems, typically by proving that all faces are equilateral triangles with the same side length.
4. The fact that the standard tetrahedron is regular (having all faces as congruent regular polygons) may be more directly provable in some systems, making this theorem a corollary of that fact.

---

## CUBE_CONGRUENT_EDGES

### CUBE_CONGRUENT_EDGES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let CUBE_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_cube /\ aff_dim e1 = &1 /\
           e2 face_of std_cube /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC CUBE_EDGES);;
```

### Informal statement
For any two edges $e_1$ and $e_2$ of the standard cube, i.e., $e_1 \text{ face\_of } \text{std\_cube}$ and $e_2 \text{ face\_of } \text{std\_cube}$ with affine dimension $\text{aff\_dim } e_1 = \text{aff\_dim } e_2 = 1$, the edges $e_1$ and $e_2$ are congruent.

Here, "congruent" means there exists a vector $c$ and an orthogonal transformation $f$ such that $e_2 = \{c + f(x) \mid x \in e_1\}$.

### Informal proof
The proof applies the `CONGRUENT_EDGES_TAC` tactic with the theorem `CUBE_EDGES`. 

This tactic works by:
1. Using `CUBE_EDGES` which explicitly characterizes all 12 edges of the standard cube as convex hulls of pairs of vertices.
2. Showing that all these edges have the same length (= 2), as each edge connects vertices that differ in exactly one coordinate.
3. Since all edges have the same length and are straight line segments, they are congruent to each other under appropriate rotation and translation.

### Mathematical insight
This theorem establishes that all edges of a standard cube are congruent, which is a fundamental geometric property of regular polyhedra. This is intuitively clear since a cube is a regular solid with all edges of the same length, but the formal proof requires showing that appropriate orthogonal transformations exist between any two edges.

The result is important for establishing symmetry properties of the cube and is a step toward characterizing the full symmetry group of the cube. It demonstrates that the cube has edge-transitivity, meaning any edge can be mapped to any other edge through a symmetry of the cube.

### Dependencies
- Theorems:
  - `CUBE_EDGES`: Characterizes all edges of the standard cube as convex hulls of pairs of vertices
- Definitions:
  - `std_cube`: The standard cube in 3D space with vertices at $(\pm 1, \pm 1, \pm 1)$
  - `congruent`: Two sets are congruent if there exists a translation and orthogonal transformation mapping one to the other

### Porting notes
When porting this theorem:
1. Ensure the definition of congruence matches (translation + orthogonal transformation)
2. The standard cube definition should have vertices at $(\pm 1, \pm 1, \pm 1)$
3. The tactical approach may need to be replaced with a more explicit proof showing that all edges have the same length (= 2), and then proving that segments of equal length are congruent

---

## CUBE_CONGRUENT_FACETS

### CUBE_CONGRUENT_FACETS
- Name: CUBE_CONGRUENT_FACETS

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let CUBE_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_cube /\ aff_dim f1 = &2 /\
           f2 face_of std_cube /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC CUBE_FACETS);;
```

### Informal statement
For any faces $f_1$ and $f_2$ of the standard cube in $\mathbb{R}^3$, if both $f_1$ and $f_2$ have affine dimension 2, then $f_1$ is congruent to $f_2$.

Here:
- The standard cube `std_cube` is defined as the convex hull of the eight points $\{\pm 1, \pm 1, \pm 1\}$ in $\mathbb{R}^3$.
- Two sets $s$ and $t$ in $\mathbb{R}^N$ are congruent if there exists a point $c$ and an orthogonal transformation $f$ such that $t = \{c + f(x) \mid x \in s\}$, i.e., one can be obtained from the other by a rigid motion.

### Informal proof
The proof follows directly from the fact that all 2-dimensional faces of the standard cube are congruent to each other. 

The theorem is proved using `CONGRUENT_FACES_TAC CUBE_FACETS`, which applies a tactic designed to prove congruence of faces. The tactic uses `CUBE_FACETS`, which provides an explicit characterization of all 2-dimensional faces of the standard cube.

From `CUBE_FACETS`, we know that the 2-dimensional faces of the standard cube are exactly the six square faces, each being the convex hull of four vertices. Since all these faces are squares with side length 2, they are all congruent to each other by rigid motions in $\mathbb{R}^3$.

### Mathematical insight
This theorem establishes that all 2-dimensional faces (i.e., the square faces) of the standard cube are congruent. This is an expected property of regular polyhedra like the cube, where all faces should be congruent regular polygons.

This result contributes to the formal characterization of Platonic solids in three-dimensional Euclidean space. The property proved here reflects the high degree of symmetry in the cube, which is one of the five Platonic solids. 

The proof strategy demonstrates how formal systems can leverage explicit characterizations (like `CUBE_FACETS`) combined with general tactics (like `CONGRUENT_FACES_TAC`) to establish geometric properties efficiently.

### Dependencies
- Theorems:
  - `CUBE_FACETS`: Characterizes all 2-dimensional faces of the standard cube
- Definitions:
  - `std_cube`: The standard cube defined as the convex hull of the eight points $\{\pm 1, \pm 1, \pm 1\}$ in $\mathbb{R}^3$
  - `congruent`: Two sets are congruent if one can be mapped to the other by an orthogonal transformation combined with a translation

### Porting notes
When porting this to another system:
1. Ensure the system has a well-defined notion of congruence between sets that matches the definition used here.
2. The proof relies on the explicit enumeration of all 2-dimensional faces of the cube, so this characterization must be available or provable in the target system.
3. The automated tactic `CONGRUENT_FACES_TAC` would need to be reimplemented or replaced with appropriate proof steps in the target system.

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
For any two edges $e_1$ and $e_2$ of the standard octahedron, if both $e_1$ and $e_2$ are faces of the standard octahedron with affine dimension 1, then $e_1$ is congruent to $e_2$.

In other words, all edges of the standard octahedron are congruent to each other.

### Informal proof
This theorem is proved by applying the tactic `CONGRUENT_EDGES_TAC` to the theorem `OCTAHEDRON_EDGES`.

The theorem `OCTAHEDRON_EDGES` provides a complete characterization of the edges of the standard octahedron, listing all 12 edges as convex hulls of pairs of adjacent vertices.

The proof shows that any two edges of the standard octahedron are congruent through the following steps:
- The standard octahedron is a regular polyhedron with all edges having the same length
- All edges connect pairs of vertices that are the same distance apart
- For any two edges, there exists an orthogonal transformation (a rotation and/or reflection) plus a translation that maps one edge to the other
- This satisfies the definition of congruence between geometric objects

### Mathematical insight
This theorem establishes an important geometric property of the standard octahedron: all of its edges are congruent to each other. This is a fundamental characteristic of regular polyhedra, of which the octahedron is one of the five Platonic solids.

The congruence of edges is crucial for the regularity of the octahedron, as it implies all edges have the same length. This property, along with the congruence of faces and equal vertex configuration, defines what makes a polyhedron regular.

The standard octahedron in this formalization has vertices at the six points $(\pm 1, 0, 0)$, $(0, \pm 1, 0)$, and $(0, 0, \pm 1)$ in $\mathbb{R}^3$, which creates a highly symmetric structure where all edges have length $\sqrt{2}$.

### Dependencies
- **Theorems**:
  - `OCTAHEDRON_EDGES`: Characterizes all 12 edges of the standard octahedron

- **Definitions**:
  - `std_octahedron`: Defines the standard octahedron as the convex hull of six points in 3D space
  - `congruent`: Two sets are congruent if one can be obtained from the other by an orthogonal transformation and a translation

### Porting notes
When porting this theorem:
1. Ensure that the definition of "congruent" matches exactly - it requires the existence of both a translation and an orthogonal transformation
2. The standard octahedron definition should be consistent with the placement of vertices at $(\pm 1, 0, 0)$, $(0, \pm 1, 0)$, and $(0, 0, \pm 1)$
3. The tactic `CONGRUENT_EDGES_TAC` appears to be a custom tactic for proving congruence of edges - you may need to implement its equivalent in the target system

---

## OCTAHEDRON_CONGRUENT_FACETS

### OCTAHEDRON_CONGRUENT_FACETS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let OCTAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_octahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_octahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC OCTAHEDRON_FACETS);;
```

### Informal statement
For any two facets $f_1$ and $f_2$ of the standard octahedron, where both $f_1$ and $f_2$ have affine dimension 2, $f_1$ is congruent to $f_2$.

Here, a "facet" refers to a face of the highest possible dimension (which is 2 for the octahedron), and two sets are "congruent" if one can be obtained from the other by an isometry (an orthogonal transformation followed by a translation).

### Informal proof
The proof is carried out by applying a tactic `CONGRUENT_FACES_TAC` to the theorem `OCTAHEDRON_FACETS`.

The theorem `OCTAHEDRON_FACETS` characterizes exactly which subsets are facets of the standard octahedron - they are precisely the 8 triangular faces, each formed by the convex hull of three vertices of the octahedron.

The `CONGRUENT_FACES_TAC` tactic likely works by:
1. Using the characterization provided by `OCTAHEDRON_FACETS` to establish that all facets of the octahedron are triangles with identical geometric properties (same side lengths, angles, etc.)
2. Showing that any two such facets can be mapped to each other by an orthogonal transformation followed by a translation, which is the definition of congruence

Since all facets of the standard octahedron are equilateral triangles of the same size, they are all congruent to each other.

### Mathematical insight
This theorem establishes an important symmetry property of the octahedron - all of its facets (2-dimensional faces) are geometrically identical. This is a key characteristic of regular polyhedra, where all faces are congruent regular polygons.

The standard octahedron in HOL Light is defined as the convex hull of six points: the unit vectors along the positive and negative directions of the three coordinate axes. This gives a very symmetric construction where all facets are equilateral triangles with side length $\sqrt{2}$.

This result is part of the broader study of the Platonic solids and their geometric properties, particularly focusing on their high degree of symmetry. Such regular polyhedra have been of mathematical interest since ancient times and have applications in various fields including crystallography, chemistry, and computer graphics.

### Dependencies
- **Theorems**:
  - `OCTAHEDRON_FACETS`: Characterizes the 2-dimensional faces of the standard octahedron

- **Definitions**:
  - `std_octahedron`: The standard octahedron defined as the convex hull of the six points (±1,0,0), (0,±1,0), (0,0,±1)
  - `congruent`: Two sets are congruent if one can be obtained from the other by an orthogonal transformation followed by a translation

### Porting notes
When porting this theorem to another system, ensure that:
1. The definition of the standard octahedron is transferred correctly
2. The notion of congruence between sets is properly defined
3. The system has appropriate tactics or methods to handle geometric reasoning about polyhedra and their faces

In systems with less automated geometric reasoning, you might need to construct a more explicit proof showing that any two facets have the same side lengths and angles, and can be mapped to each other by an isometry.

---

## DODECAHEDRON_CONGRUENT_EDGES

### DODECAHEDRON_CONGRUENT_EDGES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DODECAHEDRON_CONGRUENT_EDGES = prove
 (`!e1 e2. e1 face_of std_dodecahedron /\ aff_dim e1 = &1 /\
           e2 face_of std_dodecahedron /\ aff_dim e2 = &1
           ==> e1 congruent e2`,
  CONGRUENT_EDGES_TAC DODECAHEDRON_EDGES);;
```

### Informal statement
For any two edges $e_1$ and $e_2$ of the standard dodecahedron, if $e_1$ and $e_2$ are both faces of the standard dodecahedron with affine dimension 1, then $e_1$ is congruent to $e_2$.

Formally, $\forall e_1, e_2$ such that $e_1$ face_of std_dodecahedron $\land$ aff_dim $e_1 = 1$ $\land$ $e_2$ face_of std_dodecahedron $\land$ aff_dim $e_2 = 1$, we have $e_1$ congruent $e_2$.

### Informal proof
The theorem is proved using the `CONGRUENT_EDGES_TAC` tactic applied to `DODECAHEDRON_EDGES`.

This tactic shows that all edges of the dodecahedron are congruent to each other by:
1. Using the comprehensive characterization of the edges from `DODECAHEDRON_EDGES`, which identifies all 30 edges of the standard dodecahedron
2. Verifying that each edge has the same length
3. Applying the definition of congruence, which requires the existence of an orthogonal transformation and a translation that maps one edge to another

Since all edges of a regular dodecahedron have the same length (they are all congruent line segments), the theorem follows directly.

### Mathematical insight
This theorem formalizes a fundamental property of the regular dodecahedron: all of its edges are congruent. This is a defining characteristic of Platonic solids - they have congruent faces and congruent edges.

The standard dodecahedron is defined with vertices that are a combination of:
- The eight vertices of a cube with coordinates $(\pm 1, \pm 1, \pm 1)$
- Twelve additional vertices related to the golden ratio $\phi = \frac{1+\sqrt{5}}{2}$

All edges of the dodecahedron have the same length, which can be calculated from the coordinates of the vertices. This is essential for the dodecahedron to be a regular polyhedron.

The congruence of all edges is important for symmetry properties of the dodecahedron and its classification as one of the five Platonic solids.

### Dependencies
- Theorems:
  - `DODECAHEDRON_EDGES`: Provides an explicit characterization of all edges of the standard dodecahedron
- Definitions:
  - `std_dodecahedron`: Defines the standard dodecahedron in 3D space
  - `congruent`: Defines when two sets are congruent (one can be mapped to the other by an orthogonal transformation and a translation)
- Tactics:
  - `CONGRUENT_EDGES_TAC`: A specialized tactic that proves congruence of all edges given their explicit characterization

### Porting notes
When porting this theorem:
1. Ensure that the standard dodecahedron is defined with the same coordinates
2. The definition of congruence might vary between systems, but should capture the same geometric notion (existence of isometry)
3. Rather than reproducing the exact tactic, focus on proving that all edges have the same length, which may be more straightforward in other systems
4. The explicit list of edges from `DODECAHEDRON_EDGES` may not be needed if the target system has better automation for geometric reasoning

---

## DODECAHEDRON_CONGRUENT_FACETS

### DODECAHEDRON_CONGRUENT_FACETS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let DODECAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_dodecahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_dodecahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC DODECAHEDRON_FACETS);;
```

### Informal statement
For all subsets $f_1$ and $f_2$ of $\mathbb{R}^3$, if $f_1$ is a face of the standard dodecahedron with affine dimension 2, and $f_2$ is a face of the standard dodecahedron with affine dimension 2, then $f_1$ is congruent to $f_2$.

In other words, any two 2-dimensional faces of the standard dodecahedron are congruent to each other. Here, "congruent" means there exists a vector $c$ and an orthogonal transformation $f$ such that $f_2 = \{c + f(x) \mid x \in f_1\}$.

### Informal proof
This theorem states that all 2-dimensional facets (i.e., pentagonal faces) of the standard dodecahedron are congruent to each other.

The proof uses a special tactic called `CONGRUENT_FACES_TAC` applied to the theorem `DODECAHEDRON_FACETS`. The `DODECAHEDRON_FACETS` theorem characterizes all 12 pentagonal faces of the standard dodecahedron as specific convex hulls of 5 vertices each.

The `CONGRUENT_FACES_TAC` likely works by:
1. Extracting all the faces from `DODECAHEDRON_FACETS`
2. Computing the distances between vertices for each face
3. Verifying that these distances are identical for all faces (up to permutation)
4. Concluding that all faces are congruent since they are all regular pentagons of the same size

Since the standard dodecahedron is a Platonic solid, all of its faces must be congruent regular polygons (in this case, regular pentagons), so this result matches the expected geometric property.

### Mathematical insight
This theorem confirms a fundamental property of Platonic solids: all faces of a Platonic solid are congruent regular polygons. For the dodecahedron specifically, all 12 faces are congruent regular pentagons.

The theorem is important because:
1. It verifies that the formal definition of `std_dodecahedron` correctly captures the mathematical properties of a dodecahedron
2. It establishes that the faces satisfy the geometric requirements for a Platonic solid
3. It can be used as a building block for proving other properties of the dodecahedron

This result is part of a larger formalization of Platonic solids in HOL Light, which demonstrates how complex geometric objects can be precisely defined and their properties proven in a formal system.

### Dependencies
- **Theorems**: 
  - `DODECAHEDRON_FACETS`: Characterizes the 12 pentagonal faces of the standard dodecahedron as specific convex hulls
- **Definitions**: 
  - `std_dodecahedron`: Defines the standard dodecahedron as the convex hull of 20 specific points in 3D space
  - `congruent`: Defines when two sets in N-dimensional space are congruent via an orthogonal transformation and translation

### Porting notes
When porting this theorem to another system:
1. Ensure that the definition of a dodecahedron matches the HOL Light version, particularly the coordinates of the vertices
2. The proof strategy may differ based on the system's capabilities, but the core idea of showing that all pentagonal faces have identical dimensions and angles should be maintained
3. The congruence relation may be defined differently in other systems, so care should be taken to align the definitions
4. In systems with more geometric automation, there might be simpler ways to establish face congruence directly from the symmetry properties of Platonic solids

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
For any edges $e_1$ and $e_2$ of the standard icosahedron, where an edge is defined as a face of dimension 1, $e_1$ and $e_2$ are congruent. In other words, all edges of the standard icosahedron have the same shape and size up to rotation and translation.

Formally, for all $e_1, e_2 \subset \mathbb{R}^3$:
$$e_1 \text{ face_of } \text{std_icosahedron} \land \text{aff_dim}(e_1) = 1 \land e_2 \text{ face_of } \text{std_icosahedron} \land \text{aff_dim}(e_2) = 1 \Rightarrow e_1 \text{ congruent } e_2$$

where two sets are congruent if one can be mapped to the other by a composition of translation and orthogonal transformation.

### Informal proof
The proof uses the tactic `CONGRUENT_EDGES_TAC` applied to the theorem `ICOSAHEDRON_EDGES`.

The theorem `ICOSAHEDRON_EDGES` provides a complete characterization of all edges (1-dimensional faces) of the standard icosahedron. Each edge is represented as the convex hull of two vertices.

The tactic `CONGRUENT_EDGES_TAC` is designed to prove that all edges in a polyhedron are congruent by:
1. Using the complete list of edges from `ICOSAHEDRON_EDGES`
2. Computing the length of each edge
3. Verifying that all edges have the same length

Since all edges have the same length and are straight line segments (as they are convex hulls of two points), they are congruent to each other by definition of congruence, which allows for rotation and translation.

### Mathematical insight
This theorem establishes an important regularity property of the standard icosahedron: all of its edges are congruent. This is one of the defining characteristics of Platonic solids, which include the icosahedron.

The standard icosahedron has 30 edges, all of which have the same length. This property, along with other regularities (such as all faces being congruent equilateral triangles and all vertices having the same number of edges meeting at them), makes the icosahedron one of the five Platonic solids.

The congruence of edges is crucial for the high degree of symmetry exhibited by Platonic solids. This symmetry has implications in various fields, from crystallography to mathematical group theory.

### Dependencies
- Theorems:
  - `ICOSAHEDRON_EDGES`: Provides a complete enumeration of the 30 edges of the standard icosahedron.
  
- Definitions:
  - `std_icosahedron`: Defines the standard icosahedron as the convex hull of 12 specific points in 3D space.
  - `congruent`: Defines when two sets in Euclidean space are congruent, i.e., one can be obtained from the other by rotation and translation.

### Porting notes
When porting this theorem:
1. Ensure that the definition of "congruent" involves both rotation (orthogonal transformation) and translation.
2. The proof relies on a tactic that computes and compares the lengths of all edges, which might need to be reimplemented depending on the target system's libraries for vector operations.
3. The standard icosahedron definition should be consistent with the one in HOL Light, particularly the coordinates of the vertices.
4. In systems with stronger automation for geometric reasoning, it might be possible to provide a more concise proof by appealing directly to the regularity properties of Platonic solids.

---

## ICOSAHEDRON_CONGRUENT_FACETS

### ICOSAHEDRON_CONGRUENT_FACETS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ICOSAHEDRON_CONGRUENT_FACETS = prove
 (`!f1 f2. f1 face_of std_icosahedron /\ aff_dim f1 = &2 /\
           f2 face_of std_icosahedron /\ aff_dim f2 = &2
           ==> f1 congruent f2`,
  CONGRUENT_FACES_TAC ICOSAHEDRON_FACETS);;
```

### Informal statement
For any two faces $f_1$ and $f_2$ of the standard icosahedron in $\mathbb{R}^3$, if both have affine dimension 2, then $f_1$ is congruent to $f_2$.

Here, "face_of" means $f_1$ and $f_2$ are faces of the standard icosahedron, "aff_dim f = &2" means the face has affine dimension 2 (i.e., it's a 2-dimensional face, which for a polyhedron means a facet), and "congruent" means there exists a translation and orthogonal transformation (rotation or reflection) that maps one face to the other.

### Informal proof
This theorem states that all facets of the standard icosahedron are congruent to each other. The proof uses the `CONGRUENT_FACES_TAC` tactic applied to the `ICOSAHEDRON_FACETS` theorem.

The theorem `ICOSAHEDRON_FACETS` provides a complete enumeration of all 20 triangular faces of the standard icosahedron, characterized by their vertices. Since the standard icosahedron is a regular polyhedron, all of its faces are congruent to each other. The tactic `CONGRUENT_FACES_TAC` automates the process of checking that all possible pairs of faces in this enumeration are congruent to each other through suitable orthogonal transformations.

### Mathematical insight
This theorem formalizes a key property of regular polyhedra: all of their faces are congruent. For the icosahedron, all faces are equilateral triangles of the same size. The standard icosahedron has 20 triangular faces, and this theorem confirms that they are all congruent to each other, which is an essential property of this regular polyhedron.

The result is part of a broader effort to formalize properties of Platonic solids. While seemingly straightforward from a geometric perspective, formalizing this property requires a detailed enumeration of all faces and a formal definition of congruence in terms of orthogonal transformations.

### Dependencies
- Theorems:
  - `ICOSAHEDRON_FACETS`: Provides the complete enumeration of the 20 triangular faces of the standard icosahedron.

- Definitions:
  - `std_icosahedron`: Defines the standard icosahedron in 3D space using a specific set of vertices.
  - `congruent`: Defines when two sets in n-dimensional space are congruent (i.e., one can be mapped to the other by a translation and orthogonal transformation).

### Porting notes
When porting this theorem:
1. Ensure that the definition of congruence is consistent with the original definition in HOL Light, which involves both translations and orthogonal transformations.
2. The enumeration of facets in `ICOSAHEDRON_FACETS` is quite lengthy, listing all 20 triangular faces explicitly with their coordinates. Consider whether the target system has libraries for polyhedra that might provide a more elegant approach.
3. The proof uses the specialized tactic `CONGRUENT_FACES_TAC`, which would need to be reimplemented or replaced with appropriate tactics in the target system.

---

