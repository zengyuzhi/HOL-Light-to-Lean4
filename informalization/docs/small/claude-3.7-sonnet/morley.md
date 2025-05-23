# morley.ml

## Overview

Number of statements: 22

This file formalizes Alain Connes's proof of Morley's theorem in Euclidean geometry, which states that the three points of intersection of adjacent angle trisectors of a triangle form an equilateral triangle. It leverages the geometric framework from the multivariate geometry library and iteration utilities to develop the necessary constructions and proofs. The formalization follows Connes's approach, which uses complex numbers to provide an elegant proof of this classic theorem.

## reflect2d

### Name of formal statement
reflect2d

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let reflect2d = new_definition
 `reflect2d t = rotate2d t o cnj o rotate2d(--t)`;;
```

### Informal statement
The function `reflect2d` defines reflection about a line through the origin making angle $t$ with the positive real axis. Mathematically, for any angle $t$:

$$\text{reflect2d}(t) = \text{rotate2d}(t) \circ \text{cnj} \circ \text{rotate2d}(-t)$$

where:
- $\text{rotate2d}(t)$ represents rotation by angle $t$ in the complex plane
- $\text{cnj}$ represents complex conjugation
- $\circ$ denotes function composition

### Informal proof
This is a definition, not a theorem requiring proof.

### Mathematical insight
This definition provides a concise way to express reflection about any line through the origin in the complex plane. The key insight is the composition of three operations:

1. First rotate the plane by $-t$ so that the reflection line aligns with the real axis
2. Then perform complex conjugation, which reflects points across the real axis
3. Finally rotate back by $t$ to return to the original orientation

This approach simplifies working with reflections about arbitrary lines through the origin by reducing them to the standard reflection across the real axis (complex conjugation) combined with appropriate rotations.

The definition is used in the formalization of Morley's theorem following Alain Connes's proof approach, where reflections across various lines play a central role.

### Dependencies
#### Definitions
- `rotate2d` - Rotation in the complex plane by a given angle
- `cnj` - Complex conjugation operator

### Porting notes
When porting this definition:
- Ensure that the target system has appropriate complex number operations, particularly rotation and conjugation
- Be mindful of function composition notation and order, as some systems might use different conventions
- This definition relies on complex numbers for its elegance; systems with different geometric foundations may need alternative approaches

---

## REFLECT2D_COMPOSE

### Name of formal statement
REFLECT2D_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT2D_COMPOSE = prove
 (`!s t. reflect2d s o reflect2d t = rotate2d (&2 * (s - t))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; reflect2d] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ROTATE2D_COMPLEX; CNJ_CEXP; CNJ_MUL; CNJ_CNJ] THEN
  REWRITE_TAC[CNJ_II; CNJ_CX; CNJ_NEG; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CEXP_ADD] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; CX_MUL] THEN
  AP_TERM_TAC THEN SIMPLE_COMPLEX_ARITH_TAC);;
```

### Informal statement
For any angles $s$ and $t$, the composition of two reflection operations in the plane is equivalent to a rotation:

$$\forall s, t. \text{reflect2d}(s) \circ \text{reflect2d}(t) = \text{rotate2d}(2 \cdot (s - t))$$

where:
- $\text{reflect2d}(t)$ represents a reflection across a line making angle $t$ with the positive x-axis
- $\text{rotate2d}(θ)$ represents a counterclockwise rotation by angle $θ$
- $\circ$ denotes function composition

### Informal proof
The proof demonstrates that composing two reflection operations with angles $s$ and $t$ is equivalent to a rotation by $2(s-t)$:

1. We begin by expanding the definition of `reflect2d`, where $\text{reflect2d}(t) = \text{rotate2d}(t) \circ \text{cnj} \circ \text{rotate2d}(-t)$

2. We rewrite the composition into its complex number representation:
   - $\text{rotate2d}(θ)$ corresponds to multiplication by $e^{iθ}$ in the complex plane
   - $\text{cnj}$ is the complex conjugate operation

3. We simplify using properties of complex conjugation:
   - $\overline{\overline{z}} = z$
   - $\overline{e^{it}} = e^{-it}$
   - $\overline{z_1 \cdot z_2} = \overline{z_1} \cdot \overline{z_2}$
   - $\overline{i} = -i$

4. Through algebraic manipulation of exponentials, we arrive at:
   $$\text{reflect2d}(s) \circ \text{reflect2d}(t) = \text{multiplication by } e^{i \cdot 2(s-t)}$$

5. Since multiplication by $e^{i \cdot 2(s-t)}$ is exactly the action of $\text{rotate2d}(2(s-t))$, the theorem is proven.

### Mathematical insight
This theorem captures a fundamental property in Euclidean geometry: the composition of two reflections across lines intersecting at an angle $\frac{θ}{2}$ is equivalent to a rotation by angle $θ$. The formula shows precisely that when we reflect across a line at angle $s$ and then across a line at angle $t$, the resulting transformation is a rotation by $2(s-t)$.

This is a special case of a more general principle in geometry where compositions of isometries produce other isometries, and where reflections serve as "generators" for the group of Euclidean isometries. Understanding this relationship is crucial in geometric transformation theory and crystallography.

The result also has an elegant interpretation in terms of complex numbers, where reflections and rotations have simple representations as operations on complex numbers.

### Dependencies
#### Definitions
- `reflect2d`: Reflection across a line at angle $t$, defined as $\text{reflect2d}(t) = \text{rotate2d}(t) \circ \text{cnj} \circ \text{rotate2d}(-t)$

#### Theorems and properties used
- `FUN_EQ_THM`: Function equality theorem
- `o_THM`: Function composition theorem
- `ROTATE2D_COMPLEX`: Complex representation of rotations
- Complex number properties: `CNJ_CEXP`, `CNJ_MUL`, `CNJ_CNJ`, `CNJ_II`, `CNJ_CX`, `CNJ_NEG`
- `CEXP_ADD`: Addition property of complex exponentials

### Porting notes
When porting this theorem:
1. Ensure that the definitions of `reflect2d` and `rotate2d` are correctly implemented in the target system
2. The theorem relies heavily on complex number theory, so make sure the target system has adequate complex number support
3. Some systems may represent geometric transformations via matrices rather than complex numbers, which would require reformulating the proof

---

## rotate_about

### rotate_about
- `rotate_about`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let rotate_about = new_definition
 `rotate_about a t x = a + rotate2d t (x - a)`;;
```

### Informal statement
The function `rotate_about` is defined as follows: For a point $a$, an angle $t$, and a point $x$, 
$$\text{rotate\_about}(a, t, x) = a + \text{rotate2d}(t, x - a)$$

This defines the rotation of point $x$ around point $a$ by angle $t$. It works by:
1. Translating $x$ to the origin by subtracting $a$: $(x - a)$
2. Rotating the translated point by angle $t$ using the `rotate2d` function
3. Translating back by adding $a$ to the result

### Informal proof
(No proof needed as this is a definition)

### Mathematical insight
This definition implements a standard way to rotate a point around an arbitrary center point in 2D space. The key insight is to:

1. First translate the coordinate system so that the center of rotation becomes the origin
2. Apply a standard rotation around the origin
3. Translate the coordinate system back

This approach is canonical in computer graphics, robotics, and computational geometry when implementing rotations around arbitrary points. The definition leverages the existing `rotate2d` function which presumably handles rotation around the origin.

The definition is important because it generalizes rotation from being around the origin to being around any arbitrary point in the plane, which is essential for many geometric constructions and transformations.

### Dependencies
- Definitions:
  - `rotate2d`: Function that rotates a point around the origin by a given angle

### Porting notes
When porting this definition:
- Ensure that the target system has a corresponding definition for `rotate2d`
- The definition uses vector addition and subtraction, so ensure these operations are properly defined in the target system
- Pay attention to the order of arguments and the convention for angle measurement (radians vs degrees) used in the target system's rotation functions

---

## reflect_across

### Name of formal statement
reflect_across

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let reflect_across = new_definition
 `reflect_across (a,b) x = a + reflect2d (Arg(b - a)) (x - a)`;;
```

### Informal statement
`reflect_across (a,b) x` defines the reflection of point `x` across the line passing through points `a` and `b` in the complex plane. 

Mathematically, it is defined as:
$$\text{reflect\_across}(a,b)(x) = a + \text{reflect2d}(\text{Arg}(b-a))(x-a)$$

where:
- `a` and `b` are points in the complex plane defining a line
- `x` is the point to be reflected
- `Arg(b-a)` gives the angle of the vector from `a` to `b`
- `reflect2d` is a predefined reflection operation that reflects a point around a line through the origin at a specified angle

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition formalizes the geometric operation of reflecting a point across a line in the complex plane. The key insight is breaking down the reflection into several steps:

1. Translate the configuration so that point `a` is at the origin
2. Perform a rotation determined by the angle of the line (a,b)
3. Apply complex conjugation (which reflects across the real axis)
4. Rotate back
5. Translate back to the original position

This approach is elegant because it reduces the reflection across any line to a sequence of basic transformations (translations, rotations, and reflection across the real axis). The underlying function `reflect2d` handles the middle three steps, while this definition accounts for the translations.

The operation is useful in various geometric constructions and proofs, particularly in computational geometry and when working with triangles and other polygons in the complex plane.

### Dependencies
#### Definitions
- `reflect2d`: Reflects a point around a line through the origin at a specified angle

### Porting notes
When porting to another system:
- Ensure that complex numbers are properly supported
- Verify that the `Arg` function (argument of a complex number) is available
- Check that function composition (`o`) works as expected with complex-valued functions

---

## REFLECT_ACROSS_COMPOSE

### Name of formal statement
REFLECT_ACROSS_COMPOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE = prove
 (`!a b c.
        ~(b = a) /\ ~(c = a)
        ==> reflect_across(a,b) o reflect_across(a,c) =
            rotate_about a (&2 * Arg((b - a) / (c - a)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[reflect_across; FUN_EQ_THM; o_THM; rotate_about] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] REFLECT2D_COMPOSE] THEN
  X_GEN_TAC `x:complex` THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_2; ROTATE2D_ADD] THEN
  ASM_SIMP_TAC[ROTATE2D_SUB_ARG; COMPLEX_SUB_0]);;
```

### Informal statement
For any points $a$, $b$, and $c$ in the complex plane, if $b \neq a$ and $c \neq a$, then the composition of reflection across the line through points $a$ and $b$ followed by reflection across the line through points $a$ and $c$ is equivalent to rotation about point $a$ by angle $2 \cdot \text{Arg}\left(\frac{b-a}{c-a}\right)$.

Formally:
$$\forall a, b, c. \; (b \neq a) \land (c \neq a) \Rightarrow \text{reflect\_across}(a,b) \circ \text{reflect\_across}(a,c) = \text{rotate\_about } a \left(2 \cdot \text{Arg}\left(\frac{b-a}{c-a}\right)\right)$$

### Informal proof
We need to prove that the composition of two reflections equals a rotation.

- First, we apply the definitions of `reflect_across` and function composition, and simplify:
  - `reflect_across(a,b)(x) = a + reflect2d(Arg(b-a))(x-a)`
  - `reflect_across(a,c)(x) = a + reflect2d(Arg(c-a))(x-a)`
  
- We also use the definition of `rotate_about`: 
  - `rotate_about a t x = a + rotate2d t (x-a)`

- After applying these definitions and simplifying vector arithmetic expressions like `(a + x) - a = x`, we need to show that:
  - `reflect2d(Arg(b-a)) ∘ reflect2d(Arg(c-a))` = `rotate2d(2 * Arg((b-a)/(c-a)))`

- We apply the theorem `REFLECT2D_COMPOSE` which states that the composition of two reflections gives a rotation:
  - `reflect2d s ∘ reflect2d t = rotate2d(2 * (s - t))`
  
- Setting `s = Arg(b-a)` and `t = Arg(c-a)`, we get:
  - `reflect2d(Arg(b-a)) ∘ reflect2d(Arg(c-a)) = rotate2d(2 * (Arg(b-a) - Arg(c-a)))`

- Finally, we use the property that `Arg(z₁) - Arg(z₂) = Arg(z₁/z₂)` when dealing with non-zero complex numbers.
  - Since $b \neq a$ and $c \neq a$ (by our assumptions), we can apply this property:
  - `Arg(b-a) - Arg(c-a) = Arg((b-a)/(c-a))`

- Therefore, `reflect2d(Arg(b-a)) ∘ reflect2d(Arg(c-a)) = rotate2d(2 * Arg((b-a)/(c-a)))`, which completes our proof.

### Mathematical insight
This theorem captures a fundamental property in Euclidean geometry: the composition of two reflections across lines that intersect at a point is equivalent to a rotation about that point. The angle of rotation is twice the angle between the two lines of reflection.

In the complex plane, this becomes elegant: when we reflect across lines through the origin, we're applying operations of the form `reflect2d θ`, where θ is the angle the line makes with the positive real axis. The theorem shows that when the lines intersect at an arbitrary point `a` (not necessarily the origin), we can reduce the problem to reflections through the origin by translating, applying the reflections, and translating back.

The angle of rotation, `2 * Arg((b-a)/(c-a))`, has a clear geometric interpretation: `Arg(b-a)` is the angle of the line through `a` and `b`, `Arg(c-a)` is the angle of the line through `a` and `c`, and their difference gives the angle between these lines. Multiplying by 2 gives the angle of rotation resulting from the composition of reflections.

### Dependencies
- **Theorems**:
  - `REFLECT2D_COMPOSE`: Composition of two reflections is a rotation
- **Definitions**:
  - `rotate_about`: Rotation about a point
  - `reflect_across`: Reflection across a line defined by two points

### Porting notes
When porting this theorem:
1. Ensure that complex number operations (especially `Arg`) are properly defined in the target system
2. Check that the reflection and rotation operations have equivalent definitions
3. The use of `ASM_SIMP_TAC` with `ROTATE2D_SUB_ARG` and `COMPLEX_SUB_0` indicates properties about argument differences of complex numbers that might need to be proven separately

---

## REFLECT_ACROSS_COMPOSE_ANGLE

### REFLECT_ACROSS_COMPOSE_ANGLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE_ANGLE = prove
 (`!a b c.
        ~(b = a) /\ ~(c = a) /\ &0 <= Im((c - a) / (b - a))
        ==> reflect_across(a,c) o reflect_across(a,b) =
            rotate_about a (&2 * angle(c,a,b))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ANGLE_SYM] THEN
  ASM_SIMP_TAC[REFLECT_ACROSS_COMPOSE] THEN
  ASM_SIMP_TAC[angle; VECTOR_ANGLE_ARG; COMPLEX_SUB_0;
               REAL_SUB_ARG; ARG_LE_PI]);;
```

### Informal statement
For any points $a$, $b$, and $c$ in the complex plane, if $b \neq a$, $c \neq a$, and $\text{Im}\left(\frac{c-a}{b-a}\right) \geq 0$, then the composition of reflections 
$\text{reflect\_across}(a,c) \circ \text{reflect\_across}(a,b) = \text{rotate\_about } a (2 \cdot \text{angle}(c,a,b))$.

This means that composing the reflection across line $\overrightarrow{ac}$ with the reflection across line $\overrightarrow{ab}$ is equivalent to rotation about point $a$ by twice the angle between vectors $\overrightarrow{ab}$ and $\overrightarrow{ac}$.

### Informal proof
The proof proceeds as follows:

* First, we apply the symmetry property of angles by using `ANGLE_SYM`, which states that $\text{angle}(c,a,b) = \text{angle}(b,a,c)$.

* Then, we apply the theorem `REFLECT_ACROSS_COMPOSE`, which states that when $b \neq a$ and $c \neq a$, we have:
  $\text{reflect\_across}(a,b) \circ \text{reflect\_across}(a,c) = \text{rotate\_about } a (2 \cdot \text{Arg}(\frac{b-a}{c-a}))$

* Since we're proving a formula for $\text{reflect\_across}(a,c) \circ \text{reflect\_across}(a,b)$ (note the order is reversed from `REFLECT_ACROSS_COMPOSE`), we need to relate the expression $\text{Arg}(\frac{b-a}{c-a})$ to $\text{angle}(c,a,b)$.

* Using the definition of angle and the properties of the `Arg` function, we have:
  - By definition, $\text{angle}(c,a,b) = \text{vector\_angle}(b-a, c-a)$
  - The theorem `VECTOR_ANGLE_ARG` tells us that when both vectors are non-zero, 
    $\text{vector\_angle}(w,z) = \begin{cases} 
    \text{Arg}(z/w) & \text{if } \text{Im}(z/w) \geq 0 \\
    2\pi - \text{Arg}(z/w) & \text{otherwise}
    \end{cases}$
  
* In our case, with $w = b-a$ and $z = c-a$, and given that $\text{Im}((c-a)/(b-a)) \geq 0$ (one of our assumptions), we have:
  $\text{vector\_angle}(b-a, c-a) = \text{Arg}((c-a)/(b-a)) = \text{Arg}(\frac{c-a}{b-a})$

* By the property of the argument function `REAL_SUB_ARG`, we have:
  $\text{Arg}(\frac{b-a}{c-a}) = -\text{Arg}(\frac{c-a}{b-a})$

* Additionally, since $\text{Im}((c-a)/(b-a)) \geq 0$, we know that $\text{Arg}(\frac{c-a}{b-a}) \leq \pi$ by the theorem `ARG_LE_PI`.

* Therefore, $\text{reflect\_across}(a,c) \circ \text{reflect\_across}(a,b) = \text{rotate\_about } a (2 \cdot \text{angle}(c,a,b))$, which is what we wanted to prove.

### Mathematical insight
This theorem establishes a fundamental relationship between reflections and rotations in the complex plane. It shows that composing two reflections across lines passing through a common point results in a rotation about that point. The angle of rotation is twice the angle between the two reflection lines.

This result is important in geometric transformations and has applications in various areas of mathematics, including group theory (where it relates to the structure of the orthogonal group) and geometric constructions. It also illustrates how complex operations can often be decomposed into simpler ones, or conversely, how complex transformations can be built by composing simpler ones.

The condition $\text{Im}((c-a)/(b-a)) \geq 0$ ensures that we're working with the standard orientation of the angle between the vectors, which simplifies the relationship between the argument function and the angle function.

### Dependencies
**Theorems:**
- `VECTOR_ANGLE_ARG`: Relates the vector angle to the argument function
- `REFLECT_ACROSS_COMPOSE`: Describes the composition of two reflections in terms of rotation
- `ANGLE_SYM`: Symmetry property of angles
- `ARG_LE_PI`: A property of the argument function
- `REAL_SUB_ARG`: Property of the argument function for division

**Definitions:**
- `rotate_about`: Defines rotation about a point
- `reflect_across`: Defines reflection across a line
- `angle`: Defines the angle between vectors

### Porting notes
When porting this theorem:
1. Ensure that your definitions of reflection and rotation match HOL Light's. In particular, note that `reflect_across(a,b)` reflects across the line through points a and b, and `rotate_about a t` rotates around point a by angle t.
2. The condition $\text{Im}((c-a)/(b-a)) \geq 0$ is important for the orientation of the angle. Some systems might handle angles differently, requiring adjustment.
3. The use of complex numbers for 2D geometry might require adaptation if your target system uses a different representation for 2D points.

---

## REFLECT_ACROSS_COMPOSE_INVOLUTION

### REFLECT_ACROSS_COMPOSE_INVOLUTION
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_COMPOSE_INVOLUTION = prove
 (`!a b. ~(a = b) ==> reflect_across(a,b) o reflect_across(a,b) = I`,
  SIMP_TAC[REFLECT_ACROSS_COMPOSE; COMPLEX_DIV_REFL; COMPLEX_SUB_0] THEN
  REWRITE_TAC[ARG_NUM; REAL_MUL_RZERO; rotate_about; FUN_EQ_THM] THEN
  REWRITE_TAC[ROTATE2D_ZERO; I_THM] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;
```

### Informal statement
For any complex points $a$ and $b$ where $a \neq b$, the composition of reflection across the line through $a$ and $b$ with itself is the identity function. Formally:

$$\forall a, b. \; a \neq b \Rightarrow \text{reflect\_across}(a,b) \circ \text{reflect\_across}(a,b) = I$$

where $\text{reflect\_across}(a,b)$ is the reflection across the line passing through points $a$ and $b$, and $I$ is the identity function.

### Informal proof
The proof uses the compositional property of reflections given by `REFLECT_ACROSS_COMPOSE`. 

1. We apply `REFLECT_ACROSS_COMPOSE`, which states that composing two reflections through lines sharing point $a$ yields a rotation about $a$.
2. When the two reflection lines are identical (as in our case), the angle of rotation becomes:
   $$2 \cdot \text{Arg}\left(\frac{b-a}{b-a}\right)$$

3. Since $a \neq b$, we have $b-a \neq 0$, so $\frac{b-a}{b-a} = 1$
4. Using `ARG_NUM`, we know that $\text{Arg}(1) = 0$, making the rotation angle $2 \cdot 0 = 0$
5. A rotation by angle 0 is the identity transformation, so:
   $$\text{rotate\_about}(a, 0)(x) = a + \text{rotate2d}(0)(x-a) = a + (x-a) = x$$

Therefore, composing the reflection with itself yields the identity function.

### Mathematical insight
This theorem establishes the fundamental property that reflection is an involution - applying it twice returns to the original state. This is a key property of reflections in geometry and is essential for understanding the geometric transformations in the complex plane.

The theorem leverages the more general result that composing two reflections yields a rotation, but in the special case where the reflection lines are identical, the rotation angle becomes zero, resulting in the identity transformation.

This result is part of the foundational properties of the group structure of geometric transformations in the complex plane.

### Dependencies
- Theorems:
  - `REFLECT_ACROSS_COMPOSE`: Composition of two reflections across lines through a common point is a rotation
  - `COMPLEX_DIV_REFL`: $\frac{z}{z} = 1$ for non-zero complex number $z$
  - `COMPLEX_SUB_0`: Conditions for when a complex subtraction equals zero
  - `ARG_NUM`: Argument of the complex number 1 is 0
  - `ROTATE2D_ZERO`: Rotation by angle 0 is identity

- Definitions:
  - `reflect_across`: Reflection across a line through two points in the complex plane
  - `rotate_about`: Rotation about a point by a given angle

### Porting notes
When porting this theorem to other proof assistants:
1. Ensure that complex number operations and geometric transformations (reflection and rotation) are properly defined
2. The definition of argument (`Arg`) for complex numbers may vary between systems
3. The representation of the identity function (`I`) might differ between systems

AI Assistant: I'll translate the HOL Light formal content into structured mathematical English documentation as requested.

---

## REFLECT_ACROSS_SYM

### REFLECT_ACROSS_SYM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REFLECT_ACROSS_SYM = prove
 (`!a b. reflect_across(a,b) = reflect_across(b,a)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a:complex = b` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; reflect_across; reflect2d; o_THM] THEN
  REWRITE_TAC[ROTATE2D_COMPLEX; CNJ_CEXP; CNJ_MUL; CNJ_CX; CNJ_II] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_RING `--ii * --z = ii * z`] THEN
  SUBGOAL_THEN `cexp(ii * Cx(Arg(b - a))) = (b - a) / Cx(norm(b - a)) /\
                cexp(ii * Cx(Arg(a - b))) = (a - b) / Cx(norm(a - b))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(COMPLEX_FIELD
     `~(a = Cx(&0)) /\ a * b = c ==> b = c / a`) THEN
    ASM_REWRITE_TAC[GSYM ARG; CX_INJ; NORM_EQ_0; VECTOR_SUB_EQ];
    REWRITE_TAC[COMPLEX_RING `a * a * cnj b = a pow 2 * cnj b`] THEN
    SUBST1_TAC(ISPECL [`a:complex`; `b:complex`] NORM_SUB) THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[complex_div] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `b - a = ((b - a) * n) pow 2 * (cnj za - cnj zb)
      ==> a + ((b - a) * n) pow 2 * cnj za =
          b + ((a - b) * n) pow 2 * cnj zb`) THEN
    REWRITE_TAC[CNJ_SUB; COMPLEX_RING `(z - a) - (z - b):complex = b - a`] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `(b' - a') * (b - a) = n pow 2 /\ ~(n = Cx(&0))
      ==> b - a = ((b - a) * inv n) pow 2 * (b' - a')`) THEN
    REWRITE_TAC[GSYM CNJ_SUB; COMPLEX_MUL_CNJ; CX_INJ] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; COMPLEX_SUB_0]]);;
```

### Informal statement
For any two complex numbers $a$ and $b$, the reflection across the line through points $a$ and $b$ is the same as the reflection across the line through points $b$ and $a$:

$$\forall a, b \in \mathbb{C},\ \text{reflect\_across}(a, b) = \text{reflect\_across}(b, a)$$

where $\text{reflect\_across}(a, b)$ represents the reflection transformation across the line passing through complex points $a$ and $b$.

### Informal proof
We prove that for any complex numbers $a$ and $b$, the reflection across the line through $a$ and $b$ is the same as the reflection across the line through $b$ and $a$.

* First, we handle the trivial case where $a = b$. In this case, both sides are equal by simple rewriting.

* For the non-trivial case where $a \neq b$, we rewrite using the function equality theorem and expand the definition of `reflect_across` and `reflect2d`.

* After simplifying with rotation and complex conjugation properties, we need to show that 
  $e^{i \cdot \text{Arg}(b-a)} = \frac{b-a}{\text{norm}(b-a)}$ and 
  $e^{i \cdot \text{Arg}(a-b)} = \frac{a-b}{\text{norm}(a-b)}$.

* These equalities follow from the definition of the complex argument function and properties of complex division.

* Finally, we use algebraic manipulation with complex numbers to show that, for any complex $z$:
  $$a + \text{reflect2d}(\text{Arg}(b-a))(z-a) = b + \text{reflect2d}(\text{Arg}(a-b))(z-b)$$

* This equality holds because reflecting across a line is independent of which direction we consider the line, which follows from properties of complex conjugation and the fact that $a-b = -(b-a)$.

### Mathematical insight
This theorem establishes the natural symmetry property of reflection: the reflection across a line is the same operation regardless of how we orient the line. In terms of the reflection operator defined by two points, this means the order of the points doesn't matter.

This symmetry is geometrically intuitive - a reflection across a line should depend only on the line itself, not on how we parameterize it. The proof formalizes this intuition by working with the complex number representations and showing that the different parameterizations give the same transformation.

The theorem is particularly useful when working with reflections in plane geometry, providing flexibility in how we specify reflections.

### Dependencies
- Definitions:
  - `reflect2d` - Reflection in 2D using complex numbers parametrized by an angle
  - `reflect_across` - Reflection across a line through two points in the complex plane

### Porting notes
When porting this theorem, pay attention to:
1. How complex numbers and their operations (conjugation, division, etc.) are represented
2. The definition of reflection in terms of complex numbers
3. The argument function (Arg) and norm function in the target system

The proof relies on algebraic manipulations of complex numbers, so the target system should have good support for complex arithmetic.

---

## ITER_ROTATE_ABOUT

### Name of formal statement
ITER_ROTATE_ABOUT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ITER_ROTATE_ABOUT = prove
 (`!n a t. ITER n (rotate_about a t) = rotate_about a (&n * t)`,
  REWRITE_TAC[FUN_EQ_THM; rotate_about] THEN
  REWRITE_TAC[VECTOR_ARITH `a + b:real^N = a + c <=> b = c`] THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER_ALT; REAL_MUL_LZERO; ROTATE2D_ZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x - a:real^N = x`; GSYM REAL_OF_NUM_SUC] THEN
  ASM_REWRITE_TAC[REAL_ADD_RDISTRIB; ROTATE2D_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[rotate_about; REAL_MUL_LID] THEN VECTOR_ARITH_TAC);;
```

### Informal statement
For any natural number $n$, point $a$ in the plane, and angle $t$, iterating the rotation about point $a$ by angle $t$ exactly $n$ times is equivalent to rotating about point $a$ by angle $n \cdot t$.

Formally:
$$\forall n, a, t. \text{ITER}(n, \text{rotate\_about}(a, t)) = \text{rotate\_about}(a, n \cdot t)$$

where:
- $\text{ITER}(n, f)$ represents the $n$-fold iteration of function $f$
- $\text{rotate\_about}(a, t)$ represents rotation around point $a$ by angle $t$

### Informal proof
We prove that iterating a rotation about a point $n$ times is equivalent to performing a single rotation by $n$ times the angle.

First, we use function extensionality to show that two functions are equal if they produce the same outputs for all inputs. After rewriting with the definition of `rotate_about`, we simplify the vector expression to focus on the essential parts.

The proof proceeds by induction on $n$:

- Base case ($n = 0$): 
  When $n = 0$, $\text{ITER}(0, \text{rotate\_about}(a, t)) = \text{id}$ by definition of ITER.
  Also, $\text{rotate\_about}(a, 0 \cdot t) = \text{rotate\_about}(a, 0) = \text{id}$ since rotation by 0 is the identity.

- Inductive step:
  Assuming the result holds for $n$, we show it for $n+1$:
  $$\text{ITER}(n+1, \text{rotate\_about}(a, t)) = \text{rotate\_about}(a, (n+1) \cdot t)$$
  
  Using the alternative characterization of ITER and substituting $(n+1)$ with $\text{SUC}(n)$, we get:
  $$\text{ITER}(\text{SUC}(n), \text{rotate\_about}(a, t)) = \text{ITER}(n, \text{rotate\_about}(a, t))(\text{rotate\_about}(a, t))$$
  
  By the induction hypothesis and properties of rotation, this equals:
  $$\text{rotate\_about}(a, n \cdot t)(\text{rotate\_about}(a, t)) = \text{rotate\_about}(a, n \cdot t + t) = \text{rotate\_about}(a, (n+1) \cdot t)$$
  
  The final step uses the fact that rotating by angle $\alpha$ followed by angle $\beta$ is equivalent to rotating by angle $\alpha + \beta$.

### Mathematical insight
This theorem establishes a fundamental property of iterated rotations around a fixed point. It shows that composing rotations around the same center is equivalent to a single rotation by the sum of angles. This is a key geometric property that enables efficient calculation of multiple rotations without having to perform each rotation step sequentially.

The result belongs to the broader class of theorems about group actions, as rotations form a group and act on the plane. The theorem expresses how powers of a group element (rotation by angle t) correspond to the group operation (multiplication of angles).

### Dependencies
- **Theorems**:
  - `ITER_ALT`: Provides an alternative characterization of ITER for inductive proofs.

- **Definitions**:
  - `ITER`: Defines function iteration, where ITER n f is the n-fold composition of f.
  - `rotate_about`: Defines rotation of point x around point a by angle t.

### Porting notes
When porting to another system:
- Ensure the target system has appropriate vector operations and definitions for 2D rotations.
- The proof relies on algebraic properties of vector operations and rotations, so built-in vector automation (like HOL Light's VECTOR_ARITH_TAC) may need to be replaced with explicit vector algebra in systems lacking similar automation.
- The iteration operator (ITER) is a common utility in many proof assistants but might have a different name or slightly different definition.

---

## REAL_LE_IM_DIV_CYCLIC

### Name of formal statement
REAL_LE_IM_DIV_CYCLIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_LE_IM_DIV_CYCLIC = prove
 (`!a b c. &0 <= Im ((c - a) / (b - a)) <=> &0 <= Im((a - b) / (c - b))`,
  REWRITE_TAC[IM_COMPLEX_DIV_GE_0] THEN
  REWRITE_TAC[complex_mul; IM; IM_SUB; RE_SUB; IM_CNJ; CNJ_SUB; RE_CNJ] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any complex numbers $a$, $b$, and $c$, the following equivalence holds:
$$0 \leq \text{Im}\left(\frac{c - a}{b - a}\right) \iff 0 \leq \text{Im}\left(\frac{a - b}{c - b}\right)$$

where $\text{Im}(z)$ denotes the imaginary part of the complex number $z$.

### Informal proof
The proof proceeds by algebraic manipulation of both sides of the equivalence:

1. First, we rewrite the statement using the theorem `IM_COMPLEX_DIV_GE_0` which provides a way to characterize when the imaginary part of a complex division is non-negative.

2. Then, we further rewrite using rules for:
   - Complex multiplication (`complex_mul`)
   - Extracting imaginary parts (`IM`)
   - Imaginary parts of differences (`IM_SUB`)
   - Real parts of differences (`RE_SUB`)
   - Imaginary parts of complex conjugates (`IM_CNJ`)
   - Complex conjugates of differences (`CNJ_SUB`)
   - Real parts of complex conjugates (`RE_CNJ`)

3. After these rewritings, the problem reduces to a real arithmetic statement which is solved by the automated tactic `REAL_ARITH_TAC`.

The key insight is that the expressions $\text{Im}\left(\frac{c - a}{b - a}\right)$ and $\text{Im}\left(\frac{a - b}{c - b}\right)$ can be expanded into equivalent real arithmetic expressions, which can be proven equal through standard algebraic manipulation.

### Mathematical insight
This theorem demonstrates a cyclic property of the imaginary part of complex ratios. It shows that rotating the arguments in the specific pattern shown preserves the sign of the imaginary part. This has geometric significance in the complex plane, particularly in relation to angles and orientations.

The result is especially useful in computational geometry and complex analysis contexts, where determining the orientation or angle relationships between points is important. It represents a type of invariant in the cyclic permutation of points in certain complex-valued expressions.

### Dependencies
- `IM_COMPLEX_DIV_GE_0`: Characterizes when the imaginary part of a complex division is non-negative
- `complex_mul`: Definition of complex multiplication
- `IM`: Function extracting the imaginary part of a complex number
- `IM_SUB`: Theorem about imaginary parts of differences
- `RE_SUB`: Theorem about real parts of differences
- `IM_CNJ`: Theorem about imaginary parts of complex conjugates
- `CNJ_SUB`: Theorem about complex conjugates of differences
- `RE_CNJ`: Theorem about real parts of complex conjugates
- `REAL_ARITH_TAC`: Automated tactic for solving real arithmetic problems

---

## ROTATE_ABOUT_INVERT

### ROTATE_ABOUT_INVERT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ROTATE_ABOUT_INVERT = prove
 (`rotate_about a t w = z <=> w = rotate_about a (--t) z`,
  MATCH_MP_TAC(MESON[]
   `(!x. f(g x) = x) /\ (!y. g(f y) = y)
    ==> (f x = y <=> x = g y)`) THEN
  REWRITE_TAC[rotate_about; VECTOR_ADD_SUB; GSYM ROTATE2D_ADD] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_RINV] THEN
  REWRITE_TAC[ROTATE2D_ZERO] THEN VECTOR_ARITH_TAC);;
```

### Informal statement

For any point $a$, angle $t$, and points $w$ and $z$ in the plane, the following are equivalent:
- $\text{rotate\_about}(a, t, w) = z$
- $w = \text{rotate\_about}(a, -t, z)$

where $\text{rotate\_about}(a, t, x)$ is the rotation of point $x$ around point $a$ by angle $t$.

### Informal proof

The proof establishes that rotation about a point $a$ by angle $t$ and rotation about the same point by angle $-t$ are inverse operations. The proof proceeds as follows:

- First, we apply a general lemma that states if functions $f$ and $g$ are inverses of each other (i.e., $f(g(x)) = x$ and $g(f(y)) = y$ for all $x$ and $y$), then $f(x) = y$ if and only if $x = g(y)$.

- We then expand the definition of `rotate_about`:
  $\text{rotate\_about}(a, t, x) = a + \text{rotate2d}(t, x - a)$
  
- Using vector arithmetic properties, we show that:
  $\text{rotate\_about}(a, t, \text{rotate\_about}(a, -t, z)) = z$ and 
  $\text{rotate\_about}(a, -t, \text{rotate\_about}(a, t, w)) = w$

- This involves using the fact that the rotation functions `rotate2d(t)` and `rotate2d(-t)` are inverses of each other, which can be expressed using `ROTATE2D_ADD` with the property that $\text{rotate2d}(t + (-t)) = \text{rotate2d}(0)$, and $\text{rotate2d}(0)$ is the identity function.

- The proof is completed using vector arithmetic to simplify the expressions.

### Mathematical insight
This theorem formalizes the intuitive property that rotating a point around a center by an angle, and then rotating back by the negative of that angle returns the original point. In other words, it shows that `rotate_about` with angle $t$ and `rotate_about` with angle $-t$ are inverse operations. This is a fundamental property of rotations in the plane and is essential for reasoning about geometric transformations.

The result is analogous to the property that rotation matrices are orthogonal, meaning their inverse is equal to their transpose. In this case, the inverse operation to rotating by angle $t$ is rotating by angle $-t$.

### Dependencies
- Definitions:
  - `rotate_about`: Rotation of a point around another point by a given angle.

- Theorems (implicitly used):
  - `VECTOR_ADD_SUB`: Vector arithmetic property
  - `GSYM ROTATE2D_ADD`: Property relating to the composition of rotations
  - `REAL_ADD_LINV`, `REAL_ADD_RINV`: Properties of real number addition
  - `ROTATE2D_ZERO`: Property that rotation by angle 0 is the identity function

### Porting notes
When porting this theorem:
- Ensure that the rotation functions are defined with the same conventions regarding angle direction (clockwise or counterclockwise).
- The proof relies heavily on properties of vector arithmetic and rotation composition, so these properties need to be established first.
- The MESON tactic in HOL Light is a powerful automated reasoning tool. In other proof assistants, a more explicit approach might be needed to establish the inverse relationship between the rotations.

---

## ROTATE_EQ_REFLECT_LEMMA

### Name of formal statement
ROTATE_EQ_REFLECT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ROTATE_EQ_REFLECT_LEMMA = prove
 (`!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = t
        ==> rotate_about a t z = reflect_across (a,b) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rotate_about; reflect_across] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ROTATE2D_COMPLEX; reflect2d; o_THM] THEN
  REWRITE_TAC[CNJ_MUL; COMPLEX_MUL_ASSOC; CNJ_CEXP; CNJ_II] THEN
  REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG;
              GSYM CEXP_ADD; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_RING `ii * a + ii * a = ii * Cx(&2) * a`] THEN
  ASM_CASES_TAC `z:complex = a` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (COMPLEX_RING
   `~(z = a)
    ==> c * (z - a) pow 2 = b * cnj (z - a) * (z - a)
        ==> c * (z - a) = b * cnj(z - a)`)) THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [ARG] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `(e1:complex) * e2 pow 2 = e3 ==> e1 * (n * e2) pow 2 = e3 * n pow 2`) THEN
  REWRITE_TAC[GSYM CEXP_ADD; GSYM CEXP_N; CEXP_EQ] THEN
  REWRITE_TAC[COMPLEX_RING
   `ii * t + Cx(&2) * ii * z = ii * u + v * ii <=>
    t + Cx(&2) * z - u = v`] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB; GSYM CX_ADD; CX_INJ] THEN
  EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `&2 * a = &2 * b <=> a = b`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + (b - c):real = a - (c - b)`] THEN
  ASM_SIMP_TAC[REAL_SUB_ARG; COMPLEX_SUB_0] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `&0`; EXISTS_TAC `&2`] THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;
```

### Informal statement
For any complex points $a$, $b$, $z$, and angle $t$, if $b \neq a$ and $2 \cdot \text{Arg}((b - a) / (z - a)) = t$, then rotating $z$ about point $a$ by angle $t$ is equivalent to reflecting $z$ across the line determined by points $a$ and $b$.

Formally:
$$\forall a, b, z, t. \, (b \neq a) \land (2 \cdot \text{Arg}((b - a) / (z - a)) = t) \Rightarrow \text{rotate\_about}(a, t, z) = \text{reflect\_across}((a,b), z)$$

### Informal proof
We want to show that under the given conditions, rotating $z$ around $a$ by angle $t$ gives the same result as reflecting $z$ across the line passing through $a$ and $b$.

* First, we expand the definitions of `rotate_about` and `reflect_across`:
  - $\text{rotate\_about}(a, t, z) = a + \text{rotate2d}(t)(z - a)$
  - $\text{reflect\_across}((a,b), z) = a + \text{reflect2d}(\text{Arg}(b - a))(z - a)$

* It suffices to show that $\text{rotate2d}(t)(z - a) = \text{reflect2d}(\text{Arg}(b - a))(z - a)$

* We expand the definition of `reflect2d` and related complex operations:
  - $\text{reflect2d}(t) = \text{rotate2d}(t) \circ \text{cnj} \circ \text{rotate2d}(-t)$
  - $\text{rotate2d}(t)(w) = e^{i t} \cdot w$

* After expanding these definitions and applying complex number properties (conjugation, multiplication, exponentiation), we need to prove that:
  $$e^{it} \cdot (z - a) = e^{i \cdot \text{Arg}(b - a)} \cdot \overline{e^{-i \cdot \text{Arg}(b - a)} \cdot (z - a)}$$

* For the special case where $z = a$, both sides reduce to $0$, so the equation holds trivially.

* For the case where $z \neq a$, we apply complex algebraic manipulations to show that:
  $$e^{it} \cdot (z - a) = e^{i \cdot \text{Arg}(b - a)} \cdot \overline{e^{-i \cdot \text{Arg}(b - a)}} \cdot \overline{(z - a)}$$

* Using the given condition that $t = 2 \cdot \text{Arg}((b - a) / (z - a))$, we simplify further.

* Applying properties of the argument function and complex exponentiation, we verify the result holds for all possible cases of $z$, $a$, and $b$ (when $b \neq a$).

### Mathematical insight
This lemma establishes a fundamental connection between rotation and reflection in the complex plane. Specifically, it shows that under a particular angle condition, rotating a point around another point is equivalent to reflecting it across a line. This is a key geometric property that's often used in complex analysis and computational geometry.

The condition $2 \cdot \text{Arg}((b - a) / (z - a)) = t$ geometrically means that the angle $t$ is twice the angle between the line from $a$ to $b$ and the line from $a$ to $z$. This is precisely the condition under which a rotation equals a reflection.

This result is part of the classical theory of Möbius transformations and connects rotation and reflection operations in a way that simplifies many geometric arguments in the complex plane.

### Dependencies
#### Definitions
- `rotate2d`: Rotation in the complex plane by an angle t
- `rotate_about`: Rotation of a point x around point a by angle t
- `reflect_across`: Reflection of a point across a line defined by two points
- `reflect2d`: Reflection in the complex plane with respect to an angle

### Porting notes
When porting this theorem:
- Ensure the complex number representation and operations (conjugation, argument, etc.) are properly defined in the target system
- Pay attention to how the argument function (`Arg`) is defined, especially regarding its domain and range
- The proof relies heavily on complex number algebra and properties of complex exponentiation
- Consider using a library for complex geometric operations if available in the target system

---

## ROTATE_EQ_REFLECT_PI_LEMMA

### Name of formal statement
ROTATE_EQ_REFLECT_PI_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ROTATE_EQ_REFLECT_PI_LEMMA = prove
 (`!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = &4 * pi + t
        ==> rotate_about a t z = reflect_across (a,b) z`,
  REWRITE_TAC[REAL_ARITH `a = &4 * pi + t <=> t = a + --(&4 * pi)`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rotate_about a (&2 * Arg((b - a) / (z - a))) z` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC ROTATE_EQ_REFLECT_LEMMA THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[rotate_about; ROTATE2D_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  REWRITE_TAC[EULER; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; COS_NEG; SIN_NEG] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; REAL_EXP_NEG; REAL_EXP_0; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID]);;
```

### Informal statement
For any complex points $a$, $b$, $z$ and any real number $t$, if $b \neq a$ and $2 \cdot \text{Arg}(\frac{b-a}{z-a}) = 4\pi + t$, then rotating $z$ about point $a$ by angle $t$ is equivalent to reflecting $z$ across the line passing through points $a$ and $b$. 

In mathematical notation:
$$\forall a, b, z \in \mathbb{C}, \forall t \in \mathbb{R}. (b \neq a) \land (2 \cdot \text{Arg}((b-a)/(z-a)) = 4\pi + t) \implies \text{rotate\_about}(a, t, z) = \text{reflect\_across}((a, b), z)$$

### Informal proof
The proof proceeds by rewriting the condition and applying previous results about rotations and reflections:

1. First, rewrite the condition $2 \cdot \text{Arg}(\frac{b-a}{z-a}) = 4\pi + t$ as $t = 2 \cdot \text{Arg}(\frac{b-a}{z-a}) - 4\pi$ using the arithmetic property $a = 4\pi + t \iff t = a - 4\pi$.

2. The goal is to prove that $\text{rotate\_about}(a, t, z) = \text{reflect\_across}((a, b), z)$.

3. Apply transitivity of equality with the intermediate expression $\text{rotate\_about}(a, 2 \cdot \text{Arg}(\frac{b-a}{z-a}), z)$.

4. For the second part of the equality chain, apply the previously proven `ROTATE_EQ_REFLECT_LEMMA`, which states that if $b \neq a$ and $2 \cdot \text{Arg}(\frac{b-a}{z-a}) = t$, then $\text{rotate\_about}(a, t, z) = \text{reflect\_across}((a, b), z)$.

5. For the first part, we need to show that $\text{rotate\_about}(a, t, z) = \text{rotate\_about}(a, 2 \cdot \text{Arg}(\frac{b-a}{z-a}), z)$.
   - Expand the definition of $\text{rotate\_about}$: $\text{rotate\_about}(a, t, z) = a + \text{rotate2d}(t, z-a)$
   - Use the property of rotation addition: $\text{rotate2d}(t, z-a) = \text{rotate2d}(2 \cdot \text{Arg}(\frac{b-a}{z-a}) - 4\pi, z-a)$
   - Express rotation in terms of complex exponentials using Euler's formula and simplify
   - Since $\text{rotate2d}(-4\pi, v) = v$ for any vector $v$ (as a full rotation of $4\pi$ brings us back to the starting point), we have the desired equality.

Therefore, $\text{rotate\_about}(a, t, z) = \text{reflect\_across}((a, b), z)$.

### Mathematical insight
This lemma extends the relationship between rotations and reflections by considering cases where the angles differ by $4\pi$. Geometrically, it shows that when the angle of rotation $t$ differs from $2 \cdot \text{Arg}(\frac{b-a}{z-a})$ by exactly $4\pi$, the rotation of point $z$ about point $a$ by angle $t$ is equivalent to reflecting $z$ across the line determined by points $a$ and $b$.

This is part of a broader set of results establishing connections between different geometric transformations in the complex plane. The result is particularly useful in geometric arguments about triangles and other configurations in the plane, where both rotations and reflections play important roles.

### Dependencies
- **Theorems**:
  - `ROTATE_EQ_REFLECT_LEMMA`: Relates rotation about a point to reflection across a line when specific angle conditions are met
- **Definitions**:
  - `rotate_about`: Defines rotation of a point about another point
  - `reflect_across`: Defines reflection of a point across a line determined by two points

### Porting notes
When porting this theorem to another proof assistant:
1. Ensure that rotations and reflections are defined in terms of complex numbers or 2D vectors
2. The argument function (Arg) on complex numbers must be properly defined
3. Be cautious with the handling of angles and periodicity - some systems might have different conventions for angle normalization
4. The lemma relies on properties of complex exponentials and Euler's formula, which should be available in the target system

---

## EQUILATERAL_TRIANGLE_ALGEBRAIC

### Name of formal statement
EQUILATERAL_TRIANGLE_ALGEBRAIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQUILATERAL_TRIANGLE_ALGEBRAIC = prove
 (`!A B C j.
        j pow 3 = Cx(&1) /\ ~(j = Cx(&1)) /\
        A + j * B + j pow 2 * C = Cx(&0)
        ==> dist(A,B) = dist(B,C) /\ dist(C,A) = dist(B,C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[dist] THEN
  SUBGOAL_THEN `C - A:complex = j * (B - C) /\ A - B = j pow 2 * (B - C)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(j pow 3) = &1` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
    REWRITE_TAC[COMPLEX_NORM_POW; REAL_POW_EQ_1; ARITH; REAL_ABS_NORM] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For any complex points $A$, $B$, $C$, and complex number $j$ such that:
- $j^3 = 1$
- $j \neq 1$
- $A + j \cdot B + j^2 \cdot C = 0$

Then the triangle with vertices $A$, $B$, and $C$ is equilateral:
$\text{dist}(A,B) = \text{dist}(B,C)$ and $\text{dist}(C,A) = \text{dist}(B,C)$

### Informal proof
We need to show that all sides of the triangle have equal length. 

First, I'll manipulate the condition $A + j \cdot B + j^2 \cdot C = 0$ to express the differences between vertices.

* Using complex algebra, we can derive:
  * $C - A = j \cdot (B - C)$
  * $A - B = j^2 \cdot (B - C)$

* From the given conditions $j^3 = 1$, we know that $|j^3| = |j|^3 = 1$, thus $|j| = 1$.

* Recall that $\text{dist}(X,Y) = |X - Y|$ (the norm of the difference between points).

* Using the derived expressions:
  * $\text{dist}(A,B) = |A - B| = |j^2 \cdot (B - C)| = |j|^2 \cdot |B - C| = |B - C| = \text{dist}(B,C)$
  * Similarly, $\text{dist}(C,A) = |C - A| = |j \cdot (B - C)| = |j| \cdot |B - C| = |B - C| = \text{dist}(B,C)$

Therefore, all sides of the triangle have equal length, making it equilateral.

### Mathematical insight
This theorem provides an elegant algebraic characterization of equilateral triangles in the complex plane. The key insight is that multiplying a vector by a complex cube root of unity ($j$ where $j^3 = 1$ but $j \neq 1$) rotates it by exactly $120°$ (or $2\pi/3$ radians). 

The condition $A + j \cdot B + j^2 \cdot C = 0$ implies that the vertices are arranged such that rotating from one vertex to another involves this $120°$ rotation. This is precisely the defining characteristic of an equilateral triangle.

This is a beautiful connection between complex algebra and geometric properties. It shows how complex numbers can be used as a natural language to express rotational symmetry.

### Dependencies
No specific dependencies were listed in the formal content.

### Porting notes
When porting this theorem:
1. Ensure your system has complex numbers with appropriate arithmetic operations
2. Define `dist(A,B)` as the norm of the difference between complex numbers
3. The proof relies on complex algebra and properties of complex norms, so make sure these are available in your target system
4. The condition $j^3 = 1$ and $j \neq 1$ specifies the primitive cube roots of unity ($e^{2\pi i/3}$ and $e^{4\pi i/3}$), which needs to be properly encoded

---

## AFFINE_GROUP_ITER_3

### AFFINE_GROUP_ITER_3
- `AFFINE_GROUP_ITER_3`

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AFFINE_GROUP_ITER_3 = prove
 (`ITER 3 (\z. a * z + b) = (\z. a pow 3 * z + b * (Cx(&1) + a + a pow 2))`,
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`] THEN
  REWRITE_TAC[ITER; FUN_EQ_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
The theorem states that iterating the affine transformation function $f(z) = a \cdot z + b$ three times is equivalent to the function $g(z) = a^3 \cdot z + b \cdot (1 + a + a^2)$.

More formally, if we define:
$$\text{ITER}^3(f)(z) = f(f(f(z)))$$

where $f(z) = a \cdot z + b$, then:
$$\text{ITER}^3(f)(z) = a^3 \cdot z + b \cdot (1 + a + a^2)$$

### Informal proof
The proof proceeds by calculating the result of iterating the affine transformation three times:

- First, we convert the numeral `3` to its internal representation using `num_CONV`.
- Then we expand the definition of `ITER` to unfold the iterations.
- Next, we use function extensionality (`FUN_EQ_THM`) to prove the equality by showing that both functions produce the same output for any input.
- We use `NUM_REDUCE_CONV` to simplify numerical expressions.
- Finally, we complete the proof using `COMPLEX_RING`, which handles the algebraic manipulations in the complex number domain.

The key algebraic calculation involves composing the affine function with itself three times:
- $f(z) = a \cdot z + b$
- $f(f(z)) = a \cdot (a \cdot z + b) + b = a^2 \cdot z + a \cdot b + b = a^2 \cdot z + b(1 + a)$
- $f(f(f(z))) = a \cdot (a^2 \cdot z + b(1 + a)) + b = a^3 \cdot z + a \cdot b(1 + a) + b = a^3 \cdot z + b(1 + a + a^2)$

### Mathematical insight
This theorem provides a closed form for the third iteration of an affine transformation. Affine transformations appear frequently in various mathematical contexts, including group theory, linear algebra, geometry, and computer graphics.

The result is particularly useful in analyzing the behavior of affine transformations under iteration, which is relevant in dynamical systems, fixed point theory, and when studying properties of affine groups. The formula shows how the coefficients evolve after multiple iterations, revealing patterns that can be generalized to $n$ iterations.

The expression $1 + a + a^2$ appearing in the result is the sum of a geometric sequence, suggesting a connection to the general formula for $n$ iterations, which would involve $1 + a + a^2 + \ldots + a^{n-1}$.

### Dependencies
- Definitions:
  - `ITER`: Recursive function for iterating a function $n$ times, defined as:
    - `ITER 0 f x = x`
    - `ITER (SUC n) f x = f (ITER n f x)`

### Porting notes
When porting this theorem:
- Ensure your target system has a way to express function iteration similar to `ITER`.
- The proof relies on algebraic simplification capabilities for complex numbers (`COMPLEX_RING`), so you'll need equivalent algebraic simplification tactics or need to expand the proof into more elementary steps.
- Function extensionality (`FUN_EQ_THM`) is used, which may require explicit invocation in some proof assistants.

---

## AFFINE_GROUP_COMPOSE

### AFFINE_GROUP_COMPOSE
- AFFINE_GROUP_COMPOSE

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AFFINE_GROUP_COMPOSE = prove
 (`(\z. a1 * z + b1) o (\z. a2 * z + b2) =
   (\z. (a1 * a2) * z + (b1 + a1 * b2))`,
  REWRITE_TAC[o_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;
```

### Informal statement
The theorem states that the composition of two complex affine transformations can be expressed as a single affine transformation. Specifically:

$$(\lambda z . a_1 \cdot z + b_1) \circ (\lambda z . a_2 \cdot z + b_2) = \lambda z . (a_1 \cdot a_2) \cdot z + (b_1 + a_1 \cdot b_2)$$

Where $a_1, a_2, b_1, b_2$ are complex numbers, and $\circ$ represents function composition.

### Informal proof
The proof proceeds as follows:

1. Apply function composition definition using `o_THM`, which states that $(f \circ g)(x) = f(g(x))$.

2. Use `FUN_EQ_THM` to establish equality of the functions by showing they yield the same results for all inputs.

3. Apply the `COMPLEX_RING` conversion tactic to simplify and verify the algebraic equality:
   $$a_1 \cdot (a_2 \cdot z + b_2) + b_1 = (a_1 \cdot a_2) \cdot z + (b_1 + a_1 \cdot b_2)$$

   This equality holds by distributivity of multiplication over addition.

### Mathematical insight
This theorem formalizes the fundamental property that affine transformations of the complex plane form a group under composition. When composing two affine transformations of the form $z \mapsto az + b$, the resulting transformation has the coefficient equal to the product of the original coefficients, and the constant term combines the original constants in a specific way.

This result is important in complex analysis, geometric transformations, and group theory as it demonstrates the closure property of affine transformations under composition. It's also essential for understanding how Möbius transformations (a subset of which are affine transformations) behave under composition.

### Dependencies
- **Theorems**:
  - `o_THM` (function composition)
  - `FUN_EQ_THM` (extensional equality of functions)

- **Tactics**:
  - `COMPLEX_RING` (for complex number ring arithmetic)

### Porting notes
When porting this theorem to other proof assistants:
- Ensure the target system has a well-defined notion of function composition
- Verify that the system has appropriate algebraic simplification tactics for complex numbers
- The proof is straightforward and should translate easily to systems with similar algebraic reasoning capabilities

---

## AFFINE_GROUP_I

### AFFINE_GROUP_I
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let AFFINE_GROUP_I = prove
 (`I = (\z. Cx(&1) * z + Cx(&0))`,
  REWRITE_TAC[I_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;
```

### Informal statement
This theorem states that the identity function $I$ on complex numbers can be represented as the affine transformation $I(z) = 1 \cdot z + 0$ for all complex numbers $z$, where $1$ and $0$ are embedded into the complex numbers using the $\text{Cx}$ function.

Specifically:
$$I = \lambda z. \text{Cx}(1) \cdot z + \text{Cx}(0)$$

### Informal proof
The proof is straightforward:
1. Apply `REWRITE_TAC[I_THM; FUN_EQ_THM]` to expand the definition of the identity function $I$ and to reduce the equality of functions to equality at all points.
2. Use complex arithmetic simplification via `CONV_TAC COMPLEX_RING` to verify that $1 \cdot z + 0 = z$ for all complex $z$.

### Mathematical insight
This theorem expresses the identity function on complex numbers as an affine transformation of the form $f(z) = az + b$ with $a = 1$ and $b = 0$.

This is a foundational result for affine transformations, representing the simplest possible non-trivial affine map. It serves as the identity element in the group of affine transformations of the complex plane, hence the name "AFFINE_GROUP_I".

In the context of complex analysis and geometry, this theorem helps formalize the notion that the identity mapping is indeed a member of the affine group, which consists of transformations that preserve collinearity and ratios of distances.

### Dependencies
- `I_THM`: Definition of the identity function $I$
- `FUN_EQ_THM`: Theorem about functional equality
- `COMPLEX_RING`: Conversion tactic for complex number arithmetic

### Porting notes
When porting this theorem to another system:
- Ensure that the complex number type and the embedding function from reals to complex numbers (`Cx`) are properly defined
- Check that function equality is properly handled in the target system
- The proof should be straightforward in any system with decent automation for complex arithmetic

---

## AFFINE_GROUP_EQ

### Name of formal statement
AFFINE_GROUP_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_GROUP_EQ = prove
 (`!a b a' b. (\z. a * z + b) = (\z. a' * z + b') <=> a = a' /\ b = b'`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&1)`) THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
For complex numbers $a, b, a', b'$, the following are equivalent:
- $\forall z \in \mathbb{C}. a \cdot z + b = a' \cdot z + b'$
- $a = a'$ and $b = b'$

In other words, two affine functions on complex numbers are equal if and only if their coefficients are equal.

### Informal proof
The proof works by showing both directions of the equivalence:

- ($\Rightarrow$) Assume that the functions are equal, i.e., $\forall z \in \mathbb{C}. a \cdot z + b = a' \cdot z + b'$
  - We specialize this equation with $z = 0$, getting $a \cdot 0 + b = a' \cdot 0 + b'$, which simplifies to $b = b'$
  - We also specialize with $z = 1$, getting $a \cdot 1 + b = a' \cdot 1 + b'$, which gives us $a + b = a' + b'$
  - Since we know $b = b'$, we can deduce that $a = a'$
  - Thus, $a = a'$ and $b = b'$

- ($\Leftarrow$) Assume $a = a'$ and $b = b'$
  - Then for any $z$, we have $a \cdot z + b = a' \cdot z + b'$ by direct substitution

The HOL Light proof uses complex ring automation to handle the algebraic manipulations.

### Mathematical insight
This theorem establishes the uniqueness of representation for affine transformations of the form $f(z) = az + b$ on complex numbers. It shows that such transformations are completely determined by their coefficients $a$ and $b$.

This is a fundamental result for working with affine transformations in complex analysis. The result is intuitive because an affine transformation is characterized by a scaling/rotation factor $a$ and a translation factor $b$. The theorem confirms that no two distinct pairs of these parameters can represent the same transformation.

### Dependencies
No explicit dependencies were provided in the input.

### Porting notes
This theorem should be straightforward to port to other systems. The proof relies on:
1. Function extensionality (`FUN_EQ_THM`)
2. Simple algebraic manipulation with complex numbers
3. Specializing the equality at specific points (0 and 1)

Most proof assistants have these capabilities with varying syntax. The complex ring automation (`COMPLEX_RING`) might need to be replaced with the target system's automation for algebraic manipulation, or expanded into more primitive steps if such automation isn't available.

---

## AFFINE_GROUP_ROTATE_ABOUT

### Name of formal statement
AFFINE_GROUP_ROTATE_ABOUT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AFFINE_GROUP_ROTATE_ABOUT = prove
 (`!a t. rotate_about a t =
         (\z. cexp(ii * Cx(t)) * z + (Cx(&1) - cexp(ii * Cx(t))) * a)`,
  REWRITE_TAC[rotate_about; FUN_EQ_THM; ROTATE2D_COMPLEX] THEN
  CONV_TAC COMPLEX_RING);;
```

### Informal statement
For all points $a$ in the complex plane and angles $t$, the rotation about point $a$ by angle $t$ can be expressed as the complex function:
$$\text{rotate\_about}(a, t) = \lambda z. e^{it} \cdot z + (1 - e^{it}) \cdot a$$

This theorem provides an alternative formulation of rotation about a point using complex numbers, where $i$ is the imaginary unit.

### Informal proof
The proof proceeds by rewriting the definition of `rotate_about` and then using complex arithmetic:

1. First, we expand the definition of `rotate_about a t x = a + rotate2d t (x - a)` and establish function equality.

2. Then we use the fact that the 2D rotation `rotate2d t` can be expressed in complex form as multiplication by $e^{it}$ (from `ROTATE2D_COMPLEX`).

3. Finally, the resulting expression is simplified using complex ring arithmetic to obtain:
   $$\lambda z. e^{it} \cdot z + (1 - e^{it}) \cdot a$$

### Mathematical insight
This theorem expresses rotation about a point in the elegant language of complex numbers. When rotating a point $z$ about another point $a$, we can think of this operation in two ways:

1. Traditional approach: Translate $z$ so that $a$ is at the origin, rotate around the origin, and translate back.

2. Complex function approach: Apply the function $z \mapsto e^{it}z + (1-e^{it})a$.

The complex formulation is particularly useful in conformal mapping theory and when composing multiple transformations. The theorem shows that rotations about a point belong to the affine group of transformations in the plane, which is reflected in the theorem's name.

### Dependencies
- **Definitions:**
  - `rotate_about`: Defines rotation about a point as `rotate_about a t x = a + rotate2d t (x - a)`
- **Theorems (implicit):**
  - `ROTATE2D_COMPLEX`: Expresses 2D rotation in terms of complex multiplication

### Porting notes
When porting this theorem:
1. Ensure the complex number representation in the target system is compatible
2. Check how the target system handles complex exponentials and the imaginary unit
3. The proof relies on complex ring automation (`COMPLEX_RING`), so similar automation might be required in the target system, or the algebraic steps may need to be made explicit

---

## ALGEBRAIC_LEMMA

### ALGEBRAIC_LEMMA
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let ALGEBRAIC_LEMMA = prove
 (`!a1 a2 a3 b1 b2 b3 A B C.
        (\z. a3 * z + b3) ((\z. a1 * z + b1) B) = B /\
        (\z. a1 * z + b1) ((\z. a2 * z + b2) C) = C /\
        (\z. a2 * z + b2) ((\z. a3 * z + b3) A) = A /\
        ITER 3 (\z. a1 * z + b1) o ITER 3 (\z. a2 * z + b2) o
        ITER 3 (\z. a3 * z + b3) = I /\
        ~(a1 * a2 * a3 = Cx(&1)) /\
        ~(a1 * a2 = Cx(&1)) /\
        ~(a2 * a3 = Cx(&1)) /\
        ~(a3 * a1 = Cx(&1))
        ==> (a1 * a2 * a3) pow 3 = Cx (&1) /\
            ~(a1 * a2 * a3 = Cx (&1)) /\
            C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B = Cx(&0)`,
  REWRITE_TAC[AFFINE_GROUP_ITER_3; AFFINE_GROUP_COMPOSE; AFFINE_GROUP_I;
              AFFINE_GROUP_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `(a1 * a2 * a3) * a1 pow 2 * a2 *
    (a1 - a1 * a2 * a3) * (a2 - a1 * a2 * a3) * (a3 - a1 * a2 * a3) *
    (C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B) = Cx(&0)`
  MP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (COMPLEX_FIELD
     `a3 * (a1 * B + b1) + b3 = B
      ==> ~(a1 * a3 = Cx(&1))
          ==> B = (a3 * b1 + b3) / (Cx(&1) - a1 * a3)`))) THEN
    REPEAT(ANTS_TAC THENL
     [ASM_MESON_TAC[COMPLEX_MUL_SYM]; DISCH_THEN SUBST1_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (COMPLEX_RING
     `s = Cx(&0) ==> s + t = Cx(&0) ==> t = Cx(&0)`));
    REWRITE_TAC[COMPLEX_ENTIRE]] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;
```

### Informal statement
For complex numbers $a_1, a_2, a_3, b_1, b_2, b_3$ and points $A, B, C$ in the complex plane, if:

1. $a_3 \cdot (a_1 \cdot B + b_1) + b_3 = B$
2. $a_1 \cdot (a_2 \cdot C + b_2) + b_1 = C$
3. $a_2 \cdot (a_3 \cdot A + b_3) + b_2 = A$
4. $\text{ITER}^3(f_1) \circ \text{ITER}^3(f_2) \circ \text{ITER}^3(f_3) = I$ where:
   - $f_1(z) = a_1 \cdot z + b_1$
   - $f_2(z) = a_2 \cdot z + b_2$
   - $f_3(z) = a_3 \cdot z + b_3$
   - $I$ is the identity function
5. $a_1 \cdot a_2 \cdot a_3 \neq 1$
6. $a_1 \cdot a_2 \neq 1$
7. $a_2 \cdot a_3 \neq 1$
8. $a_3 \cdot a_1 \neq 1$

Then:
1. $(a_1 \cdot a_2 \cdot a_3)^3 = 1$
2. $a_1 \cdot a_2 \cdot a_3 \neq 1$
3. $C + (a_1 \cdot a_2 \cdot a_3) \cdot A + (a_1 \cdot a_2 \cdot a_3)^2 \cdot B = 0$

### Informal proof
The proof proceeds in several steps:

1. First, we apply several theorems related to affine transformations:
   - `AFFINE_GROUP_ITER_3`: Computes the result of iterating an affine transformation 3 times
   - `AFFINE_GROUP_COMPOSE`: Gives the composition of two affine transformations
   - `AFFINE_GROUP_I`: Represents the identity function as an affine transformation
   - `AFFINE_GROUP_EQ`: Provides equality conditions for affine transformations

2. For the first part of the conclusion, $(a_1 \cdot a_2 \cdot a_3)^3 = 1$, we use complex algebra. This follows from the condition that the composition of the three affine transformations iterated three times equals the identity function. 

3. For the third part of the conclusion, we prove that:
   $$(a_1 \cdot a_2 \cdot a_3) \cdot a_1^2 \cdot a_2 \cdot (a_1 - a_1 \cdot a_2 \cdot a_3) \cdot (a_2 - a_1 \cdot a_2 \cdot a_3) \cdot (a_3 - a_1 \cdot a_2 \cdot a_3) \cdot (C + (a_1 \cdot a_2 \cdot a_3) \cdot A + (a_1 \cdot a_2 \cdot a_3)^2 \cdot B) = 0$$

4. We use the fixed point equations (conditions 1, 2, and 3) to express $A$, $B$, and $C$ in terms of the parameters $a_i$ and $b_i$. Using the assumption that $a_i \cdot a_j \neq 1$ for appropriate pairs, we can solve these equations to get:
   - $B = \frac{a_3 \cdot b_1 + b_3}{1 - a_1 \cdot a_3}$
   - And similar expressions for $A$ and $C$

5. Substituting these expressions into the equation from step 3 and simplifying using complex field arithmetic shows that the expression must equal zero.

6. Since complex multiplication satisfies the cancellation property (if $a \cdot b = 0$ then either $a = 0$ or $b = 0$), and all the factors in the product are non-zero (from our assumptions), we conclude that:
   $$C + (a_1 \cdot a_2 \cdot a_3) \cdot A + (a_1 \cdot a_2 \cdot a_3)^2 \cdot B = 0$$

### Mathematical insight
This theorem is a key algebraic result about compositions of affine transformations in the complex plane. It relates:

1. The fixed points of the affine transformations (points $A$, $B$, $C$)
2. The coefficients of the affine transformations ($a_i$, $b_i$)
3. The behavior of iterating these transformations

The first conclusion, $(a_1 \cdot a_2 \cdot a_3)^3 = 1$, shows that the product of the linear coefficients is a cube root of unity (but not 1 itself). This is a constraint imposed by the condition that the composition of iterations equals the identity.

The second conclusion, $C + (a_1 \cdot a_2 \cdot a_3) \cdot A + (a_1 \cdot a_2 \cdot a_3)^2 \cdot B = 0$, provides a precise relationship between the fixed points of the affine transformations. This equation has geometric significance: the three fixed points form a specific configuration in the complex plane.

This result is used in the proof of Morley's theorem, which states that the three points of intersection of the adjacent angle trisectors of a triangle form an equilateral triangle.

### Dependencies
- **Affine Group Theorems**:
  - `AFFINE_GROUP_ITER_3`: Calculation of 3-fold iteration of an affine transformation
  - `AFFINE_GROUP_COMPOSE`: Composition of affine transformations
  - `AFFINE_GROUP_I`: Representation of the identity function
  - `AFFINE_GROUP_EQ`: Equality condition for affine transformations
- **Definitions**:
  - `ITER`: Iteration of a function n times

### Porting notes
When porting this theorem to other systems:

1. Ensure proper handling of complex algebra; the proof relies heavily on complex field manipulations.
2. The proof uses several custom tactics for complex arithmetic (`COMPLEX_RING`, `COMPLEX_FIELD`). Equivalent simplification tactics should be available or created in the target system.
3. Pay attention to how function iteration and composition are defined in the target system, as the theorem heavily relies on these concepts.
4. The theorem involves affine transformations of the form $f(z) = az + b$ where $a$ and $b$ are complex numbers. Ensure that the target system has a suitable representation for these.

---

## CYCLIC_PERM_SUBGOAL_THEN

### CYCLIC_PERM_SUBGOAL_THEN

### Type of the formal statement
Tactic

### Formal Content
```ocaml
let CYCLIC_PERM_SUBGOAL_THEN =
  let lemma = MESON[]
   `(!A B C P Q R a b c g1 g2 g3.
       Ant A B C P Q R a b c g1 g2 g3 ==> Cns A B C P Q R a b c g1 g2 g3)
    ==> (!A B C P Q R a b c g1 g2 g3.
           Ant A B C P Q R a b c g1 g2 g3
           ==> Ant B C A Q R P b c a g2 g3 g1)
        ==> (!A B C P Q R a b c g1 g2 g3.
                   Ant A B C P Q R a b c g1 g2 g3
                   ==> Cns A B C P Q R a b c g1 g2 g3 /\
                       Cns B C A Q R P b c a g2 g3 g1 /\
                       Cns C A B R P Q c a b g3 g1 g2)`
  and vars =
   [`A:complex`; `B:complex`; `C:complex`;
    `P:complex`; `Q:complex`; `R:complex`;
    `a:real`; `b:real`; `c:real`;
    `g1:complex->complex`; `g2:complex->complex`; `g3:complex->complex`] in
  fun t ttac (asl,w) ->
      let asm = list_mk_conj (map (concl o snd) (rev asl)) in
      let gnw = list_mk_forall(vars,mk_imp(asm,t)) in
      let th1 = MATCH_MP lemma (ASSUME gnw) in
      let tm1 = fst(dest_imp(concl th1)) in
      let th2 = REWRITE_CONV[INSERT_AC; CONJ_ACI; ANGLE_SYM; EQ_SYM_EQ] tm1 in
      let th3 = DISCH_ALL(MP th1 (EQT_ELIM th2)) in
      (MP_TAC th3 THEN ANTS_TAC THENL
        [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC;
         DISCH_THEN(MP_TAC o SPEC_ALL) THEN ANTS_TAC THENL
          [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
           DISCH_THEN(CONJUNCTS_THEN2 ttac MP_TAC) THEN
           DISCH_THEN(CONJUNCTS_THEN ttac)]]) (asl,w);;
```

### Informal statement
`CYCLIC_PERM_SUBGOAL_THEN` is a specialized tactic that handles cyclic permutations in proofs. It takes a term `t` and a tactic `ttac`, and applies a pattern of reasoning based on cyclically permuting variables.

The tactic works with predicates `Ant` and `Cns` that take arguments in the following format:
- Three complex points: $A$, $B$, $C$
- Three complex points: $P$, $Q$, $R$
- Three real values: $a$, $b$, $c$
- Three functions from complex to complex: $g_1$, $g_2$, $g_3$

Given that:
1. For all inputs, if `Ant A B C P Q R a b c g1 g2 g3` holds, then `Cns A B C P Q R a b c g1 g2 g3` holds
2. For all inputs, if `Ant A B C P Q R a b c g1 g2 g3` holds, then `Ant B C A Q R P b c a g2 g3 g1` also holds

The tactic proves that for any inputs, if `Ant A B C P Q R a b c g1 g2 g3` holds, then all three of the following hold:
- `Cns A B C P Q R a b c g1 g2 g3`
- `Cns B C A Q R P b c a g2 g3 g1`
- `Cns C A B R P Q c a b g3 g1 g2`

### Informal proof
The tactic implements a proof strategy for handling cyclic permutation in geometric arguments:

1. It establishes a main lemma stating that if:
   - `Ant` implies `Cns` for all inputs
   - `Ant A B C P Q R a b c g1 g2 g3` implies `Ant B C A Q R P b c a g2 g3 g1` (cyclic permutation)
   
   Then `Ant A B C P Q R a b c g1 g2 g3` implies all three cyclic variants of `Cns`.

2. When applied to a goal, the tactic:
   - Collects all assumptions from the assumption list
   - Formats them as a conjunction with the target term `t`
   - Applies the lemma and rewrites using symmetry properties and associative-commutative rules
   - Sets up a proof structure that:
     - First proves the original `Ant` property holds
     - Then uses that to establish all three cyclic variants of the `Cns` property
   - Applies the user-provided tactic `ttac` to handle the conclusions

### Mathematical insight
This tactic encapsulates a common pattern in geometric reasoning where properties that are invariant under cyclic permutation of points need to be established. Rather than repeating nearly identical proof steps three times, this tactic allows the user to prove a property for one ordering of points and then automatically extend it to all cyclic permutations.

The key insight is that many geometric properties in complex analysis and computational geometry exhibit this kind of symmetry, and a specialized tactic can significantly reduce proof effort and increase readability.

The tactic is particularly useful when working with triangles or other geometric configurations where the cyclical relationship between points is important.

### Dependencies
- **HOL Light Core Functions**:
  - `MESON`, `MATCH_MP`, `ASSUME`, `dest_imp`, `REWRITE_CONV`, `DISCH_ALL`, `MP`, `EQT_ELIM`, `MP_TAC`, `ANTS_TAC`, `POP_ASSUM_LIST`, `K`, `ALL_TAC`, `REPEAT`, `GEN_TAC`, `STRIP_TAC`, `SPEC_ALL`, `CONJUNCTS_THEN2`, `FIRST_ASSUM`, `ACCEPT_TAC`, `CONJUNCTS_THEN`

- **Simplification Theories**:
  - `INSERT_AC`, `CONJ_ACI`, `ANGLE_SYM`, `EQ_SYM_EQ`

### Porting notes
When porting this tactic to other proof assistants:

1. The core logic should be expressible in any system, but the specific implementation will need to be adapted to the system's tactic framework.

2. The tactic heavily uses HOL Light's goal manipulation and assumption handling, which differs across systems:
   - In Lean, this might be implemented as a metaprogramming tactic
   - In Isabelle, this would likely be a structured Isar proof method
   - In Coq, it could be implemented using Ltac or Ltac2

3. The cyclic permutation pattern is generic, so the approach can be adapted to other domains beyond geometry where similar symmetries apply.

4. Note that this tactic assumes certain properties of the predicates `Ant` and `Cns`, particularly that they behave well under permutation. When porting, ensure the corresponding predicates in your system have similar properties.

---

## MORLEY

### MORLEY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MORLEY = prove
 (`!A B C:real^2 P Q R.
     ~collinear{A,B,C} /\ {P,Q,R} SUBSET convex hull {A,B,C} /\
     angle(A,B,R) = angle(A,B,C) / &3 /\
     angle(B,A,R) = angle(B,A,C) / &3 /\
     angle(B,C,P) = angle(B,C,A) / &3 /\
     angle(C,B,P) = angle(C,B,A) / &3 /\
     angle(C,A,Q) = angle(C,A,B) / &3 /\
     angle(A,C,Q) = angle(A,C,B) / &3
     ==> dist(R,P) = dist(P,Q) /\ dist(Q,R) = dist(P,Q)`,
  MATCH_MP_TAC(MESON[]
    `(!A B C. &0 <= Im((C - A) / (B - A)) \/
              &0 <= Im((B - A) / (C - A))) /\
     (!A B C. Property A B C ==> Property A C B) /\
     (!A B C. &0 <= Im((C - A) / (B - A)) ==> Property A B C)
     ==> !A B C. Property A B C`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IM_COMPLEX_INV_LE_0] THEN
    REWRITE_TAC[COMPLEX_INV_DIV] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`P:real^2`; `Q:real^2`; `R:real^2`] THEN
    REWRITE_TAC[ANGLE_SYM; DIST_SYM; INSERT_AC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`P:real^2`; `R:real^2`; `Q:real^2`]) THEN
    REWRITE_TAC[ANGLE_SYM; DIST_SYM; INSERT_AC] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC])
   [`A:real^2 = B`; `A:real^2 = C`; `B:real^2 = C`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
       let th' = GEN_REWRITE_RULE I [REAL_LE_IM_DIV_CYCLIC] th in
       let th'' = GEN_REWRITE_RULE I [REAL_LE_IM_DIV_CYCLIC] th' in
       ASSUME_TAC th' THEN ASSUME_TAC th'') THEN
  ABBREV_TAC `a = angle(C:real^2,A,B) / &3` THEN
  ABBREV_TAC `b = angle(A:real^2,B,C) / &3` THEN
  ABBREV_TAC `c = angle(B:real^2,C,A) / &3` THEN
  ABBREV_TAC `g1 = rotate_about A (&2 * a)` THEN
  ABBREV_TAC `g2 = rotate_about B (&2 * b)` THEN
  ABBREV_TAC `g3 = rotate_about C (&2 * c)` THEN
  CYCLIC_PERM_SUBGOAL_THEN
    `ITER 3 g1 o ITER 3 g2 o ITER 3 g3 = (I:real^2->real^2)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g1"; "g2"; "g3"] THEN
    REWRITE_TAC[ITER_ROTATE_ABOUT] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"; "c"] THEN
    REWRITE_TAC[REAL_ARITH `&3 * &2 * a / &3 = &2 * a`] THEN
    ASM_SIMP_TAC[GSYM REFLECT_ACROSS_COMPOSE_ANGLE] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; REFLECT_ACROSS_SYM] THEN
    ASM_SIMP_TAC[REWRITE_RULE[FUN_EQ_THM; I_THM; o_THM]
                 REFLECT_ACROSS_COMPOSE_INVOLUTION];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN `&0 <= Im((P - B) / (C - B))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ARITH `(u % A + v % B + w % C) - B:real^N =
                 u % (A - B) + w % (C - B) + ((u + v + w) - &1) % B`] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; IM_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[IM_MUL_CX; COMPLEX_DIV_REFL; COMPLEX_SUB_0; IM_CX] THEN
    SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN `&0 <= Im((B - C) / (P - C))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IM_COMPLEX_INV_LE_0; COMPLEX_INV_DIV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ARITH `(u % A + v % B + w % C) - C:real^N =
                   v % (B - C) + u % (A - C) + ((u + v + w) - &1) % C`] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; IM_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[IM_MUL_CX; COMPLEX_DIV_REFL; COMPLEX_SUB_0; IM_CX] THEN
    SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= u * --a ==> u * a <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
    ASM_REWRITE_TAC[GSYM IM_COMPLEX_INV_GE_0; COMPLEX_INV_DIV];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `~(P:real^2 = B) /\ ~(P = C)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x y z. ~(angle(x:real^2,y,z) / &3 = pi / &2)`
     (fun th -> ASM_MESON_TAC[th; ANGLE_REFL]) THEN
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= pi /\ &0 < pi ==> ~(a / &3 = pi / &2)`) THEN
    REWRITE_TAC[ANGLE_RANGE; PI_POS];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `(g3:complex->complex)(g1(Q)) = Q`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g1"; "g3"] THEN
    ONCE_REWRITE_TAC[ROTATE_ABOUT_INVERT] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `reflect_across(A,C) Q` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ROTATE_EQ_REFLECT_LEMMA THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME `angle(C:real^2,A,Q) = a`)] THEN
      REWRITE_TAC[angle] THEN ONCE_REWRITE_TAC[VECTOR_ANGLE_SYM] THEN
      ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[REFLECT_ACROSS_SYM] THEN
    MATCH_MP_TAC ROTATE_EQ_REFLECT_PI_LEMMA THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
    REWRITE_TAC[REAL_ARITH `&2 * a = &4 * pi + &2 * --c <=>
                            a = &2 * pi - c`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [SYM(ASSUME `angle(B:real^2,C,A) / &3 = c`)] THEN
    ONCE_REWRITE_TAC[ANGLE_SYM] THEN FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[angle] THEN
    ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM COMPLEX_INV_DIV] THEN
    MATCH_MP_TAC ARG_INV THEN REWRITE_TAC[GSYM ARG_EQ_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `angle(A:real^2,C,Q) = &0` MP_TAC THENL
     [REWRITE_TAC[angle] THEN ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0];
      ASM_REWRITE_TAC[REAL_ARITH `a / &3 = &0 <=> a = &0`]] THEN
    ASM_MESON_TAC[COLLINEAR_ANGLE; ANGLE_SYM; INSERT_AC];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE LAND_CONV [AFFINE_GROUP_ROTATE_ABOUT])) THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `~(cexp(ii * Cx(&2 * a)) * cexp(ii * Cx(&2 * b)) = Cx(&1)) /\
    ~(cexp(ii * Cx(&2 * a)) * cexp(ii * Cx(&2 * b)) *
      cexp(ii * Cx(&2 * c)) = Cx(&1))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CEXP_ADD; GSYM COMPLEX_ADD_LDISTRIB; GSYM CX_ADD] THEN
    MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 < pi /\
      &3 * a + &3 * b + &3 * c = pi /\ ~(&3 * c = pi)
      ==> (&0 < &2 * a + &2 * b /\ &2 * a + &2 * b < &2 * pi) /\
          (&0 < &2 * a + &2 * b + &2 * c /\
           &2 * a + &2 * b + &2 * c < &2 * pi)`) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "c"] THEN
      REWRITE_TAC[REAL_ARITH `&3 * x / &3 = x`; PI_POS] THEN
      SIMP_TAC[ANGLE_RANGE; REAL_LE_DIV; REAL_POS] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[TRIANGLE_ANGLE_SUM; ADD_AC; ANGLE_SYM];
        ASM_MESON_TAC[COLLINEAR_ANGLE; ANGLE_SYM; INSERT_AC]];
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
      REWRITE_TAC[CEXP_II_NE_1; GSYM CX_ADD]];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a1 = cexp(ii * Cx(&2 * a))`;
    `a2 = cexp(ii * Cx(&2 * b))`;
    `a3 = cexp(ii * Cx(&2 * c))`;
    `b1 = (Cx (&1) - a1) * A`;
    `b2 = (Cx (&1) - a2) * B`;
    `b3 = (Cx (&1) - a3) * C`] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC EQUILATERAL_TRIANGLE_ALGEBRAIC THEN
  EXISTS_TAC `a1 * a2 * a3:complex` THEN
  MATCH_MP_TAC ALGEBRAIC_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`b1:complex`; `b2:complex`; `b3:complex`] THEN
  PURE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[]);;
```

### Informal statement

**Morley's Theorem**: Let $ABC$ be a non-collinear triangle, and let $P$, $Q$, $R$ be points in the triangle (i.e., in the convex hull of $\{A,B,C\}$) such that:
- The angle $\angle ABR = \angle ABC/3$
- The angle $\angle BAR = \angle BAC/3$
- The angle $\angle BCP = \angle BCA/3$
- The angle $\angle CBP = \angle CBA/3$
- The angle $\angle CAQ = \angle CAB/3$
- The angle $\angle ACQ = \angle ACB/3$

Then the triangle $PQR$ is equilateral, i.e., $\text{dist}(R,P) = \text{dist}(P,Q) = \text{dist}(Q,R)$.

In other words, if we trisect each angle of a triangle and consider the points where the adjacent trisectors meet, then these three points form an equilateral triangle.

### Informal proof

The proof follows a complex algebraic approach inspired by Alain Connes' proof:

1. First, we set up a more convenient notation:
   - Let $a = \angle CAB/3$, $b = \angle ABC/3$, and $c = \angle BCA/3$  
   - Let $g_1 = \text{rotate\_about } A (2a)$
   - Let $g_2 = \text{rotate\_about } B (2b)$
   - Let $g_3 = \text{rotate\_about } C (2c)$

2. We prove that the composition $g_1^3 \circ g_2^3 \circ g_3^3 = I$ (identity function):
   - We rewrite each rotation as a composition of reflections using the relationship that a rotation of angle $2\theta$ around a point is equivalent to the composition of two reflections across lines through that point at angle $\theta$ apart.
   - We use properties of reflections, particularly that reflecting twice across the same line gives the identity.

3. We establish that $P, Q, R$ are related to each other through these rotations:
   - We show that $g_3(g_1(Q)) = Q$
   - Similar relations hold for the other points

4. We convert our rotations into complex affine transformations:
   - Each rotation about a point can be expressed as $z \mapsto e^{i\theta}z + (1-e^{i\theta})c$ where $c$ is the center of rotation
   - Let $a_1 = e^{2ai}$, $a_2 = e^{2bi}$, $a_3 = e^{2ci}$
   - Let $b_1 = (1-a_1)A$, $b_2 = (1-a_2)B$, $b_3 = (1-a_3)C$

5. Using algebraic lemmas, we show that:
   - $(a_1 a_2 a_3)^3 = 1$ and $a_1 a_2 a_3 \neq 1$
   - $C + (a_1 a_2 a_3)A + (a_1 a_2 a_3)^2B = 0$

6. The final step applies a result on equilateral triangles:
   - If $j^3 = 1$, $j \neq 1$, and $A + jB + j^2C = 0$, then triangle $ABC$ is equilateral
   - With our values, this proves that $PQR$ is an equilateral triangle

At each step, we guarantee the conditions are met, particularly that the points are in the convex hull of the original triangle and the original triangle is non-collinear.

### Mathematical insight

Morley's theorem is a striking result in Euclidean geometry, discovered by Frank Morley in 1899. It's surprising because it reveals an unexpected connection between angle trisectors (which are notoriously difficult to construct with compass and straightedge) and equilateral triangles.

The proof presented here uses a complex algebraic approach inspired by Alain Connes, which differs from traditional synthetic geometry proofs. This approach leverages:

1. The representation of the plane as complex numbers
2. The use of rotations and reflections as complex transformations
3. Algebraic properties of compositions of these transformations

The key insight is that the three trisection points define an equilateral triangle because they satisfy a specific algebraic relation involving cube roots of unity. The proof relies on expressing the geometric constraints (angle trisections) as algebraic constraints on transformations, and then showing these constraints force the points to form an equilateral triangle.

What makes the theorem particularly beautiful is that it works for any triangle, regardless of its shape or size. This universality suggests a deep underlying structure in Euclidean geometry.

### Dependencies

- **Theorems**:
  - `VECTOR_ANGLE_SYM`: The vector angle between vectors is symmetric
  - `VECTOR_ANGLE_ARG`: Relationship between vector angle and complex argument
  - `COLLINEAR_ANGLE`: Characterization of collinearity in terms of angles
  - `REFLECT_ACROSS_COMPOSE_ANGLE`: Composition of reflections equals rotation
  - `REFLECT_ACROSS_COMPOSE_INVOLUTION`: Reflecting twice across the same line gives the identity
  - `REFLECT_ACROSS_SYM`: Reflection is symmetric with respect to the line endpoints
  - `ITER_ROTATE_ABOUT`: Iterating rotations adds the angles
  - `REAL_LE_IM_DIV_CYCLIC`: Cyclic property of the imaginary part of complex division
  - `ROTATE_ABOUT_INVERT`: Inverse relation of rotations with negated angle
  - `ROTATE_EQ_REFLECT_LEMMA`: Relationship between rotations and reflections
  - `ROTATE_EQ_REFLECT_PI_LEMMA`: Similar relationship with an additional term
  - `EQUILATERAL_TRIANGLE_ALGEBRAIC`: Algebraic characterization of equilateral triangles
  - `AFFINE_GROUP_ROTATE_ABOUT`: Representation of rotation as a complex affine map
  - `ALGEBRAIC_LEMMA`: Key algebraic result relating the transformations

- **Definitions**:
  - `ITER`: Iteration of a function
  - `rotate_about`: Rotation around a point
  - `reflect_across`: Reflection across a line determined by two points

### Porting notes

When porting this theorem:

1. The proof relies heavily on complex number representation of points in the plane. Make sure your target system has a good library for complex numbers and their geometric interpretations.

2. The theorem uses several specialized geometric functions like `rotate_about` and `reflect_across`. You'll need to either port these definitions or replace them with equivalent operations in your target system.

3. The proof uses a sequence of lemmas about complex algebraic properties of rotations and reflections. These might need to be proved separately in your target system.

4. The cyclic permutation pattern used in the proof ("CYCLIC_PERM_SUBGOAL_THEN") is a specific HOL Light pattern. You'll need to adopt a different approach for handling the symmetric cases in other systems.

5. The final algebraic manipulation relies on properties of cube roots of unity. Ensure your target system has appropriate support for complex roots of unity.

---

