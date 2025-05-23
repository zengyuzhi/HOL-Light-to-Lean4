# quartic.ml

## Overview

Number of statements: 13

This file (`quartic.ml`) contains formalizations related to quartic equations. It likely defines the concept of a quartic equation and develops theorems related to finding and reasoning about its solutions. The file's content may include definitions for quartic polynomials and theorems concerning the existence, uniqueness, or algebraic properties of their roots.


## QUARTIC_1

### Name of formal statement
QUARTIC_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_1 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   D pow 2 = &3 * a pow 2 / &4 - &2 * b + &2 * s /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;
```
### Informal statement
If `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, `R^2 = a^2 / 4 - b + y`, `R = 0`, `s^2 = y^2 - 4 * d`, `D^2 = 3 * a^2 / 4 - 2 * b + 2 * s`, and `x = -a / 4 + R / 2 + D / 2`, then `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
The theorem states that under certain conditions, a root of a quartic equation can be expressed in terms of the coefficients of the quartic. The proof uses `CONV_TAC REAL_RING`, which indicates that the proof strategy involves using ring equalities and simplification in the field of real numbers.

- The main logical step is to substitute the expression for `x` into the quartic equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0` and simplify.
- The conditions `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, `R^2 = a^2 / 4 - b + y`, `R = 0`, `s^2 = y^2 - 4 * d`, `D^2 = 3 * a^2 / 4 - 2 * b + 2 * s` are used in the simplification process to eliminate terms and arrive at `0 = 0`.
- The tactic `REAL_RING` automatically performs the necessary algebraic manipulations, relying on axioms and theorems of real rings.

### Mathematical insight
The theorem demonstrates a special case of solving a quartic equation, specifically when `R = 0`. This simplification allows for a more direct expression of a root `x` in terms of the coefficients `a`, `b`, `c`, and `d`. The theorem connects algebraic conditions on intermediate variables (`y`, `R`, `s`, `D`) to the roots of the polynomial.

### Dependencies
- `REAL_RING`

### Porting notes (optional)
Porting this theorem will primarily depend on the availability of a similar `REAL_RING` tactic or decision procedure in the target proof assistant. If such a tactic is not available, the algebraic simplification may need to be performed manually by unfolding definitions and applying ring axioms. The precise formulation of real numbers and their operations should also be considered for compatibility.


---

## QUARTIC_2

### Name of formal statement
QUARTIC_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_2 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   D pow 2 = &3 * a pow 2 / &4 - &2 * b + &2 * s /\
   x = --a / &4 + R / &2 - D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;
```
### Informal statement
Prove that if `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, `R^2 = a^2 / 4 - b + y`, `R = 0`, `s^2 = y^2 - 4 * d`, `D^2 = 3 * a^2 / 4 - 2 * b + 2 * s` and `x = -a / 4 + R / 2 - D / 2` then `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
- The theorem asserts that a root `x` of a quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0` can be expressed in terms of radicals.
- The proof strategy is to substitute the expression for `x` in terms of `a`, `b`, `c`, `d`, `y`, `R`, `s`, and `D` into the quartic equation and then simplify the resulting expression to zero using the real field axioms and ring properties, which is handled by `CONV_TAC REAL_RING`.
- The proof assumes that the given relationships among `y`, `R`, `s`, `D`, `a`, `b`, `c`, and `d` hold and then shows that `x` as defined is indeed a root of the quartic equation.

### Mathematical insight
This theorem provides a condition which suffices to find a root of a quartic equation. The proof involves substituting the expression for `x` into the quartic equation and simplifying to verify the equality to zero. The significance of this theorem lies in showing that under specific conditions related to the coefficients of the quartic equation, a solution can be explicitly constructed.

### Dependencies
- `REAL_RING` (conversion tactic for simplification using real field axioms and ring properties)


---

## QUARTIC_3

### Name of formal statement
QUARTIC_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_3 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   E pow 2 = &3 * a pow 2 / &4 - &2 * b - &2 * s /\
   x = --a / &4 - R / &2 + E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;
```

### Informal statement
Given real numbers `a`, `b`, `c`, and `d`, and assuming that `y` is a real number satisfying the equation `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, and that `R` is a real number satisfying the equation `R^2 = a^2 / 4 - b + y`, and that `R = 0`, and that `s` is a real number satisfying the equation `s^2 = y^2 - 4 * d`, and that `E` is a real number satisfying the equation `E^2 = 3 * a^2 / 4 - 2 * b - 2 * s`, and that `x` is a real number satisfying the equation `x = -a / 4 - R / 2 + E / 2`, then `x` is a root of the quartic polynomial `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
The theorem states that under certain conditions, a specific value `x` is a root of a quartic polynomial. The proof uses `CONV_TAC REAL_RING`, which utilizes real ring decision procedures to simplify and verify the equality after substitutions:

- Start with the equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.
- Substitute `x = -a / 4 - R / 2 + E / 2` into the quartic polynomial.
- Using the given conditions `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, `R^2 = a^2 / 4 - b + y`, `R = 0`, `s^2 = y^2 - 4 * d`, and `E^2 = 3 * a^2 / 4 - 2 * b - 2 * s`, the expression is simplified.
- After simplification using real field arithmetic, the equation reduces to `0 = 0`, thus proving the theorem.

### Mathematical insight
This theorem provides a solution for finding a root of a quartic equation under certain conditions related to intermediary variables `y`, `R`, `s`, and `E`. It's a specific case where the quartic equation can be reduced to a simpler form through algebraic manipulations and the given equations, allowing the determination of a valid root. The core idea revolves around substituting a carefully constructed value for `x`, which simplifies the quartic polynomial using relationships governing `y`, `R`, `s`, and `E`.

### Dependencies
- `REAL_RING` (conversion tactic for real ring reasoning)


---

## QUARTIC_4

### Name of formal statement
QUARTIC_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_4 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   R = &0 /\
   s pow 2 = y pow 2 - &4 * d /\
   E pow 2 = &3 * a pow 2 / &4 - &2 * b - &2 * s /\
   x = --a / &4 - R / &2 - E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_RING);;
```
### Informal statement
Given real numbers `a`, `b`, `c`, `d`, `y`, `R`, `s`, `E`, and `x`, if the following conditions hold:
1.  `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`
2.  `R^2 = a^2/4 - b + y`
3.  `R = 0`
4.  `s^2 = y^2 - 4*d`
5.  `E^2 = 3*a^2/4 - 2*b - 2*s`
6.  `x = -a/4 - R/2 - E/2`

Then `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
The theorem states that under certain conditions, a specific value `x` is a root of the quartic polynomial `x^4 + a*x^3 + b*x^2 + c*x + d`. The proof, achieved by `CONV_TAC REAL_RING`, uses real ring conversion to simplify the polynomial expression `x^4 + a*x^3 + b*x^2 + c*x + d` after substituting the given expression for `x` and applying the constraints on `y`, `R`, `s` and `E`. The core idea is algebraic manipulation and simplification, relying on the axioms and theorems of real numbers to show that the expression reduces to zero.

*   Start with the equation `x^4 + a*x^3 + b*x^2 + c*x + d`.
*   Substitute the expression for `x` given by `x = -a/4 - R/2 - E/2` into the quartic polynomial.
*   Apply the constraints `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`, `R^2 = a^2/4 - b + y`, `R = 0`, `s^2 = y^2 - 4*d`, and `E^2 = 3*a^2/4 - 2*b - 2*s` to simplify the expression.
*   Use algebraic manipulation within the real field (using properties of addition, subtraction, multiplication, and division) to reduce the entire expression to `0`.
*   The tactic `CONV_TAC REAL_RING` automates this process of algebraic simplification within the real field.

### Mathematical insight
The theorem provides a solution to the quartic equation under specific constraints. It demonstrates that the given value of `x`, constructed using `a`, `b`, `c`, `d`, `y`, `R`, `s`, and `E` as defined, is indeed a root of the quartic polynomial with coefficients `a`, `b`, `c`, and `d`. The importance lies in providing an explicit construction of a root under these constraints, which is a step toward solving the general quartic equation.

### Dependencies
*   The proof relies heavily on the properties of real numbers and polynomial arithmetic. Specifically, it uses theorems and axioms related to addition, subtraction, multiplication, division, and exponentiation in the real field, as encapsulated within `REAL_RING`.


---

## QUARTIC_1'

### Name of formal statement
QUARTIC_1'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_1' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   D pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b +
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;
```
### Informal statement
Given real numbers `a`, `b`, `c`, and `d`, and real numbers `x`, `y`, `R`, and `D` such that:
1. `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, and
2. `R^2 = a^2 / 4 - b + y`, and
3. `R != 0`, and
4. `D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R)`, and
5. `x = -a / 4 + R / 2 + D / 2`,

then `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
The theorem states that `x` is a root of the quartic polynomial `x^4 + a * x^3 + b * x^2 + c * x + d = 0` under certain conditions on `a`, `b`, `c`, `d`, `y`, `R`, and `D`. The proof likely involves the following steps:
- Substitute the expression for `x` into the quartic polynomial `x^4 + a * x^3 + b * x^2 + c * x + d`.
- Use the given equations relating `y`, `R`, `D`, `a`, `b`, `c`, and `d` to simplify the resulting expression.
- After suitable algebraic manipulations, show that the expression reduces to `0`.
- The tactic `REAL_FIELD` suggests that the proof uses real field arithmetic simplification.

### Mathematical insight
This theorem provides a solution to the quartic equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0` by finding a root `x` in terms of `a`, `b`, `c`, and `d`. The equations for `y`, `R`, and `D` are intermediate steps in this solution process, which originates from the Ferrari's solution of quartic equations, involving the resolution of a cubic resolvent. The condition `R != 0` is essential to avoid division by zero in the expression for `D^2`.

### Dependencies
- `REAL_FIELD` tactic.

### Porting notes (optional)
- The `REAL_FIELD` tactic in HOL Light performs algebraic simplification in the real field. Other proof assistants may have similar tactics or require explicit rewriting rules to perform the same simplification.
- Care must be taken to ensure that the condition `R != 0` is properly handled in the target proof assistant.


---

## QUARTIC_2'

### Name of formal statement
QUARTIC_2'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_2' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   D pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b +
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 + R / &2 - D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;
```

### Informal statement
Given real numbers `a`, `b`, `c`, `d`, `x`, `y`, `R`, and `D` such that:
1. `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, and
2. `R^2 = a^2 / 4 - b + y`, and
3. `R` is not equal to 0, and
4. `D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R)`, and
5. `x = -a / 4 + R / 2 - D / 2`,
then `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
The theorem proves that `x` is a root of the quartic equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0` under certain conditions.

- The conditions define `y`, `R`, and `D` in terms of the coefficients `a`, `b`, `c`, and `d` of the quartic equation.
- The proof uses `REAL_FIELD` tactic, indicating that the proof relies on algebraic manipulations within the real field.
- The core idea is to substitute the expression for `x` into the quartic equation and then simplify the resulting expression using the given conditions to show that it equals zero. This involves expansions, substitutions based on the definitions of `y`, `R`, and `D`, and algebraic simplification.

### Mathematical insight
The theorem provides a solution to the quartic equation by expressing a root `x` in terms of radicals involving the coefficients `a`, `b`, `c`, and `d`. The conditions imposed on `y`, `R`, and `D` are intermediate steps in deriving this radical expression. This is part of the broader theory of solving polynomial equations by radicals.

### Dependencies
- `REAL_FIELD` tactic


---

## QUARTIC_3'

### Name of formal statement
QUARTIC_3'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_3' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   E pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 - R / &2 + E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;
```
### Informal statement
Given real numbers `a`, `b`, `c`, `d`, `x`, `y`, `R`, and `E`, if the following conditions hold:
1. `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`
2. `R^2 = a^2 / 4 - b + y`
3. `R` is not equal to `0`
4. `E^2 = 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)`
5. `x = -a / 4 - R / 2 + E / 2`

then `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
The theorem proves that a root `x` of a quartic polynomial `x^4 + a * x^3 + b * x^2 + c * x + d = 0` can be expressed using radicals, given certain intermediate variables satisfy certain polynomial equations.

- The tactic `CONV_TAC REAL_FIELD` is used to prove this theorem.  This tactic likely simplifies the expression `x^4 + a * x^3 + b * x^2 + c * x + d` using the definition of `x` and the conditions on `y`, `R`, and `E`, with the goal of showing that it simplifies to 0.  The `REAL_FIELD` conversion likely uses identities of real algebra to perform polynomial expansions and simplifications. Essential logical steps involve substituting the definition of `x` and then applying algebraic manipulations to reduce the quartic expression to zero, leveraging the relationships between `y`, `R`, and `E` as defined in the assumptions.

### Mathematical insight
The theorem demonstrates the solution to the quartic equation using radicals. It leverages a series of substitutions and variable transformations (`y`, `R`, `E`) to express a root `x` as a combination of these variables, effectively isolating a solution. This is a complex algebraic result showing the existence of a radical solution, analogous to the quadratic and cubic formulas.

### Dependencies
- `REAL_FIELD` (a conversion tactic for simplifying real field expressions)


---

## QUARTIC_4'

### Name of formal statement
QUARTIC_4'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_4' = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   ~(R = &0) /\
   E pow 2 = &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R) /\
   x = --a / &4 - R / &2 - E / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;
```
### Informal statement
Given `y`, `b`, `a`, `c`, `d`, `R`, `E`, and `x` such that
- `y` cubed minus `b` times `y` squared plus (`a` times `c` minus 4 times `d`) times `y` minus `a` squared times `d` plus 4 times `b` times `d` minus `c` squared equals 0,
- `R` squared equals `a` squared divided by 4 minus `b` plus `y`,
- `R` is not equal to 0,
- `E` squared equals 3 times `a` squared divided by 4 minus `R` squared minus 2 times `b` minus (`4` times `a` times `b` minus 8 times `c` minus `a` cubed) divided by (`4` times `R`),
- `x` equals negative `a` divided by 4 minus `R` divided by 2 minus `E` divided by 2,

then `x` to the power of `4` plus `a` times `x` cubed plus `b` times `x` squared plus `c` times `x` plus `d` equals 0.

### Informal sketch
The theorem aims to prove that a specific `x` is a root of a quartic equation. The proof strategy involves:
- Assume the given conditions concerning `y`, `R`, `E`, and `x`. These conditions essentially define `x` in terms of roots of a cubic polynomial related to the quartic.
- Substitute the expression for `x` into the quartic polynomial `x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d`.
- Simplify the resulting expression using real field tactics (`CONV_TAC REAL_FIELD`) to demonstrate that it equals 0. The critical part of the tactic is that it uses field and ring axioms to automatically simplify the expression to 0 under the given hypothesis.

### Mathematical insight
This theorem demonstrates that a root of a quartic equation `x^4 + ax^3 + bx^2 + cx + d = 0` can be expressed in terms of the roots of a related cubic equation. This is a specific instance of a more general method for solving quartic equations. The formulas are derived from Cardano's method and Ferrari's solution for quartics, where variable substitutions and resolvent cubics are used to find the roots of the quartic.

### Dependencies
- `REAL_FIELD` is used in `CONV_TAC` tactic. It depends on field and ring arithmetics for real numbers.


---

## QUARTIC_1

### Name of formal statement
QUARTIC_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_1 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   x = --a / &4 + R / &2 + D / &2
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;
```

### Informal statement
If the real numbers `a`, `b`, `c`, `d`, `x`, `y`, `R`, `s`, and `D` satisfy the following conditions:
1. `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`,
2. `R^2 = a^2/4 - b + y`,
3. `s^2 = y^2 - 4*d`,
4. `D^2 = if R = 0 then 3*a^2/4 - 2*b + 2*s else 3*a^2/4 - R^2 - 2*b + (4*a*b - 8*c - a^3) / (4*R)`, and
5. `x = -a/4 + R/2 + D/2`,
then `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
The theorem proves that `x` is a root of the quartic polynomial `x^4 + a*x^3 + b*x^2 + c*x + d` assuming `x` is constructed as indicated from roots `y`, `R`, `s`, and `D` of certain polynomials derived from the coefficients of the quartic.
- The proof proceeds by simplifying the expression `x^4 + a*x^3 + b*x^2 + c*x + d`, substituting the expression for `x` in terms of `a`, `R`, and `D`.
- The conditions on `R`, `s`, `D`, and `y` are then used to reduce the expression until it equals `0`.
- The tactic `REAL_FIELD` is used, indicating that the proof relies on identities and simplification within the real field. This tactic likely automates the algebraic manipulations required.

### Mathematical insight
The theorem demonstrates the existence of a solution to a quartic equation using a specific algebraic construction. It gives an explicit formula for a root of a quartic polynomial equation in terms of its coefficients, although this formula involves solving for intermediate quantities (`y`, `R`, `s`, and `D`). The key idea involves reducing the quartic equation to a sequence of simpler equations, ultimately expressing a root of the quartic in terms of square roots and cube roots of expressions involving the original coefficients.

### Dependencies
- `REAL_FIELD` (Tactic): Plays a crucial role in real field simplification and likely relies on numerous underlying real arithmetic lemmas and theorems.


---

## QUARTIC_1

### Name of formal statement
QUARTIC_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_1 = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (x = --a / &4 + R / &2 + D / &2 \/
    x = --a / &4 - R / &2 + E / &2)
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  CONV_TAC REAL_FIELD);;
```

### Informal statement
For real numbers `x`, `y`, `a`, `b`, `c`, `d`, `R`, `s`, `D`, and `E`, if the following conditions hold:
1.  `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`,
2.  `R^2 = a^2 / 4 - b + y`,
3.  `s^2 = y^2 - 4 * d`,
4.  `D^2 = if R = 0 then 3 * a^2 / 4 - 2 * b + 2 * s else 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R)`,
5.  `E^2 = if R = 0 then 3 * a^2 / 4 - 2 * b - 2 * s else 3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)`,
6.  `x = -a / 4 + R / 2 + D / 2` or `x = -a / 4 - R / 2 + E / 2`,

then `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
The theorem proves that under certain conditions on `a`, `b`, `c`,`d`,`x`,`y`,`R`,`s`,`D`, and `E`, where `x` take on one of two values, `x` is a root of the quartic polynomial `x^4 + a * x^3 + b * x^2 + c * x + d`.

The proof likely involves the following steps:
*   Assume the antecedent of the implication.
*   Given the definition of `x` using disjunction, perform a case split on the two values that `x` can take.
*   For each case, substitute the corresponding expression for `x` in the quartic polynomial `x^4 + a * x^3 + b * x^2 + c * x + d`.
*   Use the assumptions about `y`, `R`, `s`, `D`, and `E` to simplify the resulting expression.
*   The simplification should ideally lead to `0` using real field arithmetic.
*   The tactic `CONV_TAC REAL_FIELD` suggests heavy use of algebraic simplification and rewriting within the real field.

### Mathematical insight
This theorem states the conditions under which a given `x`, defined based on the parameters `a`, `b`, `c`, and `d`, is a root of a quartic polynomial. It essentially describes a way to find solutions to a quartic equation using a sequence of substitutions and simplifications involving intermediate variables `y`, `R`, `s`, `D`, and `E`.

### Dependencies
None obvious from the statement. It relies on the real number field.

### Porting notes (optional)
The main challenge in porting this theorem will likely be replicating the algebraic simplification capabilities of `CONV_TAC REAL_FIELD`. Other proof assistants may require more manual steps or different tactics to achieve the same level of automation in simplifying polynomial expressions. Handling of the conditional definitions of D^2 and E^2 based on `R = 0` will also require careful attention.


---

## QUARTIC_CASES

### Name of formal statement
QUARTIC_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_CASES = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (x = --a / &4 + R / &2 + D / &2 \/
    x = --a / &4 + R / &2 - D / &2 \/
    x = --a / &4 - R / &2 + E / &2 \/
    x = --a / &4 - R / &2 - E / &2)
   ==> x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
Given real numbers `a`, `b`, `c`, and `d`, and assuming that `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, `R^2 = a^2 / 4 - b + y`, `s^2 = y^2 - 4 * d`, and where `D^2` is defined as `3 * a^2 / 4 - 2 * b + 2 * s` if `R = 0` and as `3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R)` otherwise, and `E^2` is defined as `3 * a^2 / 4 - 2 * b - 2 * s` if `R = 0` and as `3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)` otherwise, then `x = -a / 4 + R / 2 + D / 2` or `x = -a / 4 + R / 2 - D / 2` or `x = -a / 4 - R / 2 + E / 2` or `x = -a / 4 - R / 2 - E / 2` implies that `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
The theorem states that under certain conditions relating `a`, `b`, `c`, `d`, `x`, `y`, `R`, `s`, `D`, and `E`, if `x` takes on one of four specific forms, then `x` is a root of the quartic polynomial `x^4 + a * x^3 + b * x^2 + c * x + d`.

The proof proceeds by:
- Applying `COND_CASES_TAC` to perform case splitting based on the conditions within the hypothesis related to `R = 0`.
- Rewriting the assumptions using `ASM_REWRITE_TAC[]` to simplify the hypothesis.
- Eliminating an assumption using `POP_ASSUM MP_TAC`.
- Applying field arithmetic simplification (using `REAL_FIELD`) to the goal.

The key idea is to verify that under the given substitutions derived from Cardano's method for solving quartics, the given values for `x` do indeed satisfy the quartic equation. The case splitting and field arithmetic are necessary to handle the different expressions that arise depending on whether `R` is zero or not.

### Mathematical insight
This theorem provides specific cases that arise when solving a quartic equation, `x^4 + a * x^3 + b * x^2 + c * x + d = 0`. It presents a set of sufficient conditions under which certain values of 'x', expressed in terms of 'a', 'b', 'c', 'd', and some auxiliary variables (`y`, `R`, `s`, `D`, `E`), are indeed roots of the equation. The conditions involve solving a cubic equation (in `y`), and then defining `R`, `s`, `D`, and `E` based on `y` and the coefficients of the quartic. The conditional definitions of `D^2` and `E^2` depending on `R = 0` reflects the different forms the solutions take depending on the discriminant of the resolvent cubic.

### Dependencies
- `COND_CASES_TAC`
- `ASM_REWRITE_TAC`
- `POP_ASSUM`
- `MP_TAC`
- `CONV_TAC`
- `REAL_FIELD`


---

## QUARTIC_CASES

### Name of formal statement
QUARTIC_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_CASES = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R))
   ==> (x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0 <=>
        x = --a / &4 + R / &2 + D / &2 \/
        x = --a / &4 + R / &2 - D / &2 \/
        x = --a / &4 - R / &2 + E / &2 \/
        x = --a / &4 - R / &2 - E / &2)`,
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  CONV_TAC REAL_FIELD);;
```

### Informal statement
If the real numbers `a`, `b`, `c`, `d`, `y`, `R`, `s`, `D`, and `E` satisfy the following conditions:
1. `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`
2. `R^2 = a^2 / 4 - b + y`
3. `s^2 = y^2 - 4 * d`
4. `D^2` equals `3 * a^2 / 4 - 2 * b + 2 * s` if `R = 0`, and `3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R)` otherwise.
5. `E^2` equals `3 * a^2 / 4 - 2 * b - 2 * s` if `R = 0`, and `3 * a^2 / 4 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)` otherwise.

Then, `x^4 + a * x^3 + b * x^2 + c * x + d = 0` if and only if one of the following is true:
1. `x = -a / 4 + R / 2 + D / 2`
2. `x = -a / 4 + R / 2 - D / 2`
3. `x = -a / 4 - R / 2 + E / 2`
4. `x = -a / 4 - R / 2 - E / 2`

### Informal sketch
The theorem gives the roots of a quartic polynomial in terms of radicals. The proof proceeds by assuming the conditions on `a`, `b`, `c`, `d`, `y`, `R`, `s`, `D`, and `E`. It then rewrites the equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0` to show it's equivalent to one of four possible equalities for `x` involving those parameters. The proof employs conditional case analysis (`COND_CASES_TAC`, `ASM_REWRITE_TAC`, `POP_ASSUM MP_TAC`) and field arithmetic (`REAL_FIELD`).

### Mathematical insight
This theorem provides a closed-form solution for the roots of a quartic equation. It expresses the roots in terms of radicals, using auxiliary variables R, s, D, and E, which are defined based on the coefficients of the quartic polynomial and a variable y, itself a root of a related cubic polynomial. The theorem's main result gives a complete characterization of the solutions to the quartic as being one of these four possible expressions involving radicals.

### Dependencies
**Theorems:**
- `COND_CASES_TAC`
- `ASM_REWRITE_TAC`
- `POP_ASSUM MP_TAC`

**Tactics:**
- `REAL_FIELD`


---

## QUARTIC_CASES

### Name of formal statement
QUARTIC_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUARTIC_CASES = prove
 (`y pow 3 - b * y pow 2 + (a * c - &4 * d) * y -
   a pow 2 * d + &4 * b * d - c pow 2 = &0 /\
   R pow 2 = a pow 2 / &4 - b + y /\
   s pow 2 = y pow 2 - &4 * d /\
   (D pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b + &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b +
                   (&4 * a * b - &8 * c - a pow 3) / (&4 * R)) /\
   (E pow 2 = if R = &0 then &3 * a pow 2 / &4 - &2 * b - &2 * s
              else &3 * a pow 2 / &4 - R pow 2 - &2 * b -
             (&4 * a * b - &8 * c - a pow 3) / (&4 * R))
   ==> (x pow 4 + a * x pow 3 + b * x pow 2 + c * x + d = &0 <=>
        x = --a / &4 + R / &2 + D / &2 \/
        x = --a / &4 + R / &2 - D / &2 \/
        x = --a / &4 - R / &2 + E / &2 \/
        x = --a / &4 - R / &2 - E / &2)`,
  CONV_TAC REAL_FIELD);;
```

### Informal statement
Given real numbers `a`, `b`, `c`, and `d`, and real numbers `y`, `R`, `s`, `D`, and `E` such that:
1. `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`
2. `R^2 = a^2 / 4 - b + y`
3. `s^2 = y^2 - 4 * d`
4. `D^2` is equal to `3/4 * a^2 - 2 * b + 2 * s` if `R = 0`, and `3/4 * a^2 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R)` otherwise.
5. `E^2` is equal to `3/4 * a^2 - 2 * b - 2 * s` if `R = 0`, and `3/4 * a^2 - R^2 - 2 * b - (4 * a * b - 8 * c - a^3) / (4 * R)` otherwise.

Then the equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0` holds if and only if one of the following is true:
1. `x = -a / 4 + R / 2 + D / 2`
2. `x = -a / 4 + R / 2 - D / 2`
3. `x = -a / 4 - R / 2 + E / 2`
4. `x = -a / 4 - R / 2 - E / 2`

### Informal sketch
The theorem provides a solution for quartic equations. The proof, using `CONV_TAC REAL_FIELD`, involves symbolic manipulation in the field of real numbers. The conditions on `y`, `R`, `s`, `D`, and `E` are derived from the standard method of solving quartic equations, transforming the quartic into a solvable form by reducing it to a series of quadratic equations. The proof likely involves substituting each of the potential roots back into the original equation and simplifying using the given relationships between `a`, `b`, `c`, `d`, `y`, `R`, `s`, `D`, and `E`. The `CONV_TAC REAL_FIELD` tactic then handles complex algebraic steps automatically.

### Mathematical insight
This theorem gives an explicit algebraic solution to the quartic equation, expressing the roots in terms of the coefficients. It is a significant result in classical algebra, demonstrating that quartic equations are solvable by radicals. The conditions imposed ensure that the intermediate variables `R`, `D`, and `E` (related to resolvents and auxiliary quadratics) are well-defined and that the final expressions correctly represent the roots.

### Dependencies
- `REAL_FIELD` (Tactic for algebraic simplification in the field of real number)


---

