# quartic.ml

## Overview

Number of statements: 13

The `quartic.ml` file is a HOL Light source file that appears to be self-contained, with no imports from other files. Unfortunately, without additional context or content, the specific purpose and scope of this file cannot be determined. It is likely that the file defines and proves properties related to quartic equations or quartic curves, given its name. The file's role in the larger library and its key content remain unclear without further information.

## QUARTIC_1

### Name of formal statement
QUARTIC_1

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_RING)
```

### Informal statement
For all `a`, `b`, `c`, `d`, and `y`, if the following equations hold: 
`y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`, 
`R^2 = a^2/4 - b + y`, 
`R = 0`, 
`s^2 = y^2 - 4*d`, and 
`D^2 = 3*a^2/4 - 2*b + 2*s`, 
and `x = -a/4 + R/2 + D/2`, 
then `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
* Start by assuming the given equations hold for `y`, `R`, `s`, `D`, and `x`.
* Use these assumptions to derive the value of `x` in terms of `a`, `b`, `y`, and `D`.
* Substitute `R = 0` into the equation for `R^2` to find a relationship between `a`, `b`, and `y`.
* Use the equation `s^2 = y^2 - 4*d` to relate `s` and `y`.
* Then, use the equation `D^2 = 3*a^2/4 - 2*b + 2*s` to relate `D` to `a`, `b`, and `s`.
* Finally, substitute the expression for `x` into the equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0` and simplify to show that the equation holds.

### Mathematical insight
This theorem appears to be related to the roots of a quartic equation. The construction of `x` in terms of `a`, `b`, `y`, and `D` suggests a method for finding the roots of a quartic equation given certain conditions on the coefficients.

### Dependencies
* `REAL_RING`
* Basic algebraic properties of rings and fields

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `REAL_RING` tactic is properly translated, as it is used to handle the real numbers in the proof. Additionally, the use of `CONV_TAC` may need to be replaced with a similar tactic in the target system.

---

## QUARTIC_2

### Name of formal statement
QUARTIC_2

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_RING)
```

### Informal statement
For all real numbers `a`, `b`, `c`, `d`, `y`, `R`, `s`, `D`, and `x`, if the following equations hold: 
`y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`, 
`R^2 = a^2 / 4 - b + y`, 
`R = 0`, 
`s^2 = y^2 - 4 * d`, 
`D^2 = 3 * a^2 / 4 - 2 * b + 2 * s`, and 
`x = -a / 4 + R / 2 - D / 2`, 
then `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
* First, establish the relationship between `y` and the coefficients `a`, `b`, `c`, and `d` through the cubic equation.
* Next, derive `R` in terms of `a` and `y`, noting that `R = 0` simplifies this relationship.
* Use `y` and `d` to find `s`, which is then used to calculate `D` in terms of `a`, `b`, and `s`.
* With `R` and `D` determined, compute `x` using `a`, `R`, and `D`.
* Finally, substitute `x` into the quartic equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0` to prove the statement, leveraging the `CONV_TAC REAL_RING` tactic for real number arithmetic.

### Mathematical insight
This theorem appears to relate the roots of a quartic equation to the solutions of a system of equations involving the coefficients of the quartic. The construction of `x` from `a`, `R`, and `D`, which are in turn derived from the other variables, suggests a method for finding roots of quartic equations by reducing them to simpler equations.

### Dependencies
* `CONV_TAC`
* `REAL_RING`

### Porting notes
When translating this into another proof assistant, pay close attention to how real number arithmetic is handled, as the `CONV_TAC REAL_RING` tactic is specific to HOL Light's approach to real numbers. Additionally, ensure that the target system can handle the nested definitions and substitutions used in the proof.

---

## QUARTIC_3

### Name of formal statement
QUARTIC_3

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_RING)
```

### Informal statement
The theorem `QUARTIC_3` states that if the following equations hold: 
- $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$
- $R = 0$
- $s^2 = y^2 - 4d$
- $E^2 = \frac{3a^2}{4} - 2b - 2s$
- $x = -\frac{a}{4} - \frac{R}{2} + \frac{E}{2}$
then $x^4 + ax^3 + bx^2 + cx + d = 0$.

### Informal sketch
* The theorem involves a series of equations that relate variables $y$, $R$, $s$, $E$, and $x$ with coefficients $a$, $b$, $c$, and $d$.
* The first equation is a cubic equation in terms of $y$, involving coefficients $a$, $b$, $c$, and $d$.
* The subsequent equations define $R$, $s$, and $E$ in terms of $y$ and the coefficients, with $R$ being set to $0$.
* The equation for $x$ combines $a$, $R$, and $E$.
* The conclusion is that $x$ satisfies a quartic equation with coefficients $a$, $b$, $c$, and $d$.
* The proof likely involves substituting the given equations into the quartic equation and simplifying to show that it holds.

### Mathematical insight
This theorem appears to provide a condition under which a quartic equation has a root $x$, given certain relationships between the coefficients of the quartic and other variables. The construction of $x$ from $a$, $R$, and $E$, which are in turn defined by the other equations, suggests a systematic approach to solving or analyzing quartic equations under specific constraints.

### Dependencies
* `REAL_RING`
* Basic algebraic properties and equations

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to the handling of real numbers and the `REAL_RING` tactic, as different systems may have different ways of dealing with these. Additionally, the substitution and simplification steps in the proof may require careful translation to ensure that the quartic equation is correctly derived from the given conditions.

---

## QUARTIC_4

### Name of formal statement
QUARTIC_4

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_RING)
```

### Informal statement
For all `a`, `b`, `c`, `d`, `y`, `R`, `s`, and `E` satisfying the given system of equations:
1. `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`
2. `R^2 = a^2/4 - b + y`
3. `R = 0`
4. `s^2 = y^2 - 4*d`
5. `E^2 = 3*a^2/4 - 2*b - 2*s`
6. `x = -a/4 - R/2 - E/2`
it holds that `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
* The theorem `QUARTIC_4` establishes a relationship between the roots of a quartic equation and a specific system of equations involving `y`, `R`, `s`, `E`, and `x`.
* The proof involves:
  + Manipulating the system of equations to derive relationships between the variables.
  + Using these relationships to express `x` in terms of `a`, `b`, `y`, `R`, and `E`.
  + Substituting the expression for `x` into the quartic equation to show that it equals zero.
  + The `CONV_TAC REAL_RING` tactic is used to handle the real arithmetic.

### Mathematical insight
The theorem `QUARTIC_4` provides a way to find a root `x` of a quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0` by solving a related system of equations involving `y`, `R`, `s`, and `E`. This construction is important because it relates the roots of a quartic equation to a system of equations that can be solved using standard algebraic techniques.

### Dependencies
* `CONV_TAC`
* `REAL_RING`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the real arithmetic is handled correctly. The `CONV_TAC REAL_RING` tactic may need to be replaced with a similar tactic or a set of rewrite rules that handle the real arithmetic. Additionally, the system of equations may need to be solved using a different approach, depending on the capabilities of the target proof assistant.

---

## QUARTIC_1'

### Name of formal statement
QUARTIC_1'

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all real numbers `a`, `b`, `c`, and `d`, if there exist real numbers `y`, `R`, and `D` such that:
1. `y` satisfies the cubic equation `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`,
2. `R` is nonzero and satisfies `R^2 = a^2/4 - b + y`,
3. `D` satisfies `D^2 = 3*a^2/4 - R^2 - 2*b + (4*a*b - 8*c - a^3)/(4*R)`, and
4. `x` is defined as `x = -a/4 + R/2 + D/2`,
then `x` is a root of the quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
* The theorem starts with a set of conditions involving real numbers `a`, `b`, `c`, `d`, `y`, `R`, and `D`, which are related through a system of equations.
* The first condition involves a cubic equation in `y`, which is used to establish a relationship between `y` and the other variables.
* The second condition introduces `R`, which is required to be nonzero, and relates it to `a`, `b`, and `y` through a quadratic equation.
* The third condition involves `D` and relates it to `a`, `b`, `R`, and other variables through another equation involving a square root.
* The fourth condition defines `x` in terms of `a`, `R`, and `D`.
* The conclusion states that `x` satisfies the quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.
* The proof likely involves manipulating these equations and using properties of real numbers and algebraic manipulations to establish the conclusion.

### Mathematical insight
This theorem appears to be related to the solution of quartic equations, which are polynomial equations of degree four. The conditions given in the theorem provide a way to construct a root `x` of a given quartic equation, using intermediate variables `y`, `R`, and `D` that satisfy certain equations. The theorem is likely important in algebra and computer science, particularly in the context of solving polynomial equations.

### Dependencies
* `REAL_FIELD`
* Basic properties of real numbers and algebraic manipulations

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the real number properties and algebraic manipulations are handled correctly. Additionally, the use of `CONV_TAC REAL_FIELD` in the HOL Light proof may need to be replaced with equivalent tactics or mechanisms for handling real numbers in the target proof assistant.

---

## QUARTIC_2'

### Name of formal statement
QUARTIC_2'

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all `a`, `b`, `c`, `d`, `y`, `R`, `D`, and `x` satisfying the given system of equations:
1. `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`
2. `R^2 = a^2/4 - b + y`
3. `R ≠ 0`
4. `D^2 = 3*a^2/4 - R^2 - 2*b + (4*a*b - 8*c - a^3)/(4*R)`
5. `x = -a/4 + R/2 - D/2`
it holds that `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
* The theorem `QUARTIC_2'` involves a system of equations relating `y`, `R`, `D`, and `x` with coefficients `a`, `b`, `c`, and `d`.
* The proof likely involves manipulating these equations to express `x` in terms of `a`, `b`, `c`, `d`, `y`, `R`, and `D`.
* Key steps include:
  - Using the equation `R^2 = a^2/4 - b + y` to relate `R` and `y`.
  - Applying the equation `D^2 = 3*a^2/4 - R^2 - 2*b + (4*a*b - 8*c - a^3)/(4*R)` to relate `D` with other variables.
  - Substituting `x = -a/4 + R/2 - D/2` into the polynomial equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0` to establish the relationship between `x` and the coefficients `a`, `b`, `c`, `d`.
  - Using `CONV_TAC REAL_FIELD` suggests the use of real field tactics for the proof, implying that the theorem involves real numbers and possibly properties of polynomials.

### Mathematical insight
This theorem appears to be related to the roots of a quartic polynomial, providing a condition under which a specific `x` satisfies the equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0`. The conditions given form a system that relates `y`, `R`, `D`, and `x`, suggesting a method for finding roots of quartic equations under certain constraints.

### Dependencies
- `REAL_FIELD`
- Possibly: `CONV_TAC`

### Porting notes
When porting this theorem to another proof assistant like Lean, Coq, or Isabelle, pay special attention to:
- The handling of real numbers and polynomials, as the `REAL_FIELD` tactic is specific to HOL Light.
- The representation of the system of equations and how it is used to prove the final polynomial equation.
- Differences in how binders and substitutions are handled in the target system, as these are crucial for expressing `x` in terms of other variables and proving the theorem.

---

## QUARTIC_3'

### Name of formal statement
QUARTIC_3'

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
The theorem `QUARTIC_3'` states that given the equations `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`, `R^2 = a^2/4 - b + y`, `R ≠ 0`, `E^2 = 3*a^2/4 - R^2 - 2*b - (4*a*b - 8*c - a^3)/(4*R)`, and `x = -a/4 - R/2 + E/2`, it follows that `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
* The proof starts with a set of equations involving `y`, `R`, `E`, and `x`, which define the relationships between these variables.
* The equation `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0` is used to establish a relationship between `y` and the coefficients `a`, `b`, `c`, and `d`.
* The equation `R^2 = a^2/4 - b + y` defines `R` in terms of `a`, `b`, and `y`, with the constraint that `R ≠ 0`.
* The equation `E^2 = 3*a^2/4 - R^2 - 2*b - (4*a*b - 8*c - a^3)/(4*R)` defines `E` in terms of `a`, `b`, `R`, and `c`.
* The final equation `x = -a/4 - R/2 + E/2` defines `x` in terms of `a`, `R`, and `E`.
* The proof then shows that these definitions imply `x^4 + a*x^3 + b*x^2 + c*x + d = 0`, using the `CONV_TAC REAL_FIELD` tactic to handle the real field.

### Mathematical insight
This theorem provides a construction for finding a root `x` of a quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0`, given certain relationships between the coefficients `a`, `b`, `c`, and `d`. The construction involves defining intermediate values `y`, `R`, and `E` using these coefficients, and then using these values to compute `x`. The theorem is important because it provides a way to solve quartic equations, which are polynomial equations of degree 4.

### Dependencies
* `CONV_TAC`
* `REAL_FIELD`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the real field is handled correctly. The `CONV_TAC REAL_FIELD` tactic may need to be replaced with a similar tactic or a series of tactics that achieve the same effect. Additionally, the definitions of `y`, `R`, `E`, and `x` may need to be modified to fit the specific syntax and semantics of the target proof assistant.

---

## QUARTIC_4'

### Name of formal statement
QUARTIC_4'

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all `a`, `b`, `c`, `d`, `y`, `R`, `E`, and `x`, if the following conditions hold:
1. `y` satisfies the cubic equation `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`
2. `R` is defined such that `R^2 = a^2/4 - b + y`
3. `R` is not equal to `0`
4. `E` is defined such that `E^2 = 3*a^2/4 - R^2 - 2*b - (4*a*b - 8*c - a^3)/(4*R)`
5. `x` is defined as `x = -a/4 - R/2 - E/2`
Then, `x` satisfies the quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
* The proof starts with the assumption of the conditions on `y`, `R`, `E`, and `x`.
* Using `CONV_TAC REAL_FIELD`, it simplifies the expressions and applies field properties to manipulate the equations.
* The main logical stages involve:
  * Using the definition of `R` to relate `y` and `a`, `b`
  * Using the definition of `E` to further constrain the relationship between `a`, `b`, `c`, and `R`
  * Substituting the expression for `x` into the quartic equation and simplifying
  * Applying algebraic manipulations to show that the quartic equation holds
* The proof relies on careful manipulation of the given equations and the properties of real fields.

### Mathematical insight
This theorem provides a condition under which a quartic equation has a root, given certain relationships between the coefficients and other variables. The conditions involve the existence of `y`, `R`, and `E` satisfying specific equations, which are then used to construct a root `x` of the quartic equation. This construction is likely useful in algebraic geometry or computer algebra systems.

### Dependencies
* `REAL_FIELD`
* Basic properties of real numbers and fields

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of real numbers and fields. Some systems may require explicit definitions or imports for real fields, and the `CONV_TAC` tactic may need to be replaced with equivalent tactics or strategies. Additionally, the use of `pow` for exponentiation may need to be adjusted to match the target system's notation.

---

## QUARTIC_1

### Name of formal statement
QUARTIC_1

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
The theorem `QUARTIC_1` states that given the equations:
- `y^3 - b * y^2 + (a * c - 4 * d) * y - a^2 * d + 4 * b * d - c^2 = 0`
- `R^2 = a^2 / 4 - b + y`
- `s^2 = y^2 - 4 * d`
- `D^2` is defined piecewise based on `R`: if `R = 0`, then `D^2 = 3 * a^2 / 4 - 2 * b + 2 * s`, otherwise `D^2 = 3 * a^2 / 4 - R^2 - 2 * b + (4 * a * b - 8 * c - a^3) / (4 * R)`
- `x = -a / 4 + R / 2 + D / 2`
then it follows that `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.

### Informal sketch
* The proof starts by assuming the given equations involving `y`, `R`, `s`, and `D`, and the definition of `x` in terms of `a`, `R`, and `D`.
* The main goal is to show that `x` satisfies the quartic equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0`.
* The `CONV_TAC REAL_FIELD` tactic is used, indicating that the proof involves converting the goal into a form that can be solved using real numbers and possibly leveraging properties of fields.
* Key steps likely involve substituting the expressions for `R`, `s`, and `D` into the equation for `x` and then simplifying the resulting expression to show it satisfies the quartic equation.

### Mathematical insight
This theorem provides a solution to a quartic equation in terms of the roots of related equations involving `y`, `R`, `s`, and `D`. It demonstrates how to construct a root `x` of the quartic equation `x^4 + a * x^3 + b * x^2 + c * x + d = 0` given certain conditions on `y`, `R`, `s`, and `D`. This is significant in algebra for solving polynomial equations of degree four.

### Dependencies
* `CONV_TAC`
* `REAL_FIELD`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles real numbers, field properties, and piecewise definitions. The `CONV_TAC REAL_FIELD` tactic may not have a direct equivalent, so understanding its purpose in the proof is crucial for finding an appropriate strategy in the target system. Additionally, ensure that the target system's handling of binders and automation does not introduce inconsistencies with the original HOL Light proof.

---

## QUARTIC_1

### Name of formal statement
QUARTIC_1

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
For all `a`, `b`, `c`, and `d`, if there exists a `y` such that `y` satisfies the equation `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`, and `R^2 = a^2/4 - b + y`, and `s^2 = y^2 - 4*d`, and `D^2` is defined as `3*a^2/4 - 2*b + 2*s` if `R = 0`, otherwise `3*a^2/4 - R^2 - 2*b + (4*a*b - 8*c - a^3)/(4*R)`, and `E^2` is defined as `3*a^2/4 - 2*b - 2*s` if `R = 0`, otherwise `3*a^2/4 - R^2 - 2*b - (4*a*b - 8*c - a^3)/(4*R)`, and `x` is either `-a/4 + R/2 + D/2` or `-a/4 - R/2 + E/2`, then `x` is a root of the quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.

### Informal sketch
* The theorem starts with the assumption of a `y` that satisfies a specific cubic equation involving `a`, `b`, `c`, and `d`.
* It then defines `R^2` and `s^2` based on `a`, `b`, `y`, and `d`.
* The definitions of `D^2` and `E^2` depend on whether `R` is zero or not, involving further calculations with `a`, `b`, `c`, `R`, and `s`.
* The theorem concludes that if `x` is defined in terms of `a`, `R`, `D`, or `E` according to specific formulas, then `x` satisfies the quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0`.
* Key steps involve case analysis based on the value of `R` and substitution of the defined values into the quartic equation to prove that `x` is indeed a root.

### Mathematical insight
This theorem provides a condition under which a quartic equation has a root that can be expressed in terms of the coefficients of the equation and an auxiliary variable `y` that satisfies a related cubic equation. The construction involves careful case analysis and manipulation of expressions to derive the roots of the quartic equation. This is important in algebra for solving polynomial equations and has implications for various mathematical and computational applications.

### Dependencies
* `CONV_TAC`
* `REAL_FIELD`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of real numbers and the `CONV_TAC REAL_FIELD` tactic, as different systems may have varying support for real arithmetic and conversion tactics. Additionally, the case split based on `R = 0` and the definitions of `D^2` and `E^2` will require careful handling of conditional expressions and possibly different tactics for case analysis.

---

## QUARTIC_CASES

### Name of formal statement
QUARTIC_CASES

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
The theorem `QUARTIC_CASES` states that given certain conditions on the variables `a`, `b`, `c`, `d`, `x`, `y`, `R`, `s`, `D`, and `E`, if the following equations hold: 
- `y` satisfies a cubic equation involving `a`, `b`, `c`, and `d`, 
- `R` is defined in terms of `a`, `b`, and `y`, 
- `s` is defined in terms of `y` and `d`, 
- `D` and `E` are defined conditionally based on `R`, `a`, `b`, `s`, and `c`, 
- and `x` can take on specific forms involving `a`, `R`, `D`, and `E`, 
then `x` is a root of the quartic polynomial `x^4 + ax^3 + bx^2 + cx + d = 0`.

### Informal sketch
* The proof involves a case split based on the value of `R`.
* For each case, it applies algebraic manipulations and substitutions to simplify the expressions for `D` and `E`.
* The `COND_CASES_TAC` tactic is used to perform the case split, and `ASM_REWRITE_TAC` is applied to simplify the expressions.
* The `POP_ASSUM MP_TAC` and `CONV_TAC REAL_FIELD` tactics are used to manage assumptions and convert the goal into a form that can be solved using the `REAL_FIELD` tactic.
* The main logical stages involve:
  - Establishing the relationships between `R`, `s`, `D`, and `E` based on the given conditions.
  - Using these relationships to express `x` in terms of `a`, `R`, `D`, and `E`.
  - Substituting the expressions for `x` into the quartic polynomial and simplifying to show that `x` is a root.

### Mathematical insight
The theorem `QUARTIC_CASES` provides a general method for finding roots of a quartic polynomial by reducing it to a set of simpler equations involving the coefficients of the polynomial and auxiliary variables. This method is based on the idea of using the roots of a related cubic equation to construct the roots of the quartic polynomial.

### Dependencies
* `COND_CASES_TAC`
* `ASM_REWRITE_TAC`
* `POP_ASSUM`
* `MP_TAC`
* `CONV_TAC`
* `REAL_FIELD`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of conditional expressions and the use of algebraic manipulations. The `COND_CASES_TAC` tactic may need to be replaced with a similar case-splitting mechanism in the target system. Additionally, the `REAL_FIELD` tactic may require equivalent support for reasoning about real numbers in the target system.

---

## QUARTIC_CASES

### Name of formal statement
QUARTIC_CASES

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
The theorem `QUARTIC_CASES` states that given the equations `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`, `R^2 = a^2/4 - b + y`, `s^2 = y^2 - 4*d`, and the definitions of `D^2` and `E^2` which depend on whether `R = 0` or not, then the roots of the quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0` are given by four specific expressions involving `a`, `R`, `D`, and `E`. The equivalence is stated as `x` being equal to one of the four expressions if and only if `x` is a root of the quartic equation.

### Informal sketch
* The proof starts with the assumption of the given equations and definitions.
* It then applies the `COND_CASES_TAC` tactic to handle the conditional definitions of `D^2` and `E^2`.
* The `ASM_REWRITE_TAC` tactic is used to rewrite the assumptions, followed by `POP_ASSUM MP_TAC` to move the conclusion to the assumptions.
* Finally, `CONV_TAC REAL_FIELD` is applied to convert the conclusion.
* The key steps involve manipulating the equations and using the definitions to express the roots of the quartic equation in terms of `a`, `R`, `D`, and `E`.

### Mathematical insight
The theorem `QUARTIC_CASES` provides a solution to quartic equations by expressing the roots in terms of specific formulas involving the coefficients of the quartic equation. This is a significant result in algebra, as it allows for the explicit computation of roots of quartic polynomials. The use of `R`, `s`, `D`, and `E` as intermediate values helps to simplify the expressions for the roots.

### Dependencies
* `COND_CASES_TAC`
* `ASM_REWRITE_TAC`
* `POP_ASSUM`
* `MP_TAC`
* `CONV_TAC`
* `REAL_FIELD`

### Porting notes
When porting this theorem to other proof assistants, special attention should be paid to the handling of conditional definitions and the use of tactics like `COND_CASES_TAC` and `CONV_TAC REAL_FIELD`, as these may not have direct equivalents. Additionally, the representation of real numbers and the `REAL_FIELD` conversion may require careful consideration to ensure compatibility with the target proof assistant.

---

## QUARTIC_CASES

### Name of formal statement
QUARTIC_CASES

### Type of the formal statement
Theorem

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
  CONV_TAC REAL_FIELD)
```

### Informal statement
The theorem `QUARTIC_CASES` states that given the equations `y^3 - b*y^2 + (a*c - 4*d)*y - a^2*d + 4*b*d - c^2 = 0`, `R^2 = a^2/4 - b + y`, `s^2 = y^2 - 4*d`, and the definitions of `D^2` and `E^2` which depend on whether `R` is zero or not, it is equivalent to say that the quartic equation `x^4 + a*x^3 + b*x^2 + c*x + d = 0` has roots `x = -a/4 + R/2 + D/2`, `x = -a/4 + R/2 - D/2`, `x = -a/4 - R/2 + E/2`, or `x = -a/4 - R/2 - E/2`.

### Informal sketch
* The proof involves solving a quartic equation by first establishing relationships between the coefficients of the quartic and auxiliary variables `y`, `R`, `s`, `D`, and `E`.
* The `CONV_TAC REAL_FIELD` tactic is used to handle the real field arithmetic, implying that the proof involves reasoning about real numbers.
* Key steps include:
  + Establishing the equation for `y` and its relationship to `R` and `s`.
  + Defining `D` and `E` based on the value of `R`, which involves conditional expressions.
  + Using these definitions to express the roots of the quartic equation in terms of `a`, `R`, `D`, and `E`.
* The structure of the proof suggests a careful manipulation of algebraic expressions to derive the roots of the quartic equation from the given equations.

### Mathematical insight
This theorem provides a solution to quartic equations by reducing them to expressions involving the coefficients of the equation and auxiliary variables. The solution is significant because it provides an explicit form for the roots of a quartic equation, which can be complex to solve directly. The use of auxiliary variables `y`, `R`, `s`, `D`, and `E` helps in simplifying the expressions for the roots.

### Dependencies
* `CONV_TAC`
* `REAL_FIELD`

### Porting notes
When translating this theorem into another proof assistant, special care should be taken with the handling of real arithmetic and the conditional definitions of `D` and `E`. The use of `CONV_TAC REAL_FIELD` suggests that the proof relies on properties of real numbers, which may need to be explicitly stated or imported in the target system. Additionally, the conditional expressions for `D` and `E` may require careful handling to ensure that the cases are properly distinguished and that the arithmetic is correctly performed.

---

