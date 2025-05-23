# quartic.ml

## Overview

Number of statements: 13

The `quartic.ml` file contains formal proofs and solutions for quartic equations (polynomials of degree 4). It implements Ferrari's method, which reduces quartic equations to cubic and quadratic cases through algebraic transformations. The file provides complete formalization of the algebraic solution to the general quartic, including all necessary lemmas and intermediate results required to establish correctness of the solution formulas.

## QUARTIC_1

### QUARTIC_1
- `QUARTIC_1`

### Type of the formal statement
- theorem

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
This theorem addresses a special case of the quartic equation solution where $R = 0$. It states that:

If we have:
- $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$ 
- $R = 0$
- $s^2 = y^2 - 4d$
- $D^2 = \frac{3a^2}{4} - 2b + 2s$
- $x = -\frac{a}{4} + \frac{R}{2} + \frac{D}{2}$

Then $x$ is a root of the quartic equation $x^4 + ax^3 + bx^2 + cx + d = 0$.

### Informal proof
The proof is performed using the `REAL_RING` conversion tactic, which automatically proves the statement by reducing it to an identity in the ring of real numbers. This tactic handles polynomial identities by performing algebraic manipulations and verifying that both sides of the equation are equivalent.

In essence, the proof involves substituting the definitions of $R$, $s$, and $D$ into the expression for $x$, and then verifying that this value of $x$ satisfies the quartic equation through algebraic manipulation.

### Mathematical insight
This theorem represents a component of Ferrari's method for solving quartic equations. When solving a general quartic equation $x^4 + ax^3 + bx^2 + cx + d = 0$, one approach is to convert it to a depressed quartic by substituting $x = t - \frac{a}{4}$. The solution process involves introducing auxiliary variables to factorize the quartic into quadratics.

The parameter $R$ is a key discriminant in the solution process. When $R = 0$, the solution takes a special form, which is what this theorem addresses. The variables $y$, $s$, and $D$ are intermediate quantities in Ferrari's method that help express the roots of the quartic equation.

This theorem is part of a larger collection of results that together provide a complete solution to the general quartic equation.

### Dependencies
- `REAL_RING`: A conversion tactic that proves identities in the ring of real numbers

### Porting notes
- When porting this to other systems, the key challenge will be handling the equivalent of the `REAL_RING` tactic, which automatically solves polynomial equalities.
- Some proof assistants like Lean and Coq have ring solvers that can handle this proof automatically, though the exact syntax will differ.
- The proof relies on real algebraic manipulations rather than complex reasoning steps, so the focus should be on ensuring that the statement itself is correctly translated.

---

## QUARTIC_2

### QUARTIC_2

### Type of the formal statement
- theorem

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
This theorem states that if:
- $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$
- $R = 0$
- $s^2 = y^2 - 4d$
- $D^2 = \frac{3a^2}{4} - 2b + 2s$
- $x = -\frac{a}{4} + \frac{R}{2} - \frac{D}{2}$

Then $x$ satisfies the quartic equation:
$x^4 + ax^3 + bx^2 + cx + d = 0$

### Informal proof
The proof is done using the real ring decision procedure (`CONV_TAC REAL_RING`), which automatically verifies that the quartic equation is satisfied when the given conditions hold. This tactic expands the expressions, uses the field properties of real numbers, and confirms the equality.

### Mathematical insight
This theorem is part of Ferrari's method for solving quartic equations. It represents a key step in the algebraic solution of fourth-degree polynomials. The various parameters ($y$, $R$, $s$, $D$) are auxiliary variables introduced to express the roots of the quartic in terms of radicals.

The theorem specifically deals with the case where $R = 0$, which simplifies the calculation. In this case, the expression for $x$ reduces to $x = -\frac{a}{4} - \frac{D}{2}$.

The conditions form a system of equations that, when satisfied, allow us to express a root of the quartic equation. The first equation (the cubic in $y$) is the resolvent cubic of the quartic, whose roots lead to the solution of the original equation.

### Dependencies
- Real arithmetic decision procedure: `REAL_RING`

### Porting notes
- This proof relies heavily on the real arithmetic decision procedure. Other proof assistants will need similar automated reasoning tools for polynomial arithmetic to verify this result efficiently.
- Explicit numerical constants (like `&4`) use HOL Light's syntax for real numbers. These would need to be adjusted to the target system's notation.
- The approach might need to be modified in systems with different automation capabilities for real arithmetic.

---

## QUARTIC_3

### QUARTIC_3
- `QUARTIC_3`

### Type of the formal statement
- theorem

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
This theorem establishes that if the following equations hold:
1. $y^3 - b \cdot y^2 + (a \cdot c - 4 \cdot d) \cdot y - a^2 \cdot d + 4 \cdot b \cdot d - c^2 = 0$
2. $R^2 = \frac{a^2}{4} - b + y$
3. $R = 0$
4. $s^2 = y^2 - 4 \cdot d$
5. $E^2 = \frac{3 \cdot a^2}{4} - 2 \cdot b - 2 \cdot s$
6. $x = -\frac{a}{4} - \frac{R}{2} + \frac{E}{2}$

Then $x$ is a root of the quartic equation: $x^4 + a \cdot x^3 + b \cdot x^2 + c \cdot x + d = 0$

### Informal proof
The proof is established by the `REAL_RING` conversion tactic, which applies real algebraic manipulation to verify that substituting the given expressions into the quartic equation yields a valid equality. 

Specifically, this conversion:
- Substitutes the value of $x$ from condition 6 into the quartic equation
- Uses the constraints on $R$, $E$, $s$, and $y$ from conditions 2-5
- Uses algebraic manipulation in the real number field to verify that the resulting expression equals zero, confirming that $x$ is indeed a root of the quartic equation

### Mathematical insight
This theorem is part of the solution method for quartic equations (polynomial equations of degree 4). It represents a specific case of Ferrari's method where $R = 0$, which provides a simplified approach to finding roots.

The equations given in the antecedent represent:
1. The resolvent cubic equation (first equation in $y$)
2. Relations between the parameters of the quartic and auxiliary variables $R$, $s$, and $E$
3. The formula for the root $x$ in terms of these auxiliary variables

This particular case ($R = 0$) allows for a more direct calculation of a root without having to handle more complex expressions involving square roots.

### Dependencies
- `REAL_RING`: A conversion that proves identities in the theory of real closed fields

### Porting notes
When porting this theorem:
- The proof relies entirely on algebraic manipulation in real numbers, so any system with good support for real algebraic simplification should be able to prove this directly.
- In systems with less powerful automated reasoning for real arithmetic, you might need to provide intermediate steps in the algebraic verification.
- The theorem represents just one case in solving quartic equations, so it should be connected with other related theorems for complete coverage of quartic solution methods.

---

## QUARTIC_4

### QUARTIC_4

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
  CONV_TAC REAL_RING);;
```

### Informal statement
If the following conditions hold:
- $y^3 - b \cdot y^2 + (a \cdot c - 4 \cdot d) \cdot y - a^2 \cdot d + 4 \cdot b \cdot d - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$
- $R = 0$
- $s^2 = y^2 - 4 \cdot d$
- $E^2 = \frac{3 \cdot a^2}{4} - 2 \cdot b - 2 \cdot s$
- $x = -\frac{a}{4} - \frac{R}{2} - \frac{E}{2}$

Then $x$ satisfies the quartic equation:
$x^4 + a \cdot x^3 + b \cdot x^2 + c \cdot x + d = 0$

### Informal proof
The proof is performed using the `REAL_RING` conversion tactic, which automatically proves the theorem by polynomial arithmetic over the real numbers. This tactic treats the given equations as a system of polynomial constraints and verifies that the conclusion is indeed satisfied when all the premises hold.

The conversion handles the algebraic manipulations required to substitute the values of $y$, $R$, $s$, $E$, and $x$ into the quartic equation and verify that it equals zero.

### Mathematical insight
This theorem is part of the formula for solving quartic equations. The conditions represent a system of equations in the process of solving the general quartic equation $x^4 + a \cdot x^3 + b \cdot x^2 + c \cdot x + d = 0$. 

The approach involves:
1. First finding a value of $y$ that satisfies the resolvent cubic equation (the first condition)
2. Then computing intermediate values $R$, $s$, and $E$ (with $R=0$ in this specific case)
3. Finally determining $x$ that solves the original quartic equation

This theorem represents a verification that when $R=0$, the constructed value of $x$ indeed satisfies the original quartic equation. This is one of several cases in the complete solution method for quartic equations.

### Dependencies
#### Theorems
- `REAL_RING` (implied by the use of `CONV_TAC REAL_RING`)

### Porting notes
When porting this to other proof assistants:
- Ensure that the target system has robust ring automation similar to HOL Light's `REAL_RING`
- Be careful with the notation for real numbers (HOL Light uses `&4` to denote the real number 4)
- Note that real division is represented as `a / &4` in HOL Light

---

## QUARTIC_1'

### QUARTIC_1'
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem states that if:

1. $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
2. $R^2 = \frac{a^2}{4} - b + y$
3. $R \neq 0$
4. $D^2 = \frac{3a^2}{4} - R^2 - 2b + \frac{4ab - 8c - a^3}{4R}$
5. $x = -\frac{a}{4} + \frac{R}{2} + \frac{D}{2}$

Then the quartic equation holds: $x^4 + ax^3 + bx^2 + cx + d = 0$

### Informal proof
The proof is completed using the tactic `CONV_TAC REAL_FIELD`, which applies real field arithmetic to solve the problem. This tactic automatically handles calculations in the field of real numbers, simplifying expressions and proving the equality by standard algebraic manipulation.

This represents a computational verification that substituting the given expression for $x$ into the quartic equation and performing the algebraic simplification results in a true statement.

### Mathematical insight
This theorem represents the non-zero $R$ case of solving a quartic equation using a specific parameterization. The approach builds on Ferrari's method for solving quartic equations by introducing auxiliary variables $y$, $R$, $D$ that allow expressing a solution to the quartic in terms of these parameters.

When $R \neq 0$, we get this specific form of the solution. The significance is that this represents one of the closed-form solutions to the general quartic equation $x^4 + ax^3 + bx^2 + cx + d = 0$.

This result is part of the classical theory of solving polynomial equations of degree 4 by radicals, where different cases must be handled separately. The theorem `QUARTIC_1'` specifically handles the case where the resolvent parameter $R$ is non-zero.

### Dependencies
- `QUARTIC_1`: The more general theorem that includes both the $R = 0$ and $R \neq 0$ cases

### Porting notes
When porting this theorem:
1. Ensure your system has strong automation for field arithmetic, as the proof relies entirely on `REAL_FIELD`.
2. The theorem assumes real arithmetic, so ensure your target system has appropriate real number theories available.
3. The statement deals with quartic equation solving, so documenting this context clearly will help users understand the purpose of the theorem.

---

## QUARTIC_2'

### QUARTIC_2'
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
Let $y, b, a, c, d, R, D, x$ be real numbers satisfying:
- $y^3 - b y^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$
- $R \neq 0$
- $D^2 = \frac{3a^2}{4} - R^2 - 2b + \frac{4ab - 8c - a^3}{4R}$
- $x = -\frac{a}{4} + \frac{R}{2} - \frac{D}{2}$

Then $x$ is a root of the quartic polynomial: $x^4 + ax^3 + bx^2 + cx + d = 0$.

### Informal proof
This theorem is proved using the `REAL_FIELD` conversion tactic, which automatically proves equalities and inequalities in the field of real numbers. The tactic handles the algebraic manipulations needed to substitute the expressions for $x$ into the quartic equation and verify that it evaluates to zero.

The proof involves algebraic substitution and manipulation of the quartic formula. Starting with the expression for $x$, we substitute this into the quartic polynomial $x^4 + ax^3 + bx^2 + cx + d$ and expand. Using the given conditions on $y$, $R$, and $D$, after considerable algebraic simplification, the result equals zero.

### Mathematical insight
This theorem represents a specific case of Ferrari's method for solving quartic equations. It gives a condition for when a certain expression $x$ is a root of a general quartic polynomial $x^4 + ax^3 + bx^2 + cx + d = 0$.

The key insight is that the quartic can be transformed through a series of substitutions involving an auxiliary variable $y$ and intermediate values $R$ and $D$. This is part of a general approach where solving a quartic equation is reduced to solving a resolvent cubic equation (represented by the condition on $y$), followed by square root extractions.

This particular theorem (QUARTIC_2') is a variant of QUARTIC_2 with the condition $R \neq 0$, which handles a specific case in the solution method.

### Dependencies
- Theorems
  - `QUARTIC_2`: A similar theorem that handles the case when $R = 0$

### Porting notes
When porting this theorem, be aware that:
1. The proof relies on automated field algebra in HOL Light (`REAL_FIELD` conversion)
2. In other systems, this might require more explicit algebraic steps
3. The notation `&4` in HOL Light represents the real number 4, which in other systems might be written differently
4. The theorem deals with real numbers, so the target system should have appropriate support for real arithmetic

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
Let $a$, $b$, $c$, $d$, $y$, $R$, $E$, and $x$ be real numbers satisfying the following conditions:
- $y^3 - b \cdot y^2 + (a \cdot c - 4 \cdot d) \cdot y - a^2 \cdot d + 4 \cdot b \cdot d - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$
- $R \neq 0$
- $E^2 = \frac{3a^2}{4} - R^2 - 2b - \frac{4ab - 8c - a^3}{4R}$
- $x = -\frac{a}{4} - \frac{R}{2} + \frac{E}{2}$

Then $x$ is a root of the quartic polynomial:
$x^4 + ax^3 + bx^2 + cx + d = 0$

### Informal proof
The proof is accomplished using the `REAL_FIELD` conversion tactic, which automatically verifies this statement using field operations in the real number domain. This tactic handles the algebraic manipulations needed to substitute the expressions for $R$, $E$, and $x$ into the quartic polynomial and verify that it equals zero.

The calculation involves extensive algebraic manipulation, including:
- Substituting the expression for $x$ into the quartic polynomial
- Using the constraints on $y$, $R$, and $E$ to simplify the resulting expression
- Verifying that after all substitutions and simplifications, the polynomial evaluates to zero

This theorem is a variant of `QUARTIC_3`, which differs by considering the case where $R \neq 0$ instead of $R = 0$.

### Mathematical insight
This theorem provides one of the solution methods for quartic equations in the form $x^4 + ax^3 + bx^2 + cx + d = 0$. It represents a specific case in Ferrari's method for solving quartic equations, particularly handling the case where the parameter $R$ is non-zero.

The theorem is part of the classical approach to solving quartic equations through algebraic manipulations. It demonstrates how a quartic equation can be solved by introducing auxiliary variables ($y$, $R$, and $E$) that satisfy certain relationships. These auxiliary variables help transform the original quartic problem into simpler equations.

The significance of this result is that it provides an explicit formula for a root of a quartic equation in terms of the polynomial coefficients and auxiliary variables, which is an important result in the theory of algebraic equations.

### Dependencies
- Theorems:
  - `QUARTIC_3`: A related theorem for the case where $R = 0$

### Porting notes
When porting this theorem to other proof assistants:
- Be aware that the proof relies on the `REAL_FIELD` tactic, which performs automated algebraic reasoning over real fields. Equivalent automation may need to be implemented or adapted in the target system.
- Ensure that the target system has a robust theory of real numbers with appropriate field operations.
- The proof is largely computational in nature, so systems with good support for computational verification of algebraic identities will handle this more easily.

---

## QUARTIC_4'

### QUARTIC_4'
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
Let $x, y, R, E, a, b, c, d$ be real numbers satisfying the following conditions:
- $y^3 - b \cdot y^2 + (a \cdot c - 4 \cdot d) \cdot y - a^2 \cdot d + 4 \cdot b \cdot d - c^2 = 0$
- $R^2 = a^2/4 - b + y$
- $R \neq 0$
- $E^2 = 3a^2/4 - R^2 - 2b - \frac{4ab - 8c - a^3}{4R}$
- $x = -a/4 - R/2 - E/2$

Then $x$ satisfies the quartic equation:
$x^4 + a \cdot x^3 + b \cdot x^2 + c \cdot x + d = 0$

### Informal proof
The proof is done by applying the `REAL_FIELD` conversion tactic, which automatically solves the goal using field axioms of real numbers along with simplifications.

The tactic handles the algebraic manipulations to verify that the proposed value of $x$ does indeed satisfy the quartic equation when substituted, given the constraints on the variables.

### Mathematical insight
This theorem gives a solution formula for quartic equations. It's part of the process for finding roots of a general quartic polynomial $x^4 + ax^3 + bx^2 + cx + d = 0$.

The theorem describes one of the four possible roots, given by the formula $x = -a/4 - R/2 - E/2$, where the auxiliary variables $R$ and $E$ are determined by specific constraints. The constraints ensure that this value of $x$ is indeed a root of the quartic polynomial.

This is related to Ferrari's method for solving quartic equations, which involves introducing auxiliary variables to transform the problem into more manageable forms.

Note that this theorem (`QUARTIC_4'`) appears to be a variation of another theorem (`QUARTIC_4`), likely handling a different case where $R \neq 0$, while `QUARTIC_4` handles the case where $R = 0$.

### Dependencies
- `QUARTIC_4`: A related theorem for solving quartic equations, likely handling the case where $R = 0$

### Porting notes
- When porting this to other systems, ensure that the field solver or equivalent automation is available to handle the algebraic verification.
- The conversion `REAL_FIELD` in HOL Light is a powerful tactic for solving goals involving real-number field operations. Other systems may require more explicit algebraic manipulations or may have similar but differently named automation.
- The proof is very automation-heavy, so the main challenge in porting would be finding an equivalent automation strategy rather than translating proof steps.

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
Let $a, b, c, d, x, y, R, s, D$ be real numbers satisfying:
- $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = a^2/4 - b + y$
- $s^2 = y^2 - 4d$
- $D^2 = \begin{cases}
    3a^2/4 - 2b + 2s, & \text{if } R = 0 \\
    3a^2/4 - R^2 - 2b + \frac{4ab - 8c - a^3}{4R}, & \text{otherwise}
  \end{cases}$
- $x = -a/4 + R/2 + D/2$

Then $x^4 + ax^3 + bx^2 + cx + d = 0$.

### Informal proof
The proof is handled entirely by the `REAL_FIELD` conversion tactic in HOL Light, which performs field arithmetic simplification and verification. This means the theorem is proved by direct algebraic manipulation of the given expressions.

The conversion expands the quartic expression $x^4 + ax^3 + bx^2 + cx + d$ using the specified value of $x$ in terms of $a, R, D$, and then verifies that under the given constraints on $y, R, s, D$, this expression evaluates to zero.

### Mathematical insight
This theorem provides an explicit formula for solving a quartic equation $x^4 + ax^3 + bx^2 + cx + d = 0$ by expressing one of its roots in terms of auxiliary variables. 

This is part of Ferrari's method for solving quartic equations, which involves:
1. Converting the quartic to a depressed form by substitution
2. Introducing an auxiliary variable $y$ (the "resolvent cubic")
3. Expressing the roots in terms of nested radicals

The theorem essentially states that if $y$ is a root of the resolvent cubic equation, and $R, s, D$ are defined as given, then the value $x = -a/4 + R/2 + D/2$ is a root of the original quartic equation.

Note that the original theorem in HOL Light also includes an alternative formula for $x$ (with $E$ instead of $D$), but it was truncated in the formal content provided. The full theorem would include both possible formulations for the roots.

### Dependencies
- `REAL_FIELD`: A HOL Light conversion for solving problems in real field arithmetic

### Porting notes
When porting this theorem:
1. Ensure the target system has a strong field arithmetic solver or decision procedure
2. The theorem can be split into smaller pieces if the arithmetic solver in the target system is less powerful than HOL Light's `REAL_FIELD`
3. Note that the full theorem likely includes an additional formula for $x$ using a variable $E$ instead of $D$, which was truncated in the provided formal content

---

## QUARTIC_1

### QUARTIC_1

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
This theorem proves a solution method for quartic equations. Given a quartic equation in the form $x^4 + ax^3 + bx^2 + cx + d = 0$, if we have:

1. A value $y$ satisfying the resolvent cubic equation:
   $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$

2. Values $R$, $s$, $D$, and $E$ defined by:
   - $R^2 = \frac{a^2}{4} - b + y$
   - $s^2 = y^2 - 4d$
   - $D^2 = \begin{cases}
       \frac{3a^2}{4} - 2b + 2s & \text{if } R = 0 \\
       \frac{3a^2}{4} - R^2 - 2b + \frac{4ab - 8c - a^3}{4R} & \text{otherwise}
     \end{cases}$
   - $E^2 = \begin{cases}
       \frac{3a^2}{4} - 2b - 2s & \text{if } R = 0 \\
       \frac{3a^2}{4} - R^2 - 2b - \frac{4ab - 8c - a^3}{4R} & \text{otherwise}
     \end{cases}$

Then, any value of $x$ satisfying either:
- $x = -\frac{a}{4} + \frac{R}{2} + \frac{D}{2}$, or
- $x = -\frac{a}{4} - \frac{R}{2} + \frac{E}{2}$

is a solution to the quartic equation $x^4 + ax^3 + bx^2 + cx + d = 0$.

### Informal proof
The proof uses the `REAL_FIELD` conversion, which automatically proves this result using real field arithmetic. This conversion handles the algebraic manipulations needed to verify that substituting either of the proposed forms of $x$ into the quartic equation yields zero.

The proof relies on algebraic manipulations to verify that when either value of $x$ is substituted into the quartic equation, and the relations between the parameters are taken into account, the result simplifies to zero.

### Mathematical insight
This theorem presents Ferrari's method for solving quartic equations. The approach involves:

1. First finding a root $y$ of the "resolvent cubic" equation derived from the original quartic
2. Using this root to define parameters $R$, $s$, $D$, and $E$
3. Constructing the solutions to the original quartic equation using these parameters

The method works by reducing the quartic to a product of two quadratics. The special case handling when $R = 0$ is necessary to avoid division by zero.

This result is significant because it provides an explicit formula for the roots of any quartic polynomial, extending the well-known quadratic and cubic formulas. In mathematics, this represents the highest-degree polynomial equation that can be solved by radicals in the general case.

### Dependencies
- `REAL_FIELD`: A conversion that proves equalities in the field of real numbers

### Porting notes
When porting this theorem:
- The proof relies heavily on the field arithmetic solver in HOL Light. Other systems will need equivalent automation for field arithmetic.
- The case split for when $R = 0$ should be handled carefully.
- The nested conditionals in the definitions of $D^2$ and $E^2$ may require special attention in systems that handle conditionals differently.
- Note that HOL Light uses the prefix `&` for numeric literals (e.g., `&4` represents 4), which may need translation to the target system's number representation.

---

## QUARTIC_CASES

### QUARTIC_CASES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
Let $a, b, c, d, x, y, R, s, D, E$ be real numbers satisfying the following conditions:
- $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = a^2/4 - b + y$
- $s^2 = y^2 - 4d$
- $D^2 = \begin{cases}
    3a^2/4 - 2b + 2s & \text{if}\ R = 0 \\
    3a^2/4 - R^2 - 2b + \frac{4ab - 8c - a^3}{4R} & \text{otherwise}
  \end{cases}$
- $E^2 = \begin{cases}
    3a^2/4 - 2b - 2s & \text{if}\ R = 0 \\
    3a^2/4 - R^2 - 2b - \frac{4ab - 8c - a^3}{4R} & \text{otherwise}
  \end{cases}$
- $x = -a/4 + R/2 + D/2$ or $x = -a/4 + R/2 - D/2$ or $x = -a/4 - R/2 + E/2$ or $x = -a/4 - R/2 - E/2$

Then $x^4 + ax^3 + bx^2 + cx + d = 0$.

### Informal proof
The proof is performed by:
1. Splitting the proof into two cases based on whether $R = 0$ or $R \neq 0$, using `COND_CASES_TAC`
2. Simplifying both cases using the assumptions, via `ASM_REWRITE_TAC[]`
3. Removing the last assumption from the assumption list with `POP_ASSUM MP_TAC`
4. Solving the resulting real algebra problem using the field decision procedure `CONV_TAC REAL_FIELD`

The proof essentially relies on algebraic manipulation to verify that any of the four potential values of $x$ satisfies the quartic equation, given the constraints on the parameters.

### Mathematical insight
This theorem provides a complete set of solutions for a quartic equation $x^4 + ax^3 + bx^2 + cx + d = 0$ based on the resolvent cubic equation and related parameters. The conditions given in the theorem describe:

1. The resolvent cubic equation for $y$
2. Parameters $R$, $s$, $D$, and $E$ defined in terms of the coefficients of the quartic and the solution $y$ of the cubic
3. Four possible values of $x$ expressed using these parameters

This result is a key component of Ferrari's method for solving quartic equations, where the quartic is reduced to a resolvent cubic equation. The theorem shows that the four expressions given for $x$ represent the complete set of solutions to the original quartic equation.

### Dependencies
- `REAL_FIELD`: A decision procedure for the real field theory in HOL Light.

### Porting notes
When porting this theorem:
1. Ensure your target system has a field decision procedure comparable to `REAL_FIELD` in HOL Light.
2. Be aware that HOL Light's `&n` notation represents the real number $n$, and `--a` represents the negation of $a$ (distinct from `-a` which might represent subtraction in some contexts).
3. The proof structure is simple but relies heavily on automated algebraic manipulation. You may need to provide more explicit algebraic steps in systems with weaker automation.
4. If the target system has conditional expressions with different syntax, you'll need to adjust the definitions of $D^2$ and $E^2$ accordingly.

---

## QUARTIC_CASES

### QUARTIC_CASES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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

This theorem provides conditions for solving a quartic equation. Specifically, it states:

Let $y$, $a$, $b$, $c$, $d$, $R$, $s$, $D$, and $E$ be real numbers satisfying the following conditions:
- $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$
- $s^2 = y^2 - 4d$
- $D^2 = \begin{cases}
  \frac{3a^2}{4} - 2b + 2s & \text{if } R = 0 \\
  \frac{3a^2}{4} - R^2 - 2b + \frac{4ab - 8c - a^3}{4R} & \text{otherwise}
  \end{cases}$
- $E^2 = \begin{cases}
  \frac{3a^2}{4} - 2b - 2s & \text{if } R = 0 \\
  \frac{3a^2}{4} - R^2 - 2b - \frac{4ab - 8c - a^3}{4R} & \text{otherwise}
  \end{cases}$

Then:
$x^4 + ax^3 + bx^2 + cx + d = 0$ if and only if one of the following holds:
- $x = -\frac{a}{4} + \frac{R}{2} + \frac{D}{2}$
- $x = -\frac{a}{4} + \frac{R}{2} - \frac{D}{2}$
- $x = -\frac{a}{4} - \frac{R}{2} + \frac{E}{2}$
- $x = -\frac{a}{4} - \frac{R}{2} - \frac{E}{2}$

### Informal proof

The proof uses standard algebraic manipulations in the real field:

1. First, the proof performs a case analysis on the condition $R = 0$ using `COND_CASES_TAC`.
2. For each case, it applies simplification using the assumptions with `ASM_REWRITE_TAC[]`.
3. Then it removes the assumption from the stack with `POP_ASSUM MP_TAC`.
4. Finally, it completes the proof using `CONV_TAC REAL_FIELD`, which applies field arithmetic to verify the equivalence.

The proof essentially confirms that the four roots provided are exactly the solutions to the quartic equation when the given constraints hold.

### Mathematical insight

This theorem provides an explicit formula for the roots of a general quartic polynomial equation $x^4 + ax^3 + bx^2 + cx + d = 0$. It represents Ferrari's method for solving quartic equations.

The key insight is that a quartic can be reduced to solving auxiliary equations:
- First, a cubic equation (the "resolvent cubic") is solved to find $y$.
- From $y$, we compute parameters $R$, $s$, $D$, and $E$.
- These parameters allow us to express the four roots of the original quartic in a symmetrical form.

The conditional definitions for $D$ and $E$ handle the special case where $R = 0$, which requires different formulas.

This result is important as it provides an analytical solution for any quartic equation, extending the classic quadratic and cubic formulas to fourth-degree polynomials. The quartic formula is the highest-degree general polynomial solution formula, as proven by Abel and Galois for the impossibility of general formulas for quintic and higher polynomials.

### Dependencies
- `CONV_TAC REAL_FIELD` - A conversion tactic that applies field axioms to solve goals in real arithmetic

### Porting notes
When porting this theorem:
- Ensure that the target system has proper support for real arithmetic and field operations.
- The definition structure with conditional expressions for $D^2$ and $E^2$ needs careful handling.
- This theorem establishes the equivalence but doesn't prove the existence of solutions to the constraints. A complete quartic solver would need additional theorems for existence conditions.
- The theorem uses the standard form of quartic equations with leading coefficient 1, so any quartic would need normalization first.

---

## QUARTIC_CASES

### QUARTIC_CASES
- `QUARTIC_CASES`

### Type of the formal statement
- theorem

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
Let $y$, $a$, $b$, $c$, $d$, $R$, $s$, $D$, and $E$ be real numbers satisfying the system of equations:
- $y^3 - by^2 + (ac - 4d)y - a^2d + 4bd - c^2 = 0$
- $R^2 = \frac{a^2}{4} - b + y$
- $s^2 = y^2 - 4d$
- $D^2 = \begin{cases}
   \frac{3a^2}{4} - 2b + 2s & \text{if } R = 0 \\
   \frac{3a^2}{4} - R^2 - 2b + \frac{4ab - 8c - a^3}{4R} & \text{if } R \neq 0
  \end{cases}$
- $E^2 = \begin{cases}
   \frac{3a^2}{4} - 2b - 2s & \text{if } R = 0 \\
   \frac{3a^2}{4} - R^2 - 2b - \frac{4ab - 8c - a^3}{4R} & \text{if } R \neq 0
  \end{cases}$

Then, the quartic equation $x^4 + ax^3 + bx^2 + cx + d = 0$ is satisfied if and only if $x$ equals one of the following four values:
- $x = -\frac{a}{4} + \frac{R}{2} + \frac{D}{2}$
- $x = -\frac{a}{4} + \frac{R}{2} - \frac{D}{2}$
- $x = -\frac{a}{4} - \frac{R}{2} + \frac{E}{2}$
- $x = -\frac{a}{4} - \frac{R}{2} - \frac{E}{2}$

### Informal proof
This result is proven using the `REAL_FIELD` conversion tactic, which automatically handles the algebraic manipulations required to show the equivalence between the quartic equation and its factorized form in terms of the four roots.

The proof relies on field arithmetic over the real numbers to verify that the quartic can be rewritten as:
$$(x - (-\frac{a}{4} + \frac{R}{2} + \frac{D}{2}))(x - (-\frac{a}{4} + \frac{R}{2} - \frac{D}{2}))(x - (-\frac{a}{4} - \frac{R}{2} + \frac{E}{2}))(x - (-\frac{a}{4} - \frac{R}{2} - \frac{E}{2}))$$

The automated field solver expands this product and confirms it equals $x^4 + ax^3 + bx^2 + cx + d$ under the given constraints.

### Mathematical insight
This theorem provides the explicit formulas for the roots of a general quartic equation using Ferrari's method. The auxiliary variables $y$, $R$, $s$, $D$, and $E$ are part of a step-by-step solution process:

1. The cubic resolvent equation in $y$ must be solved first.
2. Once $y$ is found, the values of $R$, $s$, $D$, and $E$ can be computed.
3. These values then give the four roots of the original quartic.

The formulation handles special cases, particularly when $R = 0$, which requires separate treatment in the formulas for $D$ and $E$.

This result is significant in algebra as it provides the complete solution to the general quartic polynomial, extending the classical work of Ferrari who first discovered a method for solving quartic equations in the 16th century.

### Dependencies
- No explicit dependencies are used in the proof beyond the `REAL_FIELD` automated tactic.

### Porting notes
When porting this theorem:
- Ensure the target system has a powerful field arithmetic simplifier like HOL Light's `REAL_FIELD`.
- The conditional expressions for $D^2$ and $E^2$ may need special attention, as some systems might handle case analysis differently.
- The numerical constants (like `&4` in HOL Light) should be translated to the appropriate syntax in the target system.
- The theorem assumes real-valued parameters and solutions, so typing constraints should be maintained.

---

