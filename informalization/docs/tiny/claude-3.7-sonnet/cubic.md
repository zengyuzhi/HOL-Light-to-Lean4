# cubic.ml

## Overview

Number of statements: 5

This file implements the cubic formula for finding roots of cubic polynomials. It formalizes the complete solution for equations of the form ax³+bx²+cx+d=0, including the Cardano formula and the trigonometric method for the casus irreducibilis. The implementation builds on the complex number theory from the library and handles all cases of the cubic equation, including the discriminant analysis that determines whether roots are real or complex.

## ccbrt

### Name of formal statement
ccbrt

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let ccbrt = new_definition
 `ccbrt(z) = if z = Cx(&0) then Cx(&0) else cexp(clog(z) / Cx(&3))`;;
```

### Informal statement
The function $\text{ccbrt}(z)$ is defined as the cubic root of a complex number $z$:

$$\text{ccbrt}(z) = \begin{cases}
0 & \text{if } z = 0 \\
\exp(\frac{\log(z)}{3}) & \text{otherwise}
\end{cases}$$

where $\exp$ and $\log$ are the complex exponential and logarithm functions, respectively.

### Informal proof
This is a definition, so no proof is needed.

### Mathematical insight
This defines the cubic root function for complex numbers. The definition uses the complex exponential and logarithm functions to compute the cubic root. Specifically, it uses the identity that if $w^3 = z$, then $w = \exp(\frac{\log(z)}{3})$, which follows from the properties of the complex exponential and logarithm.

For complex numbers, there are actually three different cubic roots for any non-zero value (corresponding to the three cube roots of unity: $1$, $e^{2\pi i/3}$, and $e^{4\pi i/3}$). This definition chooses a specific branch of the cubic root function, determined by the branch of the logarithm function that is used in HOL Light. The definition explicitly handles the case when $z = 0$, returning $0$ as the cubic root.

### Dependencies
#### Definitions
- `cexp`: Complex exponential function
- `clog`: Complex logarithm function
- `Cx`: Function for converting a real number to a complex number

### Porting notes
When implementing this in another system, be aware that:
1. The complex logarithm is multi-valued, so the choice of branch will affect which cubic root is computed
2. Systems may have different conventions for handling the branch cuts of logarithm functions
3. Some systems might already have built-in cubic root functions with specific branch cut conventions

---

## CCBRT

### Name of formal statement
CCBRT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CCBRT = prove
 (`!z. ccbrt(z) pow 3 = z`,
  GEN_TAC THEN REWRITE_TAC[ccbrt] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_FIELD `z pow 3 = z * z * z:complex`; GSYM CEXP_ADD] THEN
  REWRITE_TAC[COMPLEX_FIELD `z / Cx(&3) + z / Cx(&3) + z / Cx(&3) = z`] THEN
  ASM_SIMP_TAC[CEXP_CLOG]);;
```

### Informal statement
For any complex number $z$, the cube of the complex cube root of $z$ equals $z$:

$$\forall z \in \mathbb{C}, (\text{ccbrt}(z))^3 = z$$

Where $\text{ccbrt}$ represents the complex cube root function.

### Informal proof
The proof establishes that the cube of the complex cube root of any complex number equals the original number:

* Begin by expanding the definition of $\text{ccbrt}$.
* Split into cases based on the definition of $\text{ccbrt}$:
  * For the case where $z = 0$, use complex ring simplification to show that $0^3 = 0$.
  * For the non-zero case, express the cube using multiplication: $z^3 = z \cdot z \cdot z$.
  * Use the property that $e^{a+b+c} = e^a \cdot e^b \cdot e^c$ by rewriting with the symmetric form of complex exponential addition.
  * Simplify the expression $\frac{z}{3} + \frac{z}{3} + \frac{z}{3} = z$.
  * Apply the identity that $e^{\log(z)} = z$ for non-zero complex numbers to complete the proof.

### Mathematical insight
This theorem establishes one of the fundamental properties of the complex cube root function: that cubing the cube root returns the original value. The complex cube root function is defined carefully to select a specific branch of the cube root, which is why the theorem needs to be proven rather than being definitional. 

The proof handles both the zero case and the non-zero case separately, using the exponential-logarithmic representation of complex roots for the non-zero case. This is a standard approach in complex analysis for defining fractional powers of complex numbers.

### Dependencies
- `ccbrt`: The complex cube root function
- `CEXP_ADD`: Property about addition of complex exponentials
- `CEXP_CLOG`: Identity relating complex exponential and logarithm
- `COMPLEX_FIELD`: Simplifier for complex field expressions
- `COMPLEX_RING`: Simplifier for complex ring expressions

### Porting notes
When porting to another system:
1. Ensure the complex cube root is properly defined with correct branch selection.
2. The proof relies on complex analysis identities, particularly the exponential-logarithmic representation of roots.
3. The special case of zero needs separate handling since logarithms are not defined at zero.
4. Different proof assistants may have different strategies for handling cases and complex field simplifications.

---

## CUBIC_REDUCTION

### Name of formal statement
CUBIC_REDUCTION

### Type of formal statement
theorem

### Formal Content
```ocaml
let CUBIC_REDUCTION = COMPLEX_FIELD
  `~(a = Cx(&0)) /\
   x = y - b / (Cx(&3) * a) /\
   p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2) /\
   q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) /
       (Cx(&54) * a pow 3)
   ==> (a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
        y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0))`;;
```

### Informal statement
Let $a, b, c, d, x, y, p, q$ be complex numbers satisfying:
- $a \neq 0$
- $x = y - \frac{b}{3a}$
- $p = \frac{3ac - b^2}{9a^2}$
- $q = \frac{9abc - 2b^3 - 27a^2d}{54a^3}$

Then, the cubic equation $ax^3 + bx^2 + cx + d = 0$ is equivalent to the reduced form $y^3 + 3py - 2q = 0$.

### Informal proof
The proof uses algebraic manipulation to show that substituting $x = y - \frac{b}{3a}$ into the original cubic equation and simplifying yields the reduced form.

Starting with $ax^3 + bx^2 + cx + d = 0$, we substitute $x = y - \frac{b}{3a}$.

After expanding and collecting terms:
- The coefficient of $y^3$ becomes $a$
- The coefficient of $y^2$ becomes $0$ (this is why we chose the substitution - to eliminate the quadratic term)
- The coefficient of $y$ becomes $3ap$
- The constant term becomes $-2aq$

Dividing everything by $a$ (which is non-zero by assumption), we get the reduced form:
$y^3 + 3py - 2q = 0$

The proof is completed using the `COMPLEX_FIELD` tactic, which handles the algebraic manipulations automatically.

### Mathematical insight
This theorem implements the standard reduction of a general cubic equation to its canonical "depressed" form by eliminating the quadratic term. This is a key step in the classical solution of cubic equations.

The substitution $x = y - \frac{b}{3a}$ is designed specifically to eliminate the $x^2$ term, making the resulting equation easier to solve. The reduced form $y^3 + 3py - 2q = 0$ can then be solved using the Cardano-Tartaglia method, which involves further substitutions.

This reduction is a fundamental step in the analytical solution of cubic equations, simplifying the problem before applying the cubic formula.

### Dependencies
- `COMPLEX_FIELD`: A decision procedure for complex field operations

### Porting notes
When porting this theorem:
- Ensure your target system has a complex number type with appropriate field operations
- The proof may be more explicit in other systems where automatic field solvers are less powerful
- Consider making the substitution and algebraic simplification steps explicit if the target system cannot automatically handle such complex field operations

---

## CUBIC_BASIC

### Name of formal statement
CUBIC_BASIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBIC_BASIC = COMPLEX_FIELD
 `!i t s.
    s pow 2 = q pow 2 + p pow 3 /\
    (s1 pow 3 = if p = Cx(&0) then Cx(&2) * q else q + s) /\
    s2 = --s1 * (Cx(&1) + i * t) / Cx(&2) /\
    s3 = --s1 * (Cx(&1) - i * t) / Cx(&2) /\
    i pow 2 + Cx(&1) = Cx(&0) /\
    t pow 2 = Cx(&3)
    ==> if p = Cx(&0) then
          (y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0) <=>
           y = s1 \/ y = s2 \/ y = s3)
        else
          ~(s1 = Cx(&0)) /\
          (y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0) <=>
               (y = s1 - p / s1 \/ y = s2 - p / s2 \/ y = s3 - p / s3))`;;
```

### Informal statement
For any complex numbers $i$, $t$, $s$, $s1$, $s2$, $s3$, $p$, $q$, if the following conditions hold:
- $s^2 = q^2 + p^3$
- $s1^3 = \begin{cases} 2q & \text{if}\ p = 0 \\ q + s & \text{otherwise} \end{cases}$
- $s2 = -s1 \cdot \frac{1 + it}{2}$
- $s3 = -s1 \cdot \frac{1 - it}{2}$
- $i^2 + 1 = 0$ (i.e., $i$ is the imaginary unit)
- $t^2 = 3$

Then:
1. If $p = 0$, the cubic equation $y^3 + 3py - 2q = 0$ has solutions $y = s1$ or $y = s2$ or $y = s3$
2. If $p \neq 0$, then $s1 \neq 0$ and the cubic equation $y^3 + 3py - 2q = 0$ has solutions $y = s1 - \frac{p}{s1}$ or $y = s2 - \frac{p}{s2}$ or $y = s3 - \frac{p}{s3}$

### Informal proof
The proof is established using complex field arithmetic, working directly with the given conditions.

Let's first establish what we know:
- From $i^2 + 1 = 0$ and $t^2 = 3$, we have $i$ is the imaginary unit and $t = \pm\sqrt{3}$.
- $s^2 = q^2 + p^3$
- $s1^3 = 2q$ (if $p = 0$) or $s1^3 = q + s$ (if $p \neq 0$)
- $s2$ and $s3$ are defined in terms of $s1$, $i$, and $t$.

The proof proceeds by verifying that the claimed values satisfy the cubic equation $y^3 + 3py - 2q = 0$.

For the case when $p = 0$:
- The cubic equation simplifies to $y^3 = 2q$
- $s1^3 = 2q$ directly from our assumptions, so $s1$ is a solution
- For $s2$ and $s3$, we can verify that $s1 + s2 + s3 = 0$ and $s1 \cdot s2 \cdot s3 = -s1^3 = -2q$
- These properties are consistent with $s1, s2, s3$ being the three roots of $y^3 = 2q$

For the case when $p \neq 0$:
- If $s1^3 = q + s$ and $s^2 = q^2 + p^3$, then $s1 \neq 0$ (otherwise we'd have $0 = q + s$)
- For the solutions of form $y = s_j - \frac{p}{s_j}$ where $j \in \{1,2,3\}$, we can substitute these values into the cubic equation
- With algebraic manipulation using the polynomial identity $(s_j - \frac{p}{s_j})^3 + 3p(s_j - \frac{p}{s_j}) - 2q = 0$, which can be verified by expansion
- The verification relies on the properties of $s1$, $s2$, and $s3$ as roots of a related cubic equation

### Mathematical insight
This theorem establishes the Cardano formula for solving cubic equations of the form $y^3 + 3py - 2q = 0$. The solutions are expressed in terms of the cubic roots of complex numbers.

The key insight is the transformation of a general cubic equation into this special form, and then using complex arithmetic to find explicit formulas for the roots. The theorem handles both the case where $p = 0$ (when the equation reduces to $y^3 = 2q$) and the general case.

The approach uses:
1. The cubic formula derived by Cardano
2. The fact that cubic equations have exactly three roots in the complex plane
3. A clever parameterization of these roots using an imaginary unit $i$ and $t = \sqrt{3}$

This result is fundamental in the theory of polynomial equations, as it provides explicit formulas for the roots of cubic equations in terms of radicals.

### Dependencies
There are no explicitly mentioned dependencies, but the proof relies on complex field arithmetic which is being supplied by the `COMPLEX_FIELD` tactic.

### Porting notes
When porting this theorem:
1. Ensure the target system has a well-developed complex number theory including powers and field operations
2. The cubic formula is sensitive to the exact form of the cubic equation - ensure that the special form $y^3 + 3py - 2q = 0$ is the one you're working with
3. The parameters $s$, $s1$, $s2$, $s3$ represent intermediate values in the Cardano formula and must be defined exactly as given
4. Special attention should be given to the handling of the two cases: $p = 0$ and $p \neq 0$

---

## CUBIC

### Name of formal statement
CUBIC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBIC = prove
 (`~(a = Cx(&0))
   ==> let p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2)
       and q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) /
               (Cx(&54) * a pow 3) in
       let s = csqrt(q pow 2 + p pow 3) in
       let s1 = if p = Cx(&0) then ccbrt(Cx(&2) * q) else ccbrt(q + s) in
       let s2 = --s1 * (Cx(&1) + ii * csqrt(Cx(&3))) / Cx(&2)
       and s3 = --s1 * (Cx(&1) - ii * csqrt(Cx(&3))) / Cx(&2) in
       if p = Cx(&0) then
         a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
            x = s1 - b / (Cx(&3) * a) \/
            x = s2 - b / (Cx(&3) * a) \/
            x = s3 - b / (Cx(&3) * a)
       else
         ~(s1 = Cx(&0)) /\
         (a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
             x = s1 - p / s1 - b / (Cx(&3) * a) \/
             x = s2 - p / s2 - b / (Cx(&3) * a) \/
             x = s3 - p / s3 - b / (Cx(&3) * a))`,
  DISCH_TAC THEN REPEAT LET_TAC THEN
  ABBREV_TAC `y = x + b / (Cx(&3) * a)` THEN
  SUBGOAL_THEN
   `a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0) <=>
    y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CUBIC_REDUCTION THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "y" THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `x = a - b <=> x + b = (a:complex)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CUBIC_BASIC THEN
  MAP_EVERY EXISTS_TAC
   [`ii`; `csqrt(Cx(&3))`; `csqrt (q pow 2 + p pow 3)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CSQRT];
    ASM_MESON_TAC[CCBRT];
    MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING;
    ASM_MESON_TAC[CSQRT]]);;
```

### Informal statement
Let $a, b, c, d$ be complex numbers with $a \neq 0$. Define the following auxiliary variables:
- $p = \frac{3ac - b^2}{9a^2}$
- $q = \frac{9abc - 2b^3 - 27a^2d}{54a^3}$
- $s = \sqrt{q^2 + p^3}$ (any complex square root)
- $s_1 = \begin{cases} \sqrt[3]{2q} & \text{if } p = 0 \\ \sqrt[3]{q + s} & \text{otherwise} \end{cases}$ (any complex cube root)
- $s_2 = -s_1 \cdot \frac{1 + i\sqrt{3}}{2}$
- $s_3 = -s_1 \cdot \frac{1 - i\sqrt{3}}{2}$

Then:

If $p = 0$, the cubic equation $ax^3 + bx^2 + cx + d = 0$ is equivalent to
$$x = s_1 - \frac{b}{3a} \vee x = s_2 - \frac{b}{3a} \vee x = s_3 - \frac{b}{3a}$$

If $p \neq 0$, then $s_1 \neq 0$ and the cubic equation $ax^3 + bx^2 + cx + d = 0$ is equivalent to
$$x = s_1 - \frac{p}{s_1} - \frac{b}{3a} \vee x = s_2 - \frac{p}{s_2} - \frac{b}{3a} \vee x = s_3 - \frac{p}{s_3} - \frac{b}{3a}$$

### Informal proof
The proof applies the method of transforming the general cubic equation to a simpler form through substitution.

* Define $y = x + \frac{b}{3a}$.

* Show that the original equation $ax^3 + bx^2 + cx + d = 0$ is equivalent to $y^3 + 3py - 2q = 0$ by using the `CUBIC_REDUCTION` theorem and simplifying with complex arithmetic.

* Rewrite the equation in the form $y = s_1 - \frac{p}{s_1} \vee y = s_2 - \frac{p}{s_2} \vee y = s_3 - \frac{p}{s_3}$ (when $p \neq 0$) or $y = s_1 \vee y = s_2 \vee y = s_3$ (when $p = 0$) by applying the `CUBIC_BASIC` theorem.

* The theorem is proven by providing appropriate instantiations, using properties of complex square roots (`CSQRT`), complex cube roots (`CCBRT`), and the identity $i^2 = -1$ (`COMPLEX_POW_II_2`).

### Mathematical insight
This theorem provides explicit formulas (Cardano's formulas) for solving general cubic equations in the complex domain. The approach involves:

1. Reducing the general cubic $ax^3 + bx^2 + cx + d = 0$ to the depressed form $y^3 + 3py - 2q = 0$ by the substitution $y = x + \frac{b}{3a}$.

2. Using Cardano's method to express the solutions of the depressed cubic in terms of complex cube roots.

The formulas work in all cases, including when the discriminant is negative (casus irreducibilis), which in the real case would correspond to three distinct real roots. In this case, the cube roots involve complex numbers, but the final solutions are real.

This result is fundamental in algebraic equation theory as it provides a complete analytic solution to the cubic equation, analogous to the quadratic formula but more intricate.

### Dependencies
- `CUBIC_REDUCTION`: Relates the general cubic to its depressed form
- `CUBIC_BASIC`: Provides solutions to the depressed cubic equation
- `CSQRT`: Properties of complex square roots
- `CCBRT`: Properties of complex cube roots
- `COMPLEX_POW_II_2`: The identity $i^2 = -1$
- `COMPLEX_RING`: Complex ring arithmetic simplification

### Porting notes
When implementing this theorem:
- Ensure that your system has proper support for complex arithmetic and complex roots
- Be aware that different systems may have different conventions for selecting branch cuts in complex square and cube roots
- In some systems, you might need explicit type annotations to handle complex arithmetic properly

---

