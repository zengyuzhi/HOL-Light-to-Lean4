# cubic.ml

## Overview

Number of statements: 5

`cubic.ml` formalizes the cubic formula within HOL Light, based on complex number theory. It resides within a larger complex analysis library, building upon `Complex/complex_transc.ml`. The file likely defines the cubic formula and provides a formal proof of its correctness.


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
The cube root function, `ccbrt`, for complex numbers is defined as follows: for any complex number z, `ccbrt(z)` is equal to `Cx(&0)` (the complex number 0) if z is equal to `Cx(&0)` (the complex number 0); otherwise, `ccbrt(z)` is equal to `cexp(clog(z) / Cx(&3))`, where `cexp` is the complex exponential function and `clog` is the complex logarithm function.

### Informal sketch
- The definition of `ccbrt` is a direct definition, relying on the previously defined complex exponential (`cexp`) and complex logarithm (`clog`) functions.
- The definition handles the special case where the input `z` is zero, explicitly setting `ccbrt(z)` to zero.
- For non-zero complex numbers, the cube root is defined using the complex exponential and logarithm. The expression `clog(z) / Cx(&3)` computes one-third of the complex logarithm of `z`. Then `cexp` is applied to this result, giving one of the cube roots of `z`.
- Because `clog` is multi-valued, this definition gives a specific cube root, not all three.

### Mathematical insight
The definition of the complex cube root leverages the relationship between the exponential and logarithmic functions in the complex domain. Specifically, taking the complex logarithm of a number, dividing it by 3, and then exponentiating the result provides one of the cube roots of that number. The special case for zero is included because the logarithm of zero is undefined. This definition provides a canonical cube root, although complex numbers have three cube roots in general.

### Dependencies
- Requires `Complex/complex_transc.ml`
- Depends on previously defined functions: `cexp`, `clog`, `Cx`


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
For all complex numbers z, `ccbrt(z)` raised to the power of 3 is equal to z.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `ccbrt(z) pow 3 = z` for an arbitrary complex number `z`.
- Apply the definition of `ccbrt`.
- Perform a case split on whether `z` is zero or not.
- In both cases, use algebraic simplification and rewriting with field and ring properties of complex numbers to equate the left-hand side to the right-hand side.
- Specifically rewrite `z pow 3` as `z * z * z` and `z / Cx(&3) + z / Cx(&3) + z / Cx(&3) = z`.
- Simplify using properties of the exponential and complex logarithm functions (`CEXP_CLOG`).

### Mathematical insight
This theorem shows that the complex cube root function `ccbrt` is a valid inverse of the cubing function on complex numbers. It confirms that cubing the complex cube root of a complex number `z` returns the original number `z`.

### Dependencies
- Definitions: `ccbrt`
- Theorems: `CEXP_CLOG`
- Theories: `COMPLEX_FIELD`

### Porting notes (optional)
The case split on whether `z` is zero or not can be handled differently depending on the target proof assistant's capabilities for dealing with conditional definitions or branching in proofs. The algebraic simplification steps rely on standard complex field and ring properties, which should be available in most proof assistants. The handling of complex exponentials and logarithms and identities might differ significantly.


---

## CUBIC_REDUCTION

### Name of formal statement
CUBIC_REDUCTION

### Type of the formal statement
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
For any complex field, given complex numbers `a`, `b`, `c`, and `d`, such that `a` is not equal to 0, and letting `x = y - b / (3 * a)`, `p = (3 * a * c - b^2) / (9 * a^2)`, and `q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3)`, it follows that the equation `a * x^3 + b * x^2 + c * x + d = 0` is equivalent to `y^3 + 3 * p * y - 2 * q = 0`.

### Informal sketch
The theorem states that a general cubic equation can be reduced to a simpler form by a suitable substitution.
- Assume `~(a = Cx(&0))`, `x = y - b / (Cx(&3) * a)`, `p = (Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2)` and `q = (Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) / (Cx(&54) * a pow 3)`.
- Show that `(a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0)) <=> (y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0))` by substitution and algebraic manipulation.
- The proof likely involves substituting `y - b / (3 * a)` for `x` in the cubic equation, expanding, and simplifying the resulting expression to obtain the reduced form.

### Mathematical insight
This theorem provides a standard method for simplifying cubic equations. By substituting `x` with `y - b/(3a)`, the quadratic term is eliminated, resulting in a depressed cubic equation. This simplification is a key step in Cardano's method for solving cubic equations.

### Dependencies
Field Theory:
- `COMPLEX_FIELD`


---

## CUBIC_BASIC

### Name of formal statement
CUBIC_BASIC

### Type of the formal statement
Theorem

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
For all complex numbers `i`, `t`, and `s`, if the square of `s` equals the square of `q` plus the cube of `p`, and the cube of `s1` equals `2 * q` if `p` is zero, otherwise `q + s`, and `s2` equals `--s1 * (1 + i * t) / 2`, and `s3` equals `--s1 * (1 - i * t) / 2`, and the square of `i` plus `1` equals `0`, and the square of `t` equals `3`, then:
- if `p` is zero, then `y` is a root of the cubic equation `y^3 + 3 * p * y - 2 * q = 0` if and only if `y` is equal to `s1`, `s2`, or `s3`;
- otherwise, `s1` is not zero, and `y` is a root of the cubic equation `y^3 + 3 * p * y - 2 * q = 0` if and only if `y` is equal to `s1 - p / s1`, `s2 - p / s2`, or `s3 - p / s3`.

### Informal sketch
The theorem states the solutions for a depressed cubic equation of the form `y^3 + 3*p*y - 2*q = 0` in the complex numbers. The proof likely involves algebraic manipulation of the given equations to show that the provided expressions for `y` indeed satisfy the cubic equation under the specified conditions. The case `p = 0` is treated separately, which simplifies solving the cubic equation to just taking the cube root.

- The initial assumptions set up the relationship between `p`, `q`, `s`, `s1`, `s2`, `s3`, `i` and `t`.
- Then, the theorem splits into two cases based on whether `p` is zero:
    - If `p = 0`, the condition simplifies and the solutions are directly `s1`, `s2`, and `s3.`
    - If `p != 0`, then a further condition `~(s1=0)` exists and the solutions are `s1-p/s1`, `s2-p/s2` and `s3-p/s3.`
- Each case involves demonstrating that the given solutions `y` satisfy the cubic equation through substitution and simplification. One might use lemmas about complex arithmetic and power operations.

### Mathematical insight
This theorem provides a way to find the roots of a specific form of cubic equation using complex numbers. The equation is in the depressed form where the quadratic term is absent. introducing complex numbers allows to provide solutions in all cases, even when real solutions are not apparent initially. The separation into two cases, `p = 0` and `p != 0`, addresses the potential for division by zero and simplifies the expressions for the roots. The formulas provided are specific to the equation `y^3 + 3*p*y - 2*q = 0`; a more general cubic equation would require additional transformations to bring it into this special form.

### Dependencies
*`COMPLEX_FIELD`

### Porting notes (optional)
When porting to other proof assistants, care must be taken to define complex numbers and their arithmetic properties correctly. The power operation pow` will also need to be available for complex exponents. The handling of conditional expressions (if-then-else) might differ syntactically across systems, but the logical meaning should be preserved. Systems with strong automation for algebraic simplification will likely make the proof easier to reproduce.


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
For complex numbers `a`, `b`, `c`, and `d`, if `a` is not equal to `Cx(&0)`, let `p` be `(Cx(&3) * a * c - b pow 2) / (Cx(&9) * a pow 2)` and `q` be `(Cx(&9) * a * b * c - Cx(&2) * b pow 3 - Cx(&27) * a pow 2 * d) / (Cx(&54) * a pow 3)`. Further, let `s` be `csqrt(q pow 2 + p pow 3)`, `s1` be `ccbrt(Cx(&2) * q)` if `p` is `Cx(&0)` and `ccbrt(q + s)` otherwise,
`s2` be `--s1 * (Cx(&1) + ii * csqrt(Cx(&3))) / Cx(&2)`, and `s3` be `--s1 * (Cx(&1) - ii * csqrt(Cx(&3))) / Cx(&2)`.
Then, if `p` is `Cx(&0)`, `a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0)` if and only if `x = s1 - b / (Cx(&3) * a)` or `x = s2 - b / (Cx(&3) * a)` or `x = s3 - b / (Cx(&3) * a)`.
Otherwise, `s1` is not `Cx(&0)` and `a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0)` if and only if `x = s1 - p / s1 - b / (Cx(&3) * a)` or `x = s2 - p / s2 - b / (Cx(&3) * a)` or `x = s3 - p / s3 - b / (Cx(&3) * a)`.

### Informal sketch
The theorem provides an explicit formula for the roots of a cubic equation with complex coefficients. The proof proceeds as follows:

- First, the equation `a * x pow 3 + b * x pow 2 + c * x + d = Cx(&0)` is reduced to the depressed cubic form `y pow 3 + Cx(&3) * p * y - Cx(&2) * q = Cx(&0)` by the substitution `y = x + b / (Cx(&3) * a)`. This reduction is justified by `CUBIC_REDUCTION`.
- Then, the depressed cubic is solved using the Cardano's method.
- The solutions for `y` are expressed in terms of complex square roots and cube roots using the `csqrt` and `ccbrt` functions. The theorem `CUBIC_BASIC` is used to represent the solutions to the depressed cubic.
- Finally, the solutions for `x` are obtained by reversing the initial substitution. Several lemmas, including `CSQRT` and `CCBRT` are used to discharge the assumptions about the correct handling of the case where `p = 0`.

### Mathematical insight
This theorem provides a closed-form solution for the roots of a cubic equation using Cardano's method. It is a fundamental result in complex analysis and algebra. The theorem is important because it shows that cubic equations can be solved explicitly using radicals.

### Dependencies
- `CUBIC_REDUCTION`
- `CUBIC_BASIC`
- `CSQRT`
- `CCBRT`
- `COMPLEX_RING`
- `COMPLEX_POW_II_2`


---

