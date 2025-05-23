# constructible.ml

## Overview

Number of statements: 49

The `constructible.ml` file formalizes the non-constructibility of irrational cubic equation solutions, specifically addressing the impossibility of trisecting an angle or constructing the cube using traditional geometric constructions. It proves two classic impossibility results, drawing on elementary methods presented in Dickson's "First Course in the Theory of Equations". The file relies on imports from `prime.ml`, `floor.ml`, and `transcendentals.ml` to establish its results. It contributes to the library by providing a formal proof of these fundamental limitations in geometric construction.

## STEP_LEMMA

### Name of formal statement
STEP_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let STEP_LEMMA = prove
 (`!P. (!n. P(&n)) /\
       (!x. P x ==> P(--x)) /\
       (!x. P x /\ ~(x = &0) ==> P(inv x)) /\
       (!x y. P x /\ P y ==> P(x + y)) /\
       (!x y. P x /\ P y ==> P(x * y))
       ==> !a b c z u v s.
               P a /\ P b /\ P c /\
               z pow 3 + a * z pow 2 + b * z + c = &0 /\
               P u /\ P v /\ P(s * s) /\ z = u + v * s
               ==> ?w. P w /\ w pow 3 + a * w pow 2 + b * w + c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `v * s = &0` THENL
   [ASM_REWRITE_TAC[REAL_ADD_RID] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`A = a * s pow 2 * v pow 2 + &3 * s pow 2 * u * v pow 2 +
         a * u pow 2 + u pow 3 +  b * u + c`;
    `B = s pow 2 * v pow 3 + &2 * a * u * v + &3 * u pow 2 * v + b * v`] THEN
  SUBGOAL_THEN `A + B * s = &0` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_CASES_TAC `(P:real->bool) s` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `B = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `~P(s:real)` THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_FIELD
     `A + B * s = &0 ==> ~(B = &0) ==> s = --A / B`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[REAL_ARITH `x pow 3 = x * x * x`; REAL_POW_2] THEN
    REPEAT(FIRST_ASSUM MATCH_ACCEPT_TAC ORELSE
           (FIRST_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC));
    ALL_TAC] THEN
  EXISTS_TAC `--(a + &2 * u)` THEN ASM_SIMP_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check ((not) o is_forall o concl))) THEN
  CONV_TAC REAL_RING)
```

### Informal statement
For all properties `P` of real numbers that satisfy the following conditions:
- `P` holds for all natural numbers,
- `P` holds for the negation of any number for which `P` holds,
- `P` holds for the multiplicative inverse of any non-zero number for which `P` holds,
- `P` holds for the sum of any two numbers for which `P` holds,
- `P` holds for the product of any two numbers for which `P` holds,
the following statement is true:
For all real numbers `a`, `b`, `c`, `z`, `u`, `v`, and `s`, if
- `P` holds for `a`, `b`, and `c`,
- `z` is a root of the cubic equation `z^3 + a*z^2 + b*z + c = 0`,
- `P` holds for `u` and `v`, and `P` holds for `s^2`, and `z = u + v*s`,
then there exists a real number `w` such that `P` holds for `w` and `w` is also a root of the same cubic equation.

### Informal sketch
* The proof starts by assuming the conditions on `P` and the existence of `z`, `u`, `v`, and `s` satisfying the given equations.
* It then proceeds by cases, first considering whether `v*s = 0`.
* If `v*s = 0`, it simplifies the equation using `REAL_ADD_RID`.
* Otherwise, it substitutes `z = u + v*s` into the cubic equation and rearranges terms to form expressions `A` and `B`.
* It then assumes `A + B*s = 0` and considers whether `s` satisfies `P` or not.
* If `s` satisfies `P`, it directly obtains a contradiction.
* If `s` does not satisfy `P`, it assumes `B = 0` and derives a contradiction by showing that `s` must equal `--A/B`, which leads to a contradiction with the assumption that `s` does not satisfy `P`.
* Finally, it constructs a solution `w = --(a + 2*u)` and verifies that `w` satisfies the cubic equation and `P`.

### Mathematical insight
This theorem is crucial for proving the non-constructibility of certain geometric constructions, such as trisecting an angle or constructing the cube root of a number, using only traditional geometric methods. It provides a fundamental limit on what can be achieved through such constructions by showing that certain algebraic equations cannot be solved within the realm of constructible numbers.

### Dependencies
* `REAL_ADD_RID`
* `REAL_FIELD`
* `REAL_ARITH`
* `REAL_POW_2`
* `CONTRAPPOS_THM`
* `MATCH_MP`
* `MP_TAC`
* `SYM`
* `UNDISCH_TAC`
* `ONCE_REWRITE_TAC`
* `GSYM`
* `DISCH_TAC`
* `REWRITE_TAC`
* `FIRST_X_ASSUM`
* `MATCH_ACCEPT_TAC`
* `EXPAND_TAC`
* `CONJ_TAC`
* `EXISTS_TAC`
* `ASM_SIMP_TAC`
* `CONV_TAC`
* `check`
* `is_forall`
* `concl` 

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of real numbers, especially the `REAL_FIELD` and `REAL_ARITH` theorems, as they may have different formulations or requirements in other systems. Additionally, the use of `MATCH_MP` and `MP_TAC` tactics may need to be adapted to the target system's tactic language. The proof's case analysis and the construction of the solution `w` should be straightforward to translate, but verifying the properties of `w` may require careful attention to the algebraic manipulations and the application of `CONV_TAC REAL_RING`.

---

## STEP_LEMMA_SQRT

### Name of formal statement
STEP_LEMMA_SQRT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let STEP_LEMMA_SQRT = prove
 (`!P. (!n. P(&n)) /\
       (!x. P x ==> P(--x)) /\
       (!x. P x /\ ~(x = &0) ==> P(inv x)) /\
       (!x y. P x /\ P y ==> P(x + y)) /\
       (!x y. P x /\ P y ==> P(x * y))
       ==> !a b c z u v s.
               P a /\ P b /\ P c /\
               z pow 3 + a * z pow 2 + b * z + c = &0 /\
               P u /\ P v /\ P(s) /\ &0 <= s /\ z = u + v * sqrt(s)
               ==> ?w. P w /\ w pow 3 + a * w pow 2 + b * w + c = &0`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP STEP_LEMMA) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[SQRT_POW_2; REAL_POW_2])
```

### Informal statement
For all properties P, if P holds for all natural numbers, and for all x, if P(x) then P(-x), and for all x not equal to 0, if P(x) then P(1/x), and for all x and y, if P(x) and P(y) then P(x + y) and P(x * y), then for all a, b, c, z, u, v, and s, if P(a), P(b), P(c), z^3 + a*z^2 + b*z + c = 0, P(u), P(v), P(s), 0 ≤ s, and z = u + v*sqrt(s), then there exists a w such that P(w) and w^3 + a*w^2 + b*w + c = 0.

### Informal sketch
* The proof starts by assuming a property P that satisfies certain conditions, including closure under negation, inversion, addition, and multiplication.
* It then proceeds to apply these conditions to a polynomial equation z^3 + a*z^2 + b*z + c = 0, where z can be expressed as u + v*sqrt(s) for some u, v, and s.
* The `GEN_TAC` and `DISCH_THEN` tactics are used to manage assumptions and discharge them as needed.
* The `MATCH_MP` tactic is used to apply the `STEP_LEMMA` to the current goal, and `ASM_MESON_TAC` is used to apply the `SQRT_POW_2` and `REAL_POW_2` theorems to solve the goal.
* The key idea is to use the properties of P to find a suitable w that satisfies the polynomial equation.

### Mathematical insight
This theorem appears to be related to the properties of polynomials and their roots, particularly in the context of algebraic numbers and fields. The `STEP_LEMMA_SQRT` theorem seems to provide a way to find a root of a cubic polynomial under certain conditions, using the properties of a given predicate P. The theorem has implications for algebraic geometry and number theory, particularly in the study of algebraic curves and varieties.

### Dependencies
* `STEP_LEMMA`
* `SQRT_POW_2`
* `REAL_POW_2`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the properties of the predicate P are correctly translated and that the polynomial equation is properly represented. Additionally, the `GEN_TAC`, `DISCH_THEN`, `MATCH_MP`, and `ASM_MESON_TAC` tactics may need to be replaced with equivalent tactics in the target proof assistant. The `SQRT_POW_2` and `REAL_POW_2` theorems may also need to be ported or re-proved in the target system.

---

## radical_RULES,radical_INDUCT,radical_CASES

### Name of formal statement
radical_RULES,radical_INDUCT,radical_CASES

### Type of the formal statement
new_inductive_definition

### Formal Content
```ocaml
let radical_RULES,radical_INDUCT,radical_CASES = new_inductive_definition
 `(!x. rational x ==> radical x) /\
  (!x. radical x ==> radical (--x)) /\
  (!x. radical x /\ ~(x = &0) ==> radical (inv x)) /\
  (!x y. radical x /\ radical y ==> radical (x + y)) /\
  (!x y. radical x /\ radical y ==> radical (x * y)) /\
  (!x. radical x /\ &0 <= x ==> radical (sqrt x))`
```

### Informal statement
For all x, if x is rational, then x is radical. For all x, if x is radical, then its negation is also radical. For all x, if x is radical and not equal to zero, then its inverse is radical. For all x and y, if x and y are both radical, then their sum and product are also radical. For all x, if x is radical and non-negative, then its square root is radical.

### Informal sketch
* The definition of `radical` is inductive, covering several base cases and recursive rules.
* The base case includes rational numbers, implying they are all `radical`.
* Recursive rules allow for the construction of new `radical` numbers by:
  + Negating existing `radical` numbers
  + Taking the inverse of non-zero `radical` numbers
  + Adding or multiplying `radical` numbers
  + Taking the square root of non-negative `radical` numbers
* The `new_inductive_definition` `radical_RULES,radical_INDUCT,radical_CASES` encapsulates these rules for defining and working with `radical` numbers.

### Mathematical insight
The concept of `radical` numbers, as defined here, encompasses numbers that can be expressed using rational numbers, addition, subtraction, multiplication, division, and square roots. This definition is foundational for exploring algebraic properties and relationships among such numbers, especially in the context of field extensions and Galois theory.

### Dependencies
* `rational`
* `--` (negation)
* `inv` (inverse)
* `+` (addition)
* `*` (multiplication)
* `sqrt` (square root)
* `&0` (zero)

### Porting notes
When translating this definition into another proof assistant, pay close attention to how each system handles inductive definitions, especially those involving multiple rules and recursive constructions. Ensure that the target system supports a similar form of inductive definition and that the translation preserves the logical structure and quantifiers. Note that differences in handling binders, function definitions, or the treatment of rational and radical numbers may require adjustments to the ported code.

---

## RADICAL_RULES

### Name of formal statement
RADICAL_RULES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_RULES = prove
 (`(!n. radical(&n)) /\
   (!x. rational x ==> radical x) /\
   (!x. radical x ==> radical (--x)) /\
   (!x. radical x /\ ~(x = &0) ==> radical (inv x)) /\
   (!x y. radical x /\ radical y ==> radical (x + y)) /\
   (!x y. radical x /\ radical y ==> radical (x - y)) /\
   (!x y. radical x /\ radical y ==> radical (x * y)) /\
   (!x y. radical x /\ radical y /\ ~(y = &0) ==> radical (x / y)) /\
   (!x n. radical x ==> radical(x pow n)) /\
   (!x. radical x /\ &0 <= x ==> radical (sqrt x))`,
  SIMP_TAC[real_div; real_sub; radical_RULES; RATIONAL_NUM] THEN
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[radical_RULES; real_pow; RATIONAL_NUM])
```

### Informal statement
For all natural numbers `n`, `n` is radical. For all `x`, if `x` is rational, then `x` is radical. For all `x`, if `x` is radical, then its negation `--x` is radical. For all `x`, if `x` is radical and not equal to 0, then its inverse `inv x` is radical. For all `x` and `y`, if `x` and `y` are radical, then their sum `x + y`, difference `x - y`, and product `x * y` are radical. For all `x` and `y`, if `x` and `y` are radical and `y` is not equal to 0, then their quotient `x / y` is radical. For all `x` and natural numbers `n`, if `x` is radical, then `x` raised to the power `n` is radical. For all `x`, if `x` is radical and greater than or equal to 0, then its square root `sqrt x` is radical.

### Informal sketch
* The proof starts with a set of assumptions about the `radical` property, including its behavior with respect to natural numbers, rational numbers, negation, inversion, addition, subtraction, multiplication, division, exponentiation, and square roots.
* The `SIMP_TAC` tactic is applied to simplify the statement using the `real_div`, `real_sub`, `radical_RULES`, and `RATIONAL_NUM` theorems.
* The `GEN_TAC` tactic is used to generalize the statement.
* The `INDUCT_TAC` tactic is applied to perform induction.
* The `ASM_SIMP_TAC` tactic is used to simplify the inductive step using the `radical_RULES`, `real_pow`, and `RATIONAL_NUM` theorems.
* Key steps involve recognizing the closure properties of the `radical` relation under various algebraic operations and the preservation of this property under certain conditions.

### Mathematical insight
The `RADICAL_RULES` theorem provides a comprehensive set of rules for manipulating expressions involving the `radical` property, which is likely related to the concept of radical numbers or expressions in algebra. This theorem is important because it establishes a foundation for reasoning about radical expressions and their behavior under various operations, which is crucial in many areas of mathematics, such as algebra, geometry, and analysis.

### Dependencies
#### Theorems
* `real_div`
* `real_sub`
* `radical_RULES`
* `RATIONAL_NUM`
* `real_pow`

### Porting notes
When porting this theorem to another proof assistant, it is essential to carefully translate the `radical` property and its associated rules, ensuring that the same level of generality and expressiveness is maintained. Special attention should be given to the handling of binders, quantifiers, and the interaction between the `radical` property and various algebraic operations. Additionally, the porting process may require adapting the proof strategy to the target system's tactics and automation capabilities.

---

## RADICAL_TAC

### Name of formal statement
RADICAL_TAC

### Type of the formal statement
Tactic definition

### Formal Content
```ocaml
let RADICAL_TAC =
  REPEAT(MATCH_ACCEPT_TAC (CONJUNCT1 RADICAL_RULES) ORELSE
         (MAP_FIRST MATCH_MP_TAC(tl(tl(CONJUNCTS RADICAL_RULES))) THEN
          REPEAT CONJ_TAC))
```

### Informal statement
The `RADICAL_TAC` tactic is defined as a repeated application of either accepting the first conjunct of `RADICAL_RULES` or applying a modus ponens rule using the second conjunct of `RADICAL_RULES` and then repeatedly applying conjunction introduction.

### Informal sketch
* The tactic starts by attempting to apply `MATCH_ACCEPT_TAC` to the first conjunct of `RADICAL_RULES`, which tries to solve the goal by matching the conclusion of the first conjunct with the current goal.
* If this fails, it attempts to apply `MATCH_MP_TAC` to the second conjunct of `RADICAL_RULES` (after skipping the first conjunct), which tries to match the antecedent of the second conjunct with the current goal and then applies the consequent.
* After applying `MATCH_MP_TAC`, the tactic repeatedly applies `CONJ_TAC` to introduce conjunctions.
* The `REPEAT` combinator is used to repeatedly apply these tactics until no further progress can be made.

### Mathematical insight
The `RADICAL_TAC` tactic appears to be designed to automate the application of a set of rules (`RADICAL_RULES`) to prove goals involving conjunctions. The tactic uses a combination of matching and modus ponens to apply the rules and then introduces conjunctions as needed.

### Dependencies
* `RADICAL_RULES`
* `CONJUNCT1`
* `CONJUNCTS`
* `MATCH_ACCEPT_TAC`
* `MATCH_MP_TAC`
* `MAP_FIRST`
* `REPEAT`
* `CONJ_TAC`

### Porting notes
When porting this tactic to another proof assistant, care should be taken to ensure that the equivalent of `REPEAT` and the tactic combinators (`ORELSE`, `THEN`) are used correctly. Additionally, the `MATCH_ACCEPT_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent tactics in the target system, and the handling of conjunctions and modus ponens may differ.

---

## expression_INDUCT,expression_RECURSION

### Name of formal statement
expression_INDUCT,expression_RECURSION

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let expression_INDUCT,expression_RECURSION = define_type
 "expression = Constant real
             | Negation expression
             | Inverse expression
             | Addition expression expression
             | Multiplication expression expression
             | Sqrt expression";;
```

### Informal statement
The type `expression` is defined as a recursive data type with six constructors: `Constant` of a real number, `Negation` of an expression, `Inverse` of an expression, `Addition` of two expressions, `Multiplication` of two expressions, and `Sqrt` of an expression.

### Informal sketch
* The definition of `expression` supports inductive proof by explicitly listing all possible forms an expression can take.
* The recursive nature of the definition allows for the construction of complex expressions from simpler ones using the given constructors.
* Key HOL Light terms involved include `define_type`, `Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, and `Sqrt`.
* The definition is foundational for further developments, as it provides a basis for reasoning about and manipulating expressions.

### Mathematical insight
This definition is important because it provides a formal representation of mathematical expressions that can be used for symbolic manipulation and proof. The recursive structure allows for the application of inductive proof techniques, which are crucial for establishing properties of expressions. The inclusion of various constructors enables the representation of a wide range of mathematical operations, making this definition a fundamental component of a formal system for mathematics.

### Dependencies
* `define_type`
* `real`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles recursive data types and inductive definitions. Some systems may require explicit specification of the recursive structure or the use of specific keywords for inductive definitions. Additionally, the representation of real numbers and the available constructors for expressions might differ, requiring adjustments to the definition to match the target system's capabilities.

---

## value

### Name of formal statement
value

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let value = define
  `(value(Constant x) = x) /\
   (value(Negation e) = --(value e)) /\
   (value(Inverse e) = inv(value e)) /\
   (value(Addition e1 e2) = value e1 + value e2) /\
   (value(Multiplication e1 e2) = value e1 * value e2) /\
   (value(Sqrt e) = sqrt(value e))
```

### Informal statement
The `value` function is defined as a recursive function over the structure of expressions, where:
- For a `Constant` expression `x`, `value` returns `x`.
- For a `Negation` expression `e`, `value` returns the negation of `value e`.
- For an `Inverse` expression `e`, `value` returns the inverse of `value e`.
- For an `Addition` expression `e1` and `e2`, `value` returns the sum of `value e1` and `value e2`.
- For a `Multiplication` expression `e1` and `e2`, `value` returns the product of `value e1` and `value e2`.
- For a `Sqrt` expression `e`, `value` returns the square root of `value e`.

### Informal sketch
* The definition of `value` proceeds by pattern matching on the structure of the input expression.
* Each case corresponds to a specific constructor of the expression type, such as `Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, and `Sqrt`.
* The function recursively unfolds the structure of the expression, applying the corresponding operation to the `value` of subexpressions.
* The `value` function effectively interprets the expression by evaluating it according to the defined rules.

### Mathematical insight
The `value` function provides an interpretation of expressions in a mathematical structure, where each constructor corresponds to a specific mathematical operation. This definition enables the evaluation of complex expressions by recursively applying the defined rules, effectively giving meaning to the abstract syntax of the expressions.

### Dependencies
* `Constant`
* `Negation`
* `Inverse`
* `Addition`
* `Multiplication`
* `Sqrt`
* `inv`
* `sqrt`
* `--` (negation operator)

### Porting notes
When translating this definition into other proof assistants, pay attention to the recursive nature of the `value` function and ensure that the target system supports similar forms of recursive definitions over inductive types. Additionally, consider the specific mathematical structure and operations defined here, as they may need to be adapted or reinterpreted in the context of the target system.

---

## wellformed

### Name of formal statement
wellformed

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let wellformed = define
  `(wellformed(Constant x) <=> rational x) /\
   (wellformed(Negation e) <=> wellformed e) /\
   (wellformed(Inverse e) <=> ~(value e = &0) /\ wellformed e) /\
   (wellformed(Addition e1 e2) <=> wellformed e1 /\ wellformed e2) /\
   (wellformed(Multiplication e1 e2) <=> wellformed e1 /\ wellformed e2) /\
   (wellformed(Sqrt e) <=> &0 <= value e /\ wellformed e)`;;
```

### Informal statement
The `wellformed` predicate is defined for an expression `e` as follows:
- A `Constant` expression `x` is well-formed if and only if `x` is rational.
- A `Negation` expression is well-formed if and only if its argument `e` is well-formed.
- An `Inverse` expression is well-formed if and only if its argument `e` does not have a value of 0 and `e` is well-formed.
- An `Addition` expression is well-formed if and only if both its arguments `e1` and `e2` are well-formed.
- A `Multiplication` expression is well-formed if and only if both its arguments `e1` and `e2` are well-formed.
- A `Sqrt` expression is well-formed if and only if its argument `e` has a non-negative value and `e` is well-formed.

### Informal sketch
* The definition of `wellformed` is based on the structure of the expression, with different conditions for each type of expression.
* For `Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, and `Sqrt` expressions, the definition checks the rationality, non-zero value, or non-negativity of the argument, as well as the well-formedness of subexpressions.
* The definition uses logical connectives (`/\`, `<=>`) to combine conditions for each expression type.
* Key HOL Light terms involved include `Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, `Sqrt`, `rational`, `value`, and `wellformed`.

### Mathematical insight
The `wellformed` predicate ensures that expressions are syntactically valid and semantically meaningful, preventing division by zero, square roots of negative numbers, and ensuring that constants are rational. This definition is crucial for maintaining the integrity of mathematical expressions and preventing errors in subsequent calculations.

### Dependencies
* `Constant`
* `Negation`
* `Inverse`
* `Addition`
* `Multiplication`
* `Sqrt`
* `rational`
* `value`

### Porting notes
When translating this definition to other proof assistants, pay attention to how each system handles recursive definitions, especially for `wellformed` applied to different expression types. Ensure that the target system's type system and logic can express the conditions for each expression type accurately. Additionally, consider how the target system handles the `rational` predicate and the `value` function, as these may need to be defined or imported separately.

---

## radicals

### Name of formal statement
radicals

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let radicals = define
  `(radicals(Constant x) = {}) /\
  (radicals(Negation e) = radicals e) /\
  (radicals(Inverse e) = radicals e) /\
  (radicals(Addition e1 e2) = (radicals e1) UNION (radicals e2)) /\
  (radicals(Multiplication e1 e2) = (radicals e1) UNION (radicals e2)) /\
  (radicals(Sqrt e) = e INSERT (radicals e))
```

### Informal statement
The function `radicals` is defined on expressions as follows:
- For a constant `x`, `radicals(Constant x)` is the empty set.
- For a negation `Negation e`, `radicals(Negation e)` equals `radicals e`.
- For an inverse `Inverse e`, `radicals(Inverse e)` equals `radicals e`.
- For an addition `Addition e1 e2`, `radicals(Addition e1 e2)` is the union of `radicals e1` and `radicals e2`.
- For a multiplication `Multiplication e1 e2`, `radicals(Multiplication e1 e2)` is the union of `radicals e1` and `radicals e2`.
- For a square root `Sqrt e`, `radicals(Sqrt e)` is `e` inserted into `radicals e`.

### Informal sketch
* The definition of `radicals` is given by cases on the structure of the input expression.
* For `Constant`, `Negation`, and `Inverse`, the function behaves in a straightforward manner, either returning the empty set or propagating the `radicals` computation to the argument.
* For `Addition` and `Multiplication`, `radicals` combines the results from the two operands using set union.
* For `Sqrt`, the definition inserts the argument `e` into the set of radicals of `e`, effectively accumulating the expression within its own radicals set.
* This recursive definition allows `radicals` to traverse the expression tree, collecting all subexpressions that are under a square root.

### Mathematical insight
The `radicals` function is designed to identify and collect all subexpressions within an expression that are under a square root. This is crucial in various algebraic manipulations and simplifications, where understanding the radical parts of an expression can significantly impact the applicability of certain rules or theorems. The definition ensures that `radicals` is consistent across different operations, providing a systematic way to track radical subexpressions.

### Dependencies
* `Constant`
* `Negation`
* `Inverse`
* `Addition`
* `Multiplication`
* `Sqrt`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles recursive definitions and the representation of mathematical expressions. The use of pattern matching, as seen in the HOL Light definition, might be directly supported or require alternative constructs. Additionally, consider the specific libraries or modules in the target system that deal with algebraic expressions and set operations, as these will be crucial for a faithful porting of the `radicals` function.

---

## FINITE_RADICALS

### Name of formal statement
FINITE_RADICALS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FINITE_RADICALS = prove
 (`!e. FINITE(radicals e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  SIMP_TAC[radicals; FINITE_RULES; FINITE_UNION]);;
```

### Informal statement
For all expressions `e`, the set of radicals of `e` is finite.

### Informal sketch
* The proof proceeds by induction on the structure of expressions, as indicated by `expression_INDUCT`.
* The base case and inductive step are simplified using `SIMP_TAC` with theorems `radicals`, `FINITE_RULES`, and `FINITE_UNION`, ensuring that the set of radicals for each subexpression is finite.
* The use of `MATCH_MP_TAC` suggests that the inductive hypothesis is applied to prove the finiteness of radicals for each expression `e`.

### Mathematical insight
This theorem is important because it establishes that the set of radicals of any expression is finite, which has implications for the computability and decidability of certain properties of expressions. The finiteness of radicals is a fundamental property that can be used in various mathematical constructions and proofs.

### Dependencies
* Theorems:
  + `expression_INDUCT`
  + `radicals`
  + `FINITE_RULES`
  + `FINITE_UNION`

### Porting notes
When translating this theorem into other proof assistants, special attention should be paid to the handling of induction and the `SIMP_TAC` tactic, which may have different equivalents in other systems. Additionally, the `MATCH_MP_TAC` tactic may need to be replaced with a similar tactic that applies the inductive hypothesis in the target proof assistant.

---

## WELLFORMED_RADICALS

### Name of formal statement
WELLFORMED_RADICALS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let WELLFORMED_RADICALS = prove
 (`!e. wellformed e ==> !r. r IN radicals(e) ==> &0 <= value r`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; wellformed; NOT_IN_EMPTY; IN_UNION; IN_INSERT] THEN
  MESON_TAC[]);
```

### Informal statement
For all expressions `e`, if `e` is well-formed, then for all radicals `r` in the set of radicals of `e`, the value of `r` is greater than or equal to 0.

### Informal sketch
* The proof starts by assuming an expression `e` is well-formed.
* It then considers any radical `r` that is part of the radicals of `e`.
* The proof proceeds by induction on the structure of `e`, using `expression_INDUCT`.
* The `REWRITE_TAC` step simplifies the expressions involving `radicals`, `wellformed`, and set operations like `NOT_IN_EMPTY`, `IN_UNION`, and `IN_INSERT`.
* Finally, `MESON_TAC` is used to deduce the conclusion `&0 <= value r` from the given assumptions and simplified expressions.

### Mathematical insight
This theorem establishes a fundamental property about the non-negativity of values of radicals within well-formed expressions. It's crucial for ensuring that operations involving radicals behave as expected, especially in contexts where non-negative values are required or implied.

### Dependencies
* `expression_INDUCT`
* `radicals`
* `wellformed`
* `NOT_IN_EMPTY`
* `IN_UNION`
* `IN_INSERT`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles induction, rewriting, and meson (a tactic for automatic proof). Ensure that the target system's libraries include equivalents for `expression_INDUCT`, `REWRITE_TAC`, and `MESON_TAC`, or plan how to replicate their functionality. Additionally, consider how the new system represents and manipulates expressions, radicals, and well-formedness, as these concepts are central to the theorem.

---

## RADICALS_WELLFORMED

### Name of formal statement
RADICALS_WELLFORMED

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICALS_WELLFORMED = prove
 (`!e. wellformed e ==> !r. r IN radicals e ==> wellformed r`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; wellformed; NOT_IN_EMPTY; IN_UNION; IN_INSERT] THEN
  MESON_TAC[]);;
```

### Informal statement
For all expressions `e`, if `e` is well-formed, then for all `r`, if `r` is in the set of radicals of `e`, then `r` is well-formed.

### Informal sketch
* The proof starts by assuming that an expression `e` is well-formed.
* It then considers an arbitrary `r` that is in the set of radicals of `e`.
* The proof proceeds by induction on the structure of `e`, using `expression_INDUCT`.
* The `REWRITE_TAC` step applies several definitions and properties, including `radicals`, `wellformed`, `NOT_IN_EMPTY`, `IN_UNION`, and `IN_INSERT`, to simplify the goal.
* The `MESON_TAC` step uses automated reasoning to deduce the conclusion that `r` is well-formed.

### Mathematical insight
This theorem ensures that the set of radicals of a well-formed expression only contains well-formed elements. This property is crucial for maintaining the consistency and correctness of expressions when operating on their radicals.

### Dependencies
#### Theorems and definitions
* `expression_INDUCT`
* `radicals`
* `wellformed`
* `NOT_IN_EMPTY`
* `IN_UNION`
* `IN_INSERT`

### Porting notes
When translating this theorem into another proof assistant, pay attention to the handling of induction and the application of definitions and properties during the `REWRITE_TAC` step. The `MESON_TAC` step may require equivalent automated reasoning capabilities in the target system. Additionally, ensure that the notions of well-formedness and radicals are defined and behave similarly in the target system.

---

## RADICALS_SUBSET

### Name of formal statement
RADICALS_SUBSET

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICALS_SUBSET = prove
 (`!e r. r IN radicals e ==> radicals(r) SUBSET radicals(e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; IN_UNION; NOT_IN_EMPTY; IN_INSERT; SUBSET] THEN
  MESON_TAC[]);;
```

### Informal statement
For all elements `e` and `r`, if `r` is in the set of radicals of `e`, then the set of radicals of `r` is a subset of the set of radicals of `e`.

### Informal sketch
* The proof proceeds by induction using `expression_INDUCT`, which suggests that the theorem is proven for an arbitrary `e` by considering the structure of `e`.
* The `REWRITE_TAC` step involves rewriting the `radicals` function and set operations (`IN_UNION`, `NOT_IN_EMPTY`, `IN_INSERT`, `SUBSET`) to simplify the expression and potentially reveal a clear path to the conclusion.
* The `MESON_TAC` step indicates that the proof is completed by automated reasoning, likely filling in any remaining details after the rewriting step to establish the subset relationship between `radicals(r)` and `radicals(e)`.

### Mathematical insight
This theorem provides insight into the properties of the `radicals` function, specifically showing that the radicals of any element within the set of radicals of another element are themselves contained within that set. This has implications for understanding the structure of radical sets and their relationships.

### Dependencies
* `radicals`
* `expression_INDUCT`
* `IN_UNION`
* `NOT_IN_EMPTY`
* `IN_INSERT`
* `SUBSET`

### Porting notes
When translating this theorem into another proof assistant, careful attention should be paid to the handling of the `radicals` function, the `expression_INDUCT` induction scheme, and the automation provided by `MESON_TAC`, as these may differ significantly between systems. Additionally, the rewriting steps involving `REWRITE_TAC` might need to be adapted based on how the target system handles similar set operations and function definitions.

---

## RADICAL_EXPRESSION

### Name of formal statement
RADICAL_EXPRESSION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_EXPRESSION = prove
 (`!x. radical x <=> ?e. wellformed e /\ x = value e`,
  GEN_TAC THEN EQ_TAC THEN SPEC_TAC(`x:real`,`x:real`) THENL
   [MATCH_MP_TAC radical_INDUCT THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_MESON_TAC[value; wellformed];
    SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
    MATCH_MP_TAC expression_INDUCT THEN
    REWRITE_TAC[value; wellformed] THEN SIMP_TAC[radical_RULES]])
```

### Informal statement
For all real numbers x, x is a radical if and only if there exists a well-formed expression e such that x is equal to the value of e.

### Informal sketch
* The proof proceeds by first assuming `x` is a radical and then using `radical_INDUCT` to establish that `x` can be represented as the value of a well-formed expression `e`.
* Conversely, it assumes there exists a well-formed expression `e` such that `x` equals the value of `e`, and then applies `expression_INDUCT` to show that `x` is a radical.
* Key steps involve using `MATCH_MP_TAC` for inductive reasoning, `SIMP_TAC` for simplification, and `REWRITE_TAC` for applying various theorems (`LEFT_IMP_EXISTS_THM`, `SWAP_FORALL_THM`, `IMP_CONJ`, `RIGHT_FORALL_IMP_THM`, `LEFT_FORALL_IMP_THM`, `EXISTS_REFL`) to manipulate the logical expressions.
* The `ASM_MESON_TAC` and `SIMP_TAC` with `radical_RULES` are used to finalize the proof by applying specific rules and simplifications related to radicals and well-formed expressions.

### Mathematical insight
This theorem establishes a fundamental connection between the concept of a radical and the interpretation of well-formed expressions, essentially showing that every radical can be represented as the value of some well-formed expression and vice versa. This is crucial for linking the abstract algebraic structure of radicals with their concrete representation through expressions, facilitating further reasoning and manipulation within the formal system.

### Dependencies
* Theorems:
  - `LEFT_IMP_EXISTS_THM`
  - `SWAP_FORALL_THM`
  - `IMP_CONJ`
  - `RIGHT_FORALL_IMP_THM`
  - `LEFT_FORALL_IMP_THM`
  - `EXISTS_REFL`
* Definitions:
  - `radical`
  - `wellformed`
  - `value`
* Inductive rules:
  - `radical_INDUCT`
  - `expression_INDUCT`
* Rules:
  - `radical_RULES`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how each system handles quantifiers, especially the equivalence (`<=>`) and the existential quantifier (`?e`). Also, note the use of `GEN_TAC`, `EQ_TAC`, and `SPEC_TAC` for setting up the proof structure, which may have direct analogs in other systems but could require adjustments based on the specific tactics and strategic mechanisms available. The inductive rules (`radical_INDUCT` and `expression_INDUCT`) and the specific theorems applied during the proof (e.g., `LEFT_IMP_EXISTS_THM`) will need to be either directly translated or re-proven within the target system, considering its particular formalization of real numbers, expressions, and radicals.

---

## LT_MAX

### Name of formal statement
LT_MAX

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LT_MAX = prove
 (`!a b c. a < MAX b c <=> a < b \/ a < c`,
  ARITH_TAC)
```

### Informal statement
For all real numbers a, b, and c, a is less than the maximum of b and c if and only if a is less than b or a is less than c.

### Informal sketch
* The theorem `LT_MAX` is proved using `ARITH_TAC`, which suggests that the proof involves basic arithmetic properties.
* The statement involves a universal quantifier (`!a b c`) and a biconditional (`<=>`), indicating that the proof must establish both directions of the equivalence.
* The `MAX` function is used to denote the maximum of two numbers, and the proof likely relies on the definition and properties of this function.
* The `ARITH_TAC` tactic implies that the proof is relatively straightforward and does not require complex logical manipulations.

### Mathematical insight
The `LT_MAX` theorem provides a fundamental property of the maximum function, relating it to the less-than relation. This property is essential in various mathematical contexts, such as order theory and real analysis. The theorem's importance lies in its ability to simplify expressions involving the maximum function and inequalities.

### Dependencies
* `MAX` 
* `ARITH_TAC` 

### Porting notes
When porting this theorem to other proof assistants, pay attention to the handling of the maximum function and the less-than relation. Some systems may require explicit definitions or properties of these concepts, while others may have them built-in. Additionally, the `ARITH_TAC` tactic may need to be replaced with equivalent tactics or proof strategies in the target system.

---

## depth

### Name of formal statement
depth

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let depth = define
  `(depth(Constant x) = 0) /\
   (depth(Negation e) = depth e) /\
   (depth(Inverse e) = depth e) /\
   (depth(Addition e1 e2) = MAX (depth e1) (depth e2)) /\
   (depth(Multiplication e1 e2) = MAX (depth e1) (depth e2)) /\
   (depth(Sqrt e) = 1 + depth e)`;;
```

### Informal statement
The `depth` function is defined as follows: 
- The depth of a `Constant` expression `x` is 0.
- The depth of a `Negation` expression `e` is the same as the depth of `e`.
- The depth of an `Inverse` expression `e` is the same as the depth of `e`.
- The depth of an `Addition` expression of `e1` and `e2` is the maximum of the depths of `e1` and `e2`.
- The depth of a `Multiplication` expression of `e1` and `e2` is the maximum of the depths of `e1` and `e2`.
- The depth of a `Sqrt` expression `e` is 1 plus the depth of `e`.

### Informal sketch
* The definition of `depth` is based on a recursive approach, where the depth of each type of expression is defined in terms of the depths of its subexpressions.
* For `Constant`, `Negation`, and `Inverse` expressions, the depth is either a base case (`Constant`) or directly inherited from the subexpression (`Negation` and `Inverse`).
* For `Addition` and `Multiplication`, the depth is determined by the maximum depth of the two subexpressions `e1` and `e2`.
* The `Sqrt` expression increments the depth of its subexpression `e` by 1.
* This recursive structure allows for the computation of the depth of any expression by breaking it down into its constituent parts and applying these rules.

### Mathematical insight
The `depth` function provides a way to measure the complexity of expressions by counting the maximum number of nested operations. This is useful in various mathematical and computational contexts, such as analyzing the complexity of algorithms or proving properties about expressions. The definition reflects a natural, intuitive notion of complexity, where constants are considered simplest, and square roots introduce an additional layer of complexity.

### Dependencies
* `Constant`
* `Negation`
* `Inverse`
* `Addition`
* `Multiplication`
* `Sqrt`
* `MAX` 

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles recursive definitions and the `MAX` function. Some systems may require explicit proofs of termination for recursive definitions or have different built-in functions for computing the maximum of two values. Additionally, the representation of expressions (`Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, `Sqrt`) may vary, requiring adjustments to the definition of `depth` accordingly.

---

## IN_RADICALS_SMALLER

### Name of formal statement
IN_RADICALS_SMALLER

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IN_RADICALS_SMALLER = prove
 (`!r s. s IN radicals(r) ==> depth(s) < depth(r)`,
  MATCH_MP_TAC expression_INDUCT THEN REWRITE_TAC[radicals; depth] THEN
  REWRITE_TAC[IN_UNION; NOT_IN_EMPTY; IN_INSERT; LT_MAX] THEN
  MESON_TAC[ARITH_RULE `s = a \/ s < a ==> s < 1 + a`])
```

### Informal statement
For all `r` and `s`, if `s` is in the set of radicals of `r`, then the depth of `s` is less than the depth of `r`.

### Informal sketch
* The proof starts by applying `expression_INDUCT`, which suggests a structural induction over the `expression` type.
* It then applies `REWRITE_TAC` with several theorems (`radicals`, `depth`, `IN_UNION`, `NOT_IN_EMPTY`, `IN_INSERT`, `LT_MAX`) to transform the goal into a more manageable form.
* The `MESON_TAC` with the `ARITH_RULE` suggests using basic arithmetic properties to conclude that `s` is less than `1 + a` if `s` equals `a` or `s` is less than `a`, which is used to establish the depth relationship between `s` and `r`.
* The use of `MATCH_MP_TAC` implies a match with a previously proven statement, potentially simplifying the inductive step.

### Mathematical insight
This theorem provides a crucial property about the relationship between elements in the set of radicals of a given expression `r` and their depths compared to `r`. It ensures that any element `s` within the radicals of `r` has a strictly smaller depth, which can be foundational in further proofs involving the manipulation or analysis of these radicals, contributing to the structural understanding of expressions and their radical sets.

### Dependencies
* Theorems:
  - `expression_INDUCT`
  - `radicals`
  - `depth`
  - `IN_UNION`
  - `NOT_IN_EMPTY`
  - `IN_INSERT`
  - `LT_MAX`
  - `ARITH_RULE`
* Definitions:
  - `radicals`
  - `depth`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles inductive types and their associated induction principles (`expression_INDUCT` here). Additionally, the `REWRITE_TAC` and `MESON_TAC` steps may need to be rephrased using the target system's equivalent tactics for rewriting and first-order reasoning, respectively. The arithmetic rule used might also require a different formulation depending on the proof assistant's arithmetic library.

---

## NOT_IN_OWN_RADICALS

### Name of formal statement
NOT_IN_OWN_RADICALS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_IN_OWN_RADICALS = prove
 (`!r. ~(r IN radicals r)`,
  MESON_TAC[IN_RADICALS_SMALLER; LT_REFL])
```

### Informal statement
For all `r`, it is not the case that `r` is an element of the radicals of `r`.

### Informal sketch
* The proof starts with a universal quantification over `r`.
* The goal is to show that `r` does not belong to its own radicals.
* The `MESON_TAC` tactic is applied with two premises: `IN_RADICALS_SMALLER` and `LT_REFL`.
* These premises suggest that the proof involves showing a contradiction or using a property of radicals and a reflexive relation.

### Mathematical insight
This theorem formalizes the notion that an element cannot be a radical of itself, which is a fundamental property in certain algebraic or order-theoretic contexts. Understanding this theorem requires grasping the concept of radicals and how elements relate to their own radicals.

### Dependencies
#### Theorems
* `IN_RADICALS_SMALLER`
* `LT_REFL`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how universal quantification and set membership are handled. Additionally, ensure that the `IN_RADICALS_SMALLER` and `LT_REFL` theorems (or their equivalents) are established in the target system, as they are crucial for the proof. The automation provided by `MESON_TAC` may need to be replicated using tactics or automation available in the target proof assistant.

---

## RADICALS_EMPTY_RATIONAL

### Name of formal statement
RADICALS_EMPTY_RATIONAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICALS_EMPTY_RATIONAL = prove
 (`!e. wellformed e /\ radicals e = {} ==> rational(value e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[wellformed; value; radicals; EMPTY_UNION; NOT_INSERT_EMPTY] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED]);;
```

### Informal statement
For all expressions `e`, if `e` is well-formed and the set of radicals of `e` is empty, then the value of `e` is rational.

### Informal sketch
* The proof proceeds by induction on the structure of the expression `e`, as indicated by `expression_INDUCT`.
* It first establishes that the expression is well-formed and that its set of radicals is empty.
* The `REWRITE_TAC` step applies various definitions and properties, including those for `wellformed`, `value`, `radicals`, and set operations like `EMPTY_UNION` and `NOT_INSERT_EMPTY`, to simplify the expression.
* The proof then uses `CONJ_TAC` and `GEN_TAC` to handle conjunctions and generalize variables, respectively.
* The `DISCH_THEN` and `MP_TAC` combination is used to discharge assumptions and apply them as premises in a modus ponens step.
* Finally, `ASM_SIMP_TAC` with `RATIONAL_CLOSED` simplifies the expression under the assumption, leveraging the fact that rational numbers are closed under certain operations.
* Key HOL Light terms involved include `wellformed`, `value`, `radicals`, and `RATIONAL_CLOSED`.

### Mathematical insight
This theorem is important because it establishes a relationship between the syntactic property of an expression (being well-formed and having no radicals) and a semantic property (having a rational value). This is crucial in mathematical reasoning about expressions, especially in algebra and analysis, where rationality of expressions can have significant implications.

### Dependencies
#### Theorems
* `RATIONAL_CLOSED`
#### Definitions
* `wellformed`
* `value`
* `radicals`
* `EMPTY_UNION`
* `NOT_INSERT_EMPTY`
#### Inductive rules
* `expression_INDUCT`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to how the target system handles induction, especially if it has a different mechanism for defining and using inductive rules like `expression_INDUCT`. Additionally, the treatment of rational numbers and the properties like `RATIONAL_CLOSED` may vary, requiring adjustments in how the theorem is stated and proved.

---

## FINITE_MAX

### Name of formal statement
FINITE_MAX

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FINITE_MAX = prove
 (`!s. FINITE s ==> ~(s = {}) ==> ?b:num. b IN s /\ !a. a IN s ==> a <= b`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:num->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; UNWIND_THM2; LE_REFL] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS])
```

### Informal statement
For all sets `s`, if `s` is finite and not empty, then there exists a number `b` in `s` such that for all `a` in `s`, `a` is less than or equal to `b`.

### Informal sketch
* The proof starts by applying `FINITE_INDUCT_STRONG` to establish the base case and inductive step for finite sets.
* It then handles the case where `s` is not empty by using `ASM_CASES_TAC` to consider the scenario where `s` equals the empty set, which is ruled out by the premise `~(s = {})`.
* The proof utilizes `ASM_SIMP_TAC` to simplify expressions involving `NOT_IN_EMPTY`, `UNWIND_THM2`, and `LE_REFL`, which help in managing the inductive step and establishing the relationship between elements in `s`.
* The `REWRITE_TAC` tactic is applied with various theorems (`RIGHT_OR_DISTRIB`, `EXISTS_OR_THM`, `UNWIND_THM2`) to transform the expression and prepare it for the final application of `MESON_TAC`.
* `MESON_TAC` is used with `LE_CASES`, `LE_REFL`, and `LE_TRANS` to derive the conclusion that there exists a `b` in `s` such that all `a` in `s` are less than or equal to `b`, thus establishing the maximum element in a non-empty finite set.

### Mathematical insight
The `FINITE_MAX` theorem is crucial because it guarantees the existence of a maximum element in any non-empty finite set of numbers. This is a fundamental property in mathematics, especially in combinatorics, algebra, and analysis, where the concept of a maximum or supremum is essential. The theorem's proof by induction over finite sets showcases a common technique in proving statements about finite structures.

### Dependencies
* Theorems:
  + `FINITE_INDUCT_STRONG`
  + `NOT_INSERT_EMPTY`
  + `IN_INSERT`
  + `NOT_IN_EMPTY`
  + `UNWIND_THM2`
  + `LE_REFL`
  + `RIGHT_OR_DISTRIB`
  + `EXISTS_OR_THM`
  + `LE_CASES`
  + `LE_TRANS`
* Definitions:
  + `FINITE`
  + `IN`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles finite sets, induction, and the `MESON_TAC` style of automated reasoning. The `FINITE_INDUCT_STRONG` tactic and the various rewrite and simplification tactics may have direct counterparts or require manual simulation using the target system's tactics and automation. Additionally, the representation of sets and the `IN` relation might differ, requiring adjustments to the proof script.

---

## RADICAL_TOP

### Name of formal statement
RADICAL_TOP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_TOP = prove
 (`!e. ~(radicals e = {})
       ==> ?r. r IN radicals e /\
               !s. s IN radicals(e) ==> ~(r IN radicals s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE depth (radicals e)` FINITE_MAX) THEN
  ASM_SIMP_TAC[IMAGE_EQ_EMPTY; FINITE_IMAGE; FINITE_RADICALS] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  MESON_TAC[IN_RADICALS_SMALLER; NOT_LT])
```

### Informal statement
For all `e`, if the set of radicals of `e` is not empty, then there exists a radical `r` in the set of radicals of `e` such that for all `s` in the set of radicals of `e`, `r` is not in the set of radicals of `s`.

### Informal sketch
* The proof starts by assuming that the set of radicals of `e` is not empty.
* It then uses the `FINITE_MAX` theorem to establish the existence of a maximal element in the image of `depth` applied to the set of radicals of `e`.
* The proof then applies various simplification and rewriting steps using `ASM_SIMP_TAC` and `REWRITE_TAC` to transform the goal into a more manageable form.
* The `MESON_TAC` tactic is used to discharge the resulting goal using the `IN_RADICALS_SMALLER` and `NOT_LT` theorems.
* Key steps involve recognizing the finiteness of the set of radicals and the relationship between radicals and their depths.

### Mathematical insight
This theorem provides a crucial property of radicals, namely that every non-empty set of radicals contains a "minimal" radical that is not contained in any other radical in the set. This property is essential in various applications, such as in the study of radical ideals and their properties.

### Dependencies
* Theorems:
	+ `FINITE_MAX`
	+ `IN_RADICALS_SMALLER`
	+ `NOT_LT`
* Definitions:
	+ `radicals`
	+ `depth`
* Axioms:
	+ None

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of binders and the `IN` predicate, as these may differ between systems. Additionally, the `MESON_TAC` tactic may need to be replaced with a equivalent tactic or a manual proof step, depending on the target system's automation capabilities.

---

## RADICAL_CANONICAL_TRIVIAL

### Name of formal statement
RADICAL_CANONICAL_TRIVIAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_CANONICAL_TRIVIAL = prove
 (`!e r.
     (r IN radicals e
            ==> (?a b.
                   wellformed a /\
                   wellformed b /\
                   value e = value a + value b * sqrt (value r) /\
                   radicals a SUBSET radicals e DELETE r /\
                   radicals b SUBSET radicals e DELETE r /\
                   radicals r SUBSET radicals e DELETE r))
     ==> wellformed e
         ==> ?a b. wellformed a /\
                   wellformed b /\
                   value e = value a + value b * sqrt (value r) /\
                   radicals a SUBSET (radicals e UNION radicals r) DELETE r /\
                   radicals b SUBSET (radicals e UNION radicals r) DELETE r /\
                   radicals r SUBSET (radicals e UNION radicals r) DELETE r`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `r IN radicals e` THEN ASM_SIMP_TAC[] THENL
   [DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN SET_TAC[];
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`e:expression`; `Constant(&0)`] THEN
    ASM_REWRITE_TAC[wellformed; value; radicals] THEN
    REWRITE_TAC[RATIONAL_NUM; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    UNDISCH_TAC `~(r IN radicals e)` THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN SET_TAC[]])
```

### Informal statement
For all expressions `e` and `r`, if `r` is in the radicals of `e`, then there exist expressions `a` and `b` such that `a` and `b` are well-formed, the value of `e` equals the value of `a` plus the value of `b` times the square root of the value of `r`, the radicals of `a` are a subset of the radicals of `e` minus `r`, the radicals of `b` are a subset of the radicals of `e` minus `r`, and the radicals of `r` are a subset of the radicals of `e` minus `r`. Furthermore, if `e` is well-formed, then there exist `a` and `b` such that `a` and `b` are well-formed, the value of `e` equals the value of `a` plus the value of `b` times the square root of the value of `r`, the radicals of `a` are a subset of the union of the radicals of `e` and the radicals of `r` minus `r`, the radicals of `b` are a subset of the union of the radicals of `e` and the radicals of `r` minus `r`, and the radicals of `r` are a subset of the union of the radicals of `e` and the radicals of `r` minus `r`.

### Informal sketch
* The proof proceeds by cases on whether `r` is in the radicals of `e`.
* If `r` is in the radicals of `e`, the proof uses the `MONO_EXISTS` tactic to introduce existential quantifiers for `a` and `b`, and then applies the `SET_TAC` to establish the required properties.
* If `r` is not in the radicals of `e`, the proof uses the `EXISTS_TAC` to introduce `e` and `Constant(&0)` as witnesses for `a` and `b`, and then applies various rewrite tactics to simplify the resulting expressions.
* The `NOT_IN_OWN_RADICALS` theorem is used to establish a key property about the radicals of `r`.
* The `ASM_REWRITE_TAC` and `REWRITE_TAC` are used to simplify expressions involving `wellformed`, `value`, and `radicals`.

### Mathematical insight
This theorem provides a way to rearrange an expression `e` in a canonical way, by expressing it as a sum of two well-formed expressions `a` and `b` times the square root of a radical `r`. The theorem ensures that the radicals of `a`, `b`, and `r` are properly contained in the radicals of `e` and `r`. This canonical form can be useful for simplifying expressions and proving properties about them.

### Dependencies
* Theorems:
	+ `NOT_IN_OWN_RADICALS`
	+ `MONO_EXISTS`
* Definitions:
	+ `wellformed`
	+ `value`
	+ `radicals`
* Tactics:
	+ `ASM_CASES_TAC`
	+ `ASM_SIMP_TAC`
	+ `MATCH_MP_TAC`
	+ `GEN_TAC`
	+ `SET_TAC`
	+ `EXISTS_TAC`
	+ `ASM_REWRITE_TAC`
	+ `REWRITE_TAC`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to preserve the exact logical structure and quantifier scope. The `MONO_EXISTS` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `NOT_IN_OWN_RADICALS` theorem and the `wellformed`, `value`, and `radicals` definitions will need to be ported as well.

---

## RADICAL_CANONICAL

### Name of formal statement
RADICAL_CANONICAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_CANONICAL = prove
 (`!e. wellformed e /\ ~(radicals e = {})
       ==> ?r. r IN radicals(e) /\
               ?a b. wellformed(Addition a (Multiplication b (Sqrt r))) /\
                     value e = value(Addition a (Multiplication b (Sqrt r))) /\
                     (radicals a) SUBSET (radicals(e) DELETE r) /\
                     (radicals b) SUBSET (radicals(e) DELETE r) /\
                     (radicals r) SUBSET (radicals(e) DELETE r)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP RADICAL_TOP) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:expression` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= value r /\ wellformed r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[WELLFORMED_RADICALS; RADICALS_WELLFORMED]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`wellformed e`; `r IN radicals e`] THEN
  ASM_REWRITE_TAC[IMP_IMP; wellformed; value; GSYM CONJ_ASSOC] THEN
  SPEC_TAC(`e:expression`,`e:expression`) THEN
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[wellformed; radicals; value; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; IN_UNION] THEN REPEAT CONJ_TAC THEN
  X_GEN_TAC `e1:expression` THEN TRY(X_GEN_TAC `e2:expression`) THENL
   [DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:expression`; `b:expression`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`Negation a`; `Negation b`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals] THEN REAL_ARITH_TAC;

    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:expression`; `b:expression`] THEN
    ASM_CASES_TAC `value b * sqrt(value r) = value a` THENL
     [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`Inverse(Multiplication (Constant(&2)) a)`; `Constant(&0)`] THEN
      ASM_REWRITE_TAC[value; radicals; wellformed] THEN
      REWRITE_TAC[RATIONAL_NUM; EMPTY_SUBSET; CONJ_ASSOC] THEN CONJ_TAC THENL
       [UNDISCH_TAC `~(value a + value a = &0)` THEN CONV_TAC REAL_FIELD;
        REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`Multiplication a (Inverse
        (Addition (Multiplication a a)
                  (Multiplication (Multiplication b b) (Negation r))))`;
      `Multiplication (Negation b) (Inverse
        (Addition (Multiplication a a)
                  (Multiplication (Multiplication b b) (Negation r))))`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals; UNION_SUBSET] THEN
    UNDISCH_TAC `~(value b * sqrt (value r) = value a)` THEN
    UNDISCH_TAC `~(value e1 = &0)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SQRT_POW_2) THEN CONV_TAC REAL_FIELD;

    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(fun th ->
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
      MATCH_MP RADICAL_CANONICAL_TRIVIAL)) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`a1:expression`; `b1:expression`; `a2:expression`; `b2:expression`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`Addition a1 a2`; `Addition b1 b2`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN
    MP_TAC(SPECL [`e1:expression`; `r:expression`] RADICALS_SUBSET) THEN
    MP_TAC(SPECL [`e2:expression`; `r:expression`] RADICALS_SUBSET) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[];

    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(fun th ->
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o
      MATCH_MP RADICAL_CANONICAL_TRIVIAL)) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`a1:expression`; `b1:expression`; `a2:expression`; `b2:expression`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`Addition (Multiplication a1 a2)
                (Multiplication (Multiplication b1 b2) r)`;
      `Addition (Multiplication a1 b2) (Multiplication a2 b1)`] THEN
    ASM_REWRITE_TAC[value; wellformed; radicals] THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP SQRT_POW_2) THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN
    MP_TAC(SPECL [`e1:expression`; `r:expression`] RADICALS_SUBSET) THEN
    MP_TAC(SPECL [`e2:expression`; `r:expression`] RADICALS_SUBSET) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[];

    REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`Constant(&0)`; `Constant(&1)`] THEN
    REWRITE_TAC[wellformed; value; REAL_ADD_LID; REAL_MUL_LID] THEN
    REWRITE_TAC[radicals; RATIONAL_NUM] THEN
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN ASM SET_TAC[]])
```

### Informal statement
For all expressions `e`, if `e` is well-formed and the set of radicals of `e` is not empty, then there exists a radical `r` in the set of radicals of `e` and expressions `a` and `b` such that:
- `a` and `b` are well-formed,
- the value of `e` is equal to the value of `a` plus `b` times the square root of `r`,
- the set of radicals of `a` is a subset of the set of radicals of `e` with `r` removed,
- the set of radicals of `b` is a subset of the set of radicals of `e` with `r` removed,
- the set of radicals of `r` is a subset of the set of radicals of `e` with `r` removed.

### Informal sketch
* The proof proceeds by induction on the structure of the expression `e`.
* It first considers the case when `e` is a simple expression and then handles more complex cases involving addition and multiplication.
* The `RADICAL_TOP` and `MONO_EXISTS` theorems are used to establish the existence of a suitable radical `r`.
* The proof then breaks down into several cases based on the properties of `e` and `r`, using various tactics such as `ASM_REWRITE_TAC`, `REAL_ARITH_TAC`, and `CONV_TAC` to simplify and solve the resulting goals.
* Key steps involve finding suitable expressions `a` and `b` that satisfy the required conditions, often by applying the `SQRT_POW_2` theorem or using properties of well-formed expressions and radicals.

### Mathematical insight
The `RADICAL_CANONICAL` theorem provides a way to decompose a well-formed expression `e` into simpler components `a` and `b` involving a radical `r`, under the condition that the set of radicals of `e` is not empty. This decomposition is useful for further simplification and manipulation of expressions involving radicals, and is likely used in more advanced proofs or calculations involving radical expressions.

### Dependencies
* Theorems:
  - `RADICAL_TOP`
  - `MONO_EXISTS`
  - `SQRT_POW_2`
  - `NOT_IN_OWN_RADICALS`
  - `RADICALS_SUBSET`
  - `RADICAL_CANONICAL_TRIVIAL`
* Definitions:
  - `wellformed`
  - `radicals`
  - `value`
  - `Addition`
  - `Multiplication`
  - `Sqrt`
  - `Inverse`
  - `Constant`
  - `Negation`

---

## CUBIC_ROOT_STEP

### Name of formal statement
CUBIC_ROOT_STEP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CUBIC_ROOT_STEP = prove
 (`!a b c. rational a /\ rational b /\ rational c
           ==> !e. wellformed e /\
                   ~(radicals e = {}) /\
                   (value e) pow 3 + a * (value e) pow 2 +
                                     b * (value e) + c = &0
                   ==> ?e'. wellformed e' /\
                            (radicals e') PSUBSET (radicals e) /\
                            (value e') pow 3 + a * (value e') pow 2 +
                                     b * (value e') + c = &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `e:expression` RADICAL_CANONICAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (X_CHOOSE_THEN `r:expression` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`eu:expression`; `ev:expression`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `\x. ?ex. wellformed ex /\
                        radicals ex SUBSET (radicals(e) DELETE r) /\
                        value ex = x`
              STEP_LEMMA_SQRT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN EXISTS_TAC `Constant(&n)` THEN
      REWRITE_TAC[wellformed; radicals; RATIONAL_NUM; value; EMPTY_SUBSET];
      X_GEN_TAC `x:real` THEN
      DISCH_THEN(X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `Negation ex` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value];
      X_GEN_TAC `x:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `Inverse ex` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `ey:expression` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `Addition ex ey` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value; UNION_SUBSET];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `ex:expression` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `ey:expression` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `Multiplication ex ey` THEN
      ASM_REWRITE_TAC[wellformed; radicals; value; UNION_SUBSET]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`a:real`; `b:real`; `c:real`;
    `value e`; `value eu`; `value ev`; `value r`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `Constant a` THEN
      ASM_REWRITE_TAC[wellformed; radicals; EMPTY_SUBSET; value];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `Constant b` THEN
      ASM_REWRITE_TAC[wellformed; radicals; EMPTY_SUBSET; value];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `Constant c` THEN
      ASM_REWRITE_TAC[wellformed; radicals; EMPTY_SUBSET; value];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[wellformed]) THEN
    ASM_REWRITE_TAC[value] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e':expression` THEN
  ASM_SIMP_TAC[] THEN ASM SET_TAC[])
```

### Informal statement
For all real numbers $a$, $b$, and $c$, if $a$, $b$, and $c$ are rational, then for all expressions $e$ that are well-formed, contain at least one radical, and satisfy the cubic equation $(\text{value of } e)^3 + a(\text{value of } e)^2 + b(\text{value of } e) + c = 0$, there exists an expression $e'$ that is well-formed, has radicals that are a subset of the radicals in $e$, and also satisfies the cubic equation $(\text{value of } e')^3 + a(\text{value of } e')^2 + b(\text{value of } e') + c = 0$.

### Informal sketch
* The proof starts by assuming $a$, $b$, and $c$ are rational and $e$ is a well-formed expression with at least one radical that satisfies the given cubic equation.
* It applies `RADICAL_CANONICAL` to $e$ to establish a basis for the subsequent steps, involving the manipulation of expressions and their properties.
* The proof then proceeds by cases, considering different forms that $e$ could take (e.g., constant, negation, inverse, addition, multiplication) and showing that in each case, there exists an $e'$ that meets the required conditions.
* Key steps involve using `STEP_LEMMA_SQRT` to find appropriate expressions $e'$ for different values of $x$, and using `MONO_EXISTS` to establish the existence of $e'$ under certain conditions.
* The proof manipulates expressions using tactics like `ASM_REWRITE_TAC`, `CONJUNCTS_THEN2`, and `MATCH_MP_TAC` to derive the desired properties of $e'$.

### Mathematical insight
This theorem provides a way to find a simplified expression $e'$ that satisfies the same cubic equation as a given expression $e$, under the condition that $a$, $b$, and $c$ are rational. The theorem is important because it helps in solving cubic equations by potentially reducing the complexity of the expression involved, which could be crucial in various algebraic and analytical applications.

### Dependencies
* Theorems:
  + `RADICAL_CANONICAL`
  + `STEP_LEMMA_SQRT`
  + `MONO_EXISTS`
* Definitions:
  + `wellformed`
  + `radicals`
  + `value`
  + `RATIONAL_NUM`
  + `Constant`
  + `Negation`
  + `Inverse`
  + `Addition`
  + `Multiplication`
* Other dependencies may include various properties of real numbers, expressions, and radicals, such as `EMPTY_SUBSET`, `UNION_SUBSET`, and `LEFT_IMP_EXISTS_THM`.

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of expressions, radicals, and the cubic equation. The `RADICAL_CANONICAL` and `STEP_LEMMA_SQRT` theorems, as well as the `MONO_EXISTS` rule, might require careful translation to ensure that the proof structure and the mathematical content are preserved. Additionally, the representation of expressions and their manipulation might differ between proof assistants, requiring adjustments to the tactics used in the proof.

---

## CUBIC_ROOT_RADICAL_INDUCT

### Name of formal statement
CUBIC_ROOT_RADICAL_INDUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CUBIC_ROOT_RADICAL_INDUCT = prove
 (`!a b c. rational a /\ rational b /\ rational c
           ==> !n e. wellformed e /\ CARD (radicals e) = n /\
                     (value e) pow 3 + a * (value e) pow 2 +
                                b * (value e) + c = &0
                 ==> ?x. rational x /\
                         x pow 3 + a * x pow 2 + b * x + c = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `e:expression` THEN
  STRIP_TAC THEN ASM_CASES_TAC `radicals e = {}` THENL
   [ASM_MESON_TAC[RADICALS_EMPTY_RATIONAL]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:expression`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':expression` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(radicals e')`) THEN ANTS_TAC THENL
   [REWRITE_TAC[SYM(ASSUME `CARD(radicals e) = n`)] THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[FINITE_RADICALS];
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `e':expression` THEN
    ASM_REWRITE_TAC[]])
```

### Informal statement
For all rational numbers `a`, `b`, and `c`, if there exists a well-formed expression `e` with `n` radicals such that the value of `e` satisfies the cubic equation `(value e)^3 + a * (value e)^2 + b * (value e) + c = 0`, then there exists a rational number `x` that also satisfies the cubic equation `x^3 + a * x^2 + b * x + c = 0`.

### Informal sketch
* The proof starts by assuming `a`, `b`, and `c` are rational.
* It then proceeds by induction on the number of radicals `n` in a well-formed expression `e` that satisfies the given cubic equation.
* The base case is when `e` has no radicals (`radicals e = {}`), in which case `e` is rational, and the result follows from `RADICALS_EMPTY_RATIONAL`.
* For the inductive step, it uses `CUBIC_ROOT_STEP` to find an expression `e'` with fewer radicals that also satisfies the cubic equation.
* The proof then applies mathematical induction on the number of radicals, using `CARD_PSUBSET` and `FINITE_RADICALS` to establish the inductive hypothesis.
* The `MATCH_MP_TAC` and `EXISTS_TAC` tactics are used to apply the inductive hypothesis and construct the required rational solution `x`.

### Mathematical insight
This theorem provides a way to find rational roots of cubic equations with rational coefficients, by inducting on the number of radicals in an expression that satisfies the equation. The key idea is to reduce the problem to a simpler case with fewer radicals, and then use the inductive hypothesis to construct a rational solution.

### Dependencies
* `CUBIC_ROOT_STEP`
* `RADICALS_EMPTY_RATIONAL`
* `num_WF`
* `CARD_PSUBSET`
* `FINITE_RADICALS`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to preserve the inductive structure of the proof, as well as the use of `MATCH_MP_TAC` and `EXISTS_TAC` to apply the inductive hypothesis and construct the rational solution. Additionally, the `CARD_PSUBSET` and `FINITE_RADICALS` theorems may need to be re-proved or re-imported in the target system.

---

## CUBIC_ROOT_RATIONAL

### Name of formal statement
CUBIC_ROOT_RATIONAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CUBIC_ROOT_RATIONAL = prove
 (`!a b c. rational a /\ rational b /\ rational c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. rational x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REWRITE_TAC[RADICAL_EXPRESSION] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RADICAL_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`CARD(radicals e)`; `e:expression`] THEN
  ASM_MESON_TAC[])
```

### Informal statement
For all real numbers `a`, `b`, and `c`, if `a`, `b`, and `c` are rational and there exists a radical number `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero, then there exists a rational number `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero.

### Informal sketch
* The proof starts by assuming that `a`, `b`, and `c` are rational and that there exists a radical number `x` satisfying the given cubic equation.
* The `REWRITE_TAC` tactic is applied with the `RADICAL_EXPRESSION` rule to rewrite the radical expression.
* The `REPEAT STRIP_TAC` tactic is used to strip away the quantifiers and implications.
* The `MP_TAC` tactic is applied with the `CUBIC_ROOT_RADICAL_INDUCT` theorem, which is specialized for `a`, `b`, and `c`.
* The `ASM_REWRITE_TAC` tactic is used to rewrite the assumptions.
* The `DISCH_THEN` and `MATCH_MP_TAC` tactics are applied to discharge the assumption and match the conclusion with the premise.
* The `MAP_EVERY` and `EXISTS_TAC` tactics are used to introduce the `CARD` and `radicals` expressions.
* The `ASM_MESON_TAC` tactic is applied to conclude the proof.

### Mathematical insight
This theorem provides a condition for the existence of a rational root of a cubic equation with rational coefficients, given the existence of a radical root. The key idea is to use the properties of radical numbers and the `CUBIC_ROOT_RADICAL_INDUCT` theorem to establish the existence of a rational root.

### Dependencies
* Theorems:
	+ `CUBIC_ROOT_RADICAL_INDUCT`
* Definitions:
	+ `RADICAL_EXPRESSION`
	+ `rational`
	+ `radical`
* Inductive rules: None

### Porting notes
When porting this theorem to another proof assistant, note that the `REWRITE_TAC` and `ASM_REWRITE_TAC` tactics may need to be replaced with equivalent rewriting mechanisms. Additionally, the `MP_TAC` and `MATCH_MP_TAC` tactics may need to be replaced with equivalent mechanisms for applying theorems and matching conclusions with premises. The `MAP_EVERY` and `EXISTS_TAC` tactics may also need to be replaced with equivalent mechanisms for introducing existential quantifiers.

---

## CUBIC_ROOT_INTEGER

### Name of formal statement
CUBIC_ROOT_INTEGER

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CUBIC_ROOT_INTEGER = prove
 (`!a b c. integer a /\ integer b /\ integer c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. integer x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RATIONAL) THEN
  ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
  ASM_MESON_TAC[RATIONAL_ROOT_INTEGER])
```

### Informal statement
For all integers `a`, `b`, and `c`, if there exists a radical `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero, then there exists an integer `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero.

### Informal sketch
* The theorem `CUBIC_ROOT_INTEGER` starts by assuming the existence of a radical root for a given cubic polynomial with integer coefficients.
* It then invokes `CUBIC_ROOT_RATIONAL` to establish the existence of a rational root.
* Using `RATIONAL_INTEGER`, it simplifies the rational root to an integer root.
* Finally, it applies `RATIONAL_ROOT_INTEGER` to conclude the existence of an integer root.
* Key steps involve recognizing the polynomial is monic and leveraging properties of radicals and integers.

### Mathematical insight
This theorem is important because it establishes a connection between the existence of radical roots and integer roots for cubic polynomials with integer coefficients. It provides a foundation for further analysis of polynomial roots, leveraging the fact that the polynomial is monic to narrow down the possible roots to integers.

### Dependencies
* Theorems:
	+ `CUBIC_ROOT_RATIONAL`
	+ `RATIONAL_INTEGER`
	+ `RATIONAL_ROOT_INTEGER`
* Definitions:
	+ `integer`
	+ `radical`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of radicals, integers, and rational numbers. Ensure that the target system has equivalent definitions and theorems for these concepts, such as `CUBIC_ROOT_RATIONAL` and `RATIONAL_ROOT_INTEGER`. Additionally, be mindful of the differences in tactic languages and automation capabilities between HOL Light and the target system.

---

## length

### Name of formal statement
length

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let length = new_definition
  `length(a:real^2,b:real^2) = norm(b - a)`
```

### Informal statement
The function `length` is defined as a mapping from two points `a` and `b` in 2-dimensional real space to the real number that represents the Euclidean distance between `a` and `b`, calculated as the norm (or magnitude) of the vector difference `b - a`.

### Informal sketch
* The definition of `length` relies on the concept of vector subtraction and the norm (magnitude) of a vector in 2-dimensional real space.
* It utilizes the `norm` function to compute the distance between two points `a` and `b`.
* The definition does not involve a complex proof structure, as it is a straightforward definition of a geometric concept.

### Mathematical insight
The `length` function represents a fundamental geometric concept: the distance between two points in a 2-dimensional space. This definition is crucial in various geometric and analytical contexts, as it provides a way to quantify the separation between points, which is essential for numerous applications in mathematics, physics, and engineering.

### Dependencies
* `norm`
* `real^2` (type of 2-dimensional real vectors)

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the target system supports a similar concept of 2-dimensional real vectors and a norm function. The definition itself is straightforward, but the specifics of how vectors and their operations are handled may vary between systems. Pay particular attention to how vector subtraction and norm calculation are defined and implemented in the target system.

---

## parallel

### Name of formal statement
parallel

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let parallel = new_definition
 `parallel (a:real^2,b:real^2) (c:real^2,d:real^2) <=>
        (a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)`
```

### Informal statement
The `parallel` relation between two pairs of points in 2D real space, `(a, b)` and `(c, d)`, holds if and only if the product of the differences in the x-coordinates of `(a, b)` and the y-coordinates of `(c, d)` is equal to the product of the differences in the y-coordinates of `(a, b)` and the x-coordinates of `(c, d)`. In other words, for points `a = (a$1, a$2)`, `b = (b$1, b$2)`, `c = (c$1, c$2)`, and `d = (d$1, d$2)`, `parallel (a, b) (c, d)` if and only if `(a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)`.

### Informal sketch
* The definition involves comparing the slopes of the lines formed by points `(a, b)` and `(c, d)`.
* To show that two lines are parallel, one must demonstrate that their slopes are equal.
* The given condition `(a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)` essentially checks for this equality of slopes by cross-multiplying, which is a characteristic property of parallel lines in the Cartesian plane.
* This definition does not directly compute slopes but uses the cross-product relationship to establish parallelism, avoiding division by zero issues.

### Mathematical insight
The `parallel` definition captures the geometric concept of parallel lines in a 2D real space. It is essential in geometry and various mathematical proofs involving lines and planes. This definition is meaningful because it provides a way to determine if two line segments are parallel without explicitly calculating their slopes, which can be problematic if the lines are vertical (i.e., have undefined slope).

### Dependencies
* `real^2` type definition
* Basic arithmetic operations (`+`, `-`, `*`)

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, pay attention to how these systems handle 2D vectors or points and ensure that the arithmetic operations are correctly interpreted. Additionally, consider how the target system represents real numbers and whether it has built-in support for geometric concepts like parallel lines.

---

## collinear3

### Name of formal statement
collinear3

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let collinear3 = new_definition
  `collinear3 (a:real^2) b c <=> parallel (a,b) (a,c)`;;
```

### Informal statement
The `collinear3` relation holds among three points `a`, `b`, and `c` in 2-dimensional real space if and only if the line segments from `a` to `b` and from `a` to `c` are parallel.

### Informal sketch
* The definition of `collinear3` relies on the concept of `parallel` line segments.
* To establish `collinear3 (a, b, c)`, one must show that the line segments `(a, b)` and `(a, c)` are `parallel`.
* The `parallel` relation is likely defined elsewhere and is a prerequisite for understanding the `collinear3` definition.

### Mathematical insight
The `collinear3` definition captures the geometric concept of three points being collinear (i.e., lying on the same line) by leveraging the property of parallel line segments. This definition is important in geometric and spatial reasoning, as it provides a way to express and prove statements about the collinearity of points.

### Dependencies
* `parallel`

### Porting notes
When porting this definition to another proof assistant, ensure that the `parallel` relation is defined and available. The porting process may require adapting the type annotations (e.g., `real^2`) to match the target system's representation of 2-dimensional real space. Additionally, consider the potential need to redefine or reprove any underlying geometric concepts, such as the `parallel` relation, in the target system.

---

## is_intersection

### Name of formal statement
is_intersection

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_intersection = new_definition
  `is_intersection p (a,b) (c,d) <=> collinear3 a p b /\ collinear3 c p d`;;
```

### Informal statement
The `is_intersection` relation holds for a point `p` and two line segments `(a, b)` and `(c, d)` if and only if `p` is collinear with both `a` and `b`, and `p` is collinear with both `c` and `d`.

### Informal sketch
* The definition of `is_intersection` involves checking two conditions:
 + `collinear3 a p b` holds, meaning `p` is on the line through `a` and `b`
 + `collinear3 c p d` holds, meaning `p` is on the line through `c` and `d`
* The conjunction of these conditions ensures that `p` is a point where the lines through `(a, b)` and `(c, d)` intersect

### Mathematical insight
The `is_intersection` definition formalizes the geometric concept of two line segments intersecting at a point. It's essential in geometric and topological reasoning, allowing the expression of properties and theorems about intersecting lines and points.

### Dependencies
* `collinear3`

### Porting notes
When translating this definition to other proof assistants, ensure that the collinearity predicate is correctly defined and used. Note that different systems may handle geometric or spatial reasoning differently, potentially affecting how `collinear3` is defined or used.

---

## on_circle

### Name of formal statement
on_circle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let on_circle = new_definition `on_circle x (centre,pt) <=> length(centre,x) = length(centre,pt)`;;
```

### Informal statement
The `on_circle` predicate holds for a point `x` and a pair `(centre, pt)` if and only if the distance from `centre` to `x` is equal to the distance from `centre` to `pt`.

### Informal sketch
* The definition introduces a binary relation `on_circle` between a point `x` and a pair `(centre, pt)`.
* The relation is defined in terms of the `length` function, which presumably measures the distance between two points.
* To prove that a point `x` is `on_circle` with respect to `(centre, pt)`, one would need to show that the distances from `centre` to `x` and from `centre` to `pt` are equal.

### Mathematical insight
The `on_circle` definition captures the geometric concept of a point lying on a circle, where the circle is implicitly defined by its center `centre` and a point `pt` on its circumference. This definition is likely used to establish properties of circles and their relationships to points in a geometric or analytic context.

### Dependencies
* `length`
 
### Porting notes
When translating this definition into another proof assistant, ensure that the `length` function is properly defined and that the equality of distances is correctly expressed. Note that different systems may handle distance or metric functions differently, so care should be taken to ensure compatibility.

---

## SQRT_CASES_LEMMA

### Name of formal statement
SQRT_CASES_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SQRT_CASES_LEMMA = prove
 (`!x y. y pow 2 = x ==> &0 <= x /\ (sqrt(x) = y \/ sqrt(x) = --y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
  MP_TAC(SPEC `y:real` (GEN_ALL POW_2_SQRT)) THEN
  MP_TAC(SPEC `--y` (GEN_ALL POW_2_SQRT)) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC)
```

### Informal statement
For all real numbers $x$ and $y$, if $y$ squared equals $x$, then $x$ is non-negative and the square root of $x$ is either $y$ or $-y$.

### Informal sketch
* Start with the assumption $y^2 = x$.
* Use `REAL_POW_2` and `REAL_LE_SQUARE` to establish that $x$ is non-negative.
* Apply `POW_2_SQRT` to both $y$ and $-y$ to relate $x$ with its square roots.
* Combine the results to conclude that $\sqrt{x} = y$ or $\sqrt{x} = -y$.

### Mathematical insight
This lemma provides a fundamental property of square roots, establishing a direct relationship between a number and its square roots. It is crucial for various mathematical developments involving real numbers and square root functions.

### Dependencies
* Theorems:
  + `POW_2_SQRT`
* Definitions:
  + `REAL_POW_2`
  + `REAL_LE_SQUARE`
  + `REAL_POW_NEG`
  + `REAL_ARITH`

### Porting notes
When translating this lemma into other proof assistants, pay attention to the handling of real numbers, square root functions, and the specific `REAL_POW_2` and `POW_2_SQRT` theorems, as their equivalents may have different names or require additional imports. Additionally, the `REAL_ARITH_TAC` tactic may need to be replaced with a similar arithmetic reasoning mechanism in the target proof assistant.

---

## RADICAL_LINEAR_EQUATION

### Name of formal statement
RADICAL_LINEAR_EQUATION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_LINEAR_EQUATION = prove
 (`!a b x. radical a /\ radical b /\ ~(a = &0 /\ b = &0) /\ a * x + b = &0
           ==> radical x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a = &0) /\ x = --b / a`
   (fun th -> ASM_SIMP_TAC[th; RADICAL_RULES]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD)
```

### Informal statement
For all `a`, `b`, and `x`, if `a` is radical, `b` is radical, and it is not the case that both `a` equals 0 and `b` equals 0, and the equation `a * x + b = 0` holds, then `x` is radical.

### Informal sketch
* Start by assuming the premises: `a` is radical, `b` is radical, and not both `a` and `b` are 0.
* Use these assumptions to derive that `a` is not 0, which allows us to solve the equation `a * x + b = 0` for `x`, yielding `x = -b / a`.
* Apply `RADICAL_RULES` to simplify and establish that `x` is radical, given that `a` and `b` are radical and `a` is not 0.
* The proof involves applying `STRIP_TAC` to strip away the universal quantifiers, and `ASM_SIMP_TAC` with `RADICAL_RULES` to simplify the expression and derive the conclusion that `x` is radical.

### Mathematical insight
This theorem shows that the solution to a linear equation of the form `a * x + b = 0`, where `a` and `b` are radical numbers and `a` is not 0, is itself a radical number. This is an important result because it helps establish the closure of radical numbers under certain algebraic operations, which is crucial in various areas of mathematics, such as algebra and number theory.

### Dependencies
* `radical`
* `RADICAL_RULES`
* `REAL_FIELD`

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to the handling of radical numbers and the `RADICAL_RULES` used in the proof. The porting process may require defining or importing similar rules and ensuring that the target system can handle the algebraic manipulations involved. Additionally, the treatment of division and the handling of the case where `a` is not 0 may vary between systems, requiring careful consideration to ensure a correct and efficient port.

---

## RADICAL_SIMULTANEOUS_LINEAR_EQUATION

### Name of formal statement
RADICAL_SIMULTANEOUS_LINEAR_EQUATION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_SIMULTANEOUS_LINEAR_EQUATION = prove
 (`!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(a * e = b * d /\ a * f = c * d /\ e * c = b * f) /\
        a * x + b * y = c /\ d * x + e * y = f
        ==> radical(x) /\ radical(y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN
   `~(a * e - b * d = &0) /\
    x = (e * c - b * f) / (a * e - b * d) /\
    y = (a * f - d * c) / (a * e - b * d)`
  STRIP_ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[RADICAL_RULES]])
```

### Informal statement
For all `a`, `b`, `c`, `d`, `e`, `f`, and `x`, if `a`, `b`, `c`, `d`, `e`, and `f` are radical, and it is not the case that `a * e = b * d` and `a * f = c * d` and `e * c = b * f`, and `a * x + b * y = c` and `d * x + e * y = f`, then `x` and `y` are radical.

### Informal sketch
* The proof starts by assuming the premises: `a`, `b`, `c`, `d`, `e`, and `f` are radical, and the system of linear equations `a * x + b * y = c` and `d * x + e * y = f` holds.
* It then assumes that the determinant of the system, `a * e - b * d`, is not zero, which implies that the system has a unique solution.
* The solution for `x` and `y` is then expressed as `x = (e * c - b * f) / (a * e - b * d)` and `y = (a * f - d * c) / (a * e - b * d)`.
* The proof then applies `RADICAL_RULES` to show that `x` and `y` are radical.

### Mathematical insight
This theorem provides a condition under which the solutions to a system of linear equations with radical coefficients are also radical. The condition is that the coefficients do not satisfy a certain degenerate case, which would make the system singular. This result is useful in algebraic manipulations involving radical numbers.

### Dependencies
* `RADICAL_RULES`
* Basic properties of linear equations and radical numbers

### Porting notes
When translating this theorem into other proof assistants, care should be taken to ensure that the handling of radical numbers and linear equations is consistent with the original HOL Light formulation. In particular, the `RADICAL_RULES` may need to be reimplemented or replaced with equivalent rules in the target system. Additionally, the use of `REPEAT GEN_TAC` and `STRIP_TAC` may need to be adapted to the tactical structure of the target system.

---

## RADICAL_QUADRATIC_EQUATION

### Name of formal statement
RADICAL_QUADRATIC_EQUATION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_QUADRATIC_EQUATION = prove
 (`!a b c x. radical a /\ radical b /\ radical c /\
             a * x pow 2 + b * x + c = &0 /\
             ~(a = &0 /\ b = &0 /\ c = &0)
             ==> radical x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
    MESON_TAC[RADICAL_LINEAR_EQUATION];
    ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC RADICAL_LINEAR_EQUATION THEN
  EXISTS_TAC `&2 * a` THEN
  ASM_SIMP_TAC[RADICAL_RULES; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  SUBGOAL_THEN `&0 <= b pow 2 - &4 * a * c /\
                ((&2 * a) * x + (b - sqrt(b pow 2 - &4 * a * c)) = &0 \/
                 (&2 * a) * x + (b + sqrt(b pow 2 - &4 * a * c)) = &0)`
  MP_TAC THENL
   [REWRITE_TAC[real_sub; REAL_ARITH `a + (b + c) = &0 <=> c = --(a + b)`] THEN
    REWRITE_TAC[REAL_EQ_NEG2] THEN MATCH_MP_TAC SQRT_CASES_LEMMA THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN CONV_TAC REAL_RING;
    STRIP_TAC THENL
     [EXISTS_TAC `b - sqrt(b pow 2 - &4 * a * c)`;
      EXISTS_TAC `b + sqrt(b pow 2 - &4 * a * c)`] THEN
    ASM_REWRITE_TAC[] THEN RADICAL_TAC THEN ASM_REWRITE_TAC[])
```

### Informal statement
For all `a`, `b`, `c`, and `x`, if `a`, `b`, and `c` are radical and `a * x^2 + b * x + c = 0` and not (`a = 0` and `b = 0` and `c = 0`), then `x` is radical.

### Informal sketch
* The proof starts by considering the case when `a = 0`. 
* If `a = 0`, it simplifies the equation to `b * x + c = 0` and applies the `RADICAL_LINEAR_EQUATION` theorem.
* If `a` is not `0`, it uses the `MATCH_MP_TAC` tactic with `RADICAL_LINEAR_EQUATION` to find a value that satisfies the equation.
* It then uses the `SUBGOAL_THEN` tactic to prove two subgoals: 
  + `0 <= b^2 - 4 * a * c`
  + `(&2 * a) * x + (b - sqrt(b^2 - 4 * a * c)) = 0` or `(&2 * a) * x + (b + sqrt(b^2 - 4 * a * c)) = 0`
* The proof uses various tactics such as `REWRITE_TAC`, `MATCH_MP_TAC`, `EXISTS_TAC`, and `RADICAL_TAC` to simplify and prove the subgoals.

### Mathematical insight
This theorem is important because it provides a condition under which the roots of a quadratic equation are radical. The quadratic formula is a fundamental concept in algebra, and this theorem helps to identify when the roots of the equation can be expressed using radicals.

### Dependencies
* Theorems:
  + `RADICAL_LINEAR_EQUATION`
  + `SQRT_CASES_LEMMA`
* Definitions:
  + `radical`
  + `real_sub`
  + `REAL_MUL_LZERO`
  + `REAL_ADD_LID`
  + `REAL_ENTIRE`
  + `REAL_OF_NUM_EQ`
  + `ARITH_EQ`
  + `REAL_ARITH`
  + `REAL_EQ_NEG2`
* Inductive rules: None

### Porting notes
When porting this theorem to other proof assistants, note that the `RADICAL_LINEAR_EQUATION` theorem and the `SQRT_CASES_LEMMA` may need to be ported first. Additionally, the `MATCH_MP_TAC` and `SUBGOAL_THEN` tactics may need to be replaced with equivalent tactics in the target proof assistant. The `REWRITE_TAC` and `EXISTS_TAC` tactics may also need to be modified to match the specific syntax and semantics of the target system.

---

## RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC

### Name of formal statement
RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC = prove
 (`!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(d = &0 /\ e = &0 /\ f = &0) /\
        (x - a) pow 2 + (y - b) pow 2 = c /\ d * x + e * y = f
        ==> radical x /\ radical y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d pow 2 + e pow 2` RADICAL_QUADRATIC_EQUATION) THEN
  DISCH_THEN MATCH_MP_TAC THENL
   [EXISTS_TAC `&2 * b * d * e - &2 * a * e pow 2 - &2 * d * f` THEN
    EXISTS_TAC `b pow 2 * e pow 2 + a pow 2 * e pow 2 +
                f pow 2 - c * e pow 2 - &2 * b * e * f`;
    EXISTS_TAC `&2 * a * d * e - &2 * b * d pow 2 - &2 * f * e` THEN
    EXISTS_TAC `a pow 2 * d pow 2 + b pow 2 * d pow 2 +
                f pow 2 - c * d pow 2 - &2 * a * d * f`] THEN
  (REPLICATE_TAC 3
    (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
   CONJ_TAC THENL
    [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   REWRITE_TAC[REAL_SOS_EQ_0] THEN REPEAT(POP_ASSUM MP_TAC) THEN
   CONV_TAC REAL_RING))
```

### Informal statement
For all real numbers $a$, $b$, $c$, $d$, $e$, $f$, and $x$, if $a$, $b$, $c$, $d$, $e$, and $f$ are radical (i.e., their square roots are real), and not all of $d$, $e$, and $f$ are zero, and the equations $(x - a)^2 + (y - b)^2 = c$ and $dx + ey = f$ hold, then both $x$ and $y$ are radical.

### Informal sketch
The proof involves several main stages:
* It starts by assuming the premises about $a$, $b$, $c$, $d$, $e$, $f$, and the two given equations.
* It uses the `RADICAL_QUADRATIC_EQUATION` theorem, specifying `d pow 2 + e pow 2` to establish a relationship between $x$, $y$, and the other variables.
* It then proceeds with a case analysis, using `EXISTS_TAC` to introduce specific expressions involving $a$, $b$, $d$, $e$, and $f$, aiming to show that $x$ and $y$ are radical in each case.
* The proof involves applying `RADICAL_TAC` and `ASM_REWRITE_TAC` to simplify and establish the radical nature of $x$ and $y$.
* It concludes by using `CONJ_TAC`, `REPEAT`, `POP_ASSUM`, `MP_TAC`, `CONV_TAC REAL_RING`, and `REWRITE_TAC` with `REAL_SOS_EQ_0` to finalize the proof that both $x$ and $y$ are radical.

### Mathematical insight
This theorem is important because it establishes a condition under which the solutions to a system of equations involving a circle and a line are radical, meaning their square roots are real. This has implications in geometry and algebra, particularly in problems involving the intersection of curves and lines in the real plane.

### Dependencies
* Theorems:
  + `RADICAL_QUADRATIC_EQUATION`
* Definitions:
  + `radical`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles real numbers, radical expressions, and the specific tactics used (e.g., `RADICAL_TAC`, `ASM_REWRITE_TAC`, `CONV_TAC REAL_RING`). Differences in how these systems manage real arithmetic and radical expressions may require adjustments to the proof strategy. Additionally, the use of `EXISTS_TAC` and case analysis may need to be adapted based on the target system's support for existential introduction and case splitting.

---

## RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC

### Name of formal statement
RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC = prove
 (`!a b c d e f x.
        radical a /\ radical b /\ radical c /\
        radical d /\ radical e /\ radical f /\
        ~(a = d /\ b = e /\ c = f) /\
        (x - a) pow 2 + (y - b) pow 2 = c /\
        (x - d) pow 2 + (y - e) pow 2 = f
        ==> radical x /\ radical y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC THEN
  MAP_EVERY EXISTS_TAC
   [`a:real`; `b:real`; `c:real`; `&2 * (d - a)`; `&2 * (e - b)`;
    `(d pow 2 - a pow 2) + (e pow 2 - b pow 2) + (c - f)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPLICATE_TAC 3
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING)
```

### Informal statement
For all real numbers $a$, $b$, $c$, $d$, $e$, $f$, and $x$, if $a$, $b$, $c$, $d$, $e$, and $f$ are radical, and $a$, $b$, $c$ are not equal to $d$, $e$, $f$ respectively, and the equations $(x - a)^2 + (y - b)^2 = c$ and $(x - d)^2 + (y - e)^2 = f$ hold, then $x$ and $y$ are radical.

### Informal sketch
* The proof starts by assuming the premises: $a$, $b$, $c$, $d$, $e$, $f$ are radical, and the two given equations hold.
* It then applies the `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC` theorem, which requires finding suitable values to satisfy its conditions.
* The existence of these values is established by providing explicit terms: `a`, `b`, `c`, `&2 * (d - a)`, `&2 * (e - b)`, and `(d pow 2 - a pow 2) + (e pow 2 - b pow 2) + (c - f)`.
* The proof then proceeds with a series of rewriting and simplification steps, using `ASM_REWRITE_TAC` and `CONJ_TAC`, to establish the radical nature of $x$ and $y$.
* The use of `RADICAL_TAC` and `REAL_RING` suggests that the proof involves both radical and real number properties.

### Mathematical insight
This theorem is important because it provides a condition under which the solutions to two quadratic equations are radical, which has implications in algebra and geometry, particularly in the study of conic sections and their intersections.

### Dependencies
* Theorems:
  * `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`
* Definitions:
  * `radical`

### Porting notes
When translating this theorem into other proof assistants, pay special attention to how radical numbers and real numbers are handled, as well as the automation tactics like `ASM_REWRITE_TAC` and `REAL_RING`, which might have counterparts or require manual implementation in the target system.

---

## constructible_RULES,constructible_INDUCT,constructible_CASES

### Name of formal statement
constructible_RULES,constructible_INDUCT,constructible_CASES

### Type of the formal statement
new_inductive_definition

### Formal Content
```ocaml
let constructible_RULES,constructible_INDUCT,constructible_CASES =
 new_inductive_definition
  `(!x:real^2. rational(x$1) /\ rational(x$2) ==> constructible x) /\
// Intersection of two non-parallel lines AB and CD
  (!a b c d x. constructible a /\ constructible b /\
               constructible c /\ constructible d /\
               ~parallel (a,b) (c,d) /\ is_intersection x (a,b) (c,d)
               ==> constructible x) /\
// Intersection of a nontrivial line AB and circle with centre C, radius DE
  (!a b c d e x. constructible a /\ constructible b /\
                 constructible c /\ constructible d /\
                 constructible e /\
                 ~(a = b) /\ collinear3 a x b /\ length (c,x) = length(d,e)
                 ==> constructible x) /\
// Intersection of distinct circles with centres A and D, radii BD and EF
  (!a b c d e f x. constructible a /\ constructible b /\
                   constructible c /\ constructible d /\
                   constructible e /\ constructible f /\
                   ~(a = d /\ length (b,c) = length (e,f)) /\
                   length (a,x) = length (b,c) /\ length (d,x) = length (e,f)
                   ==> constructible x)`
```

### Informal statement
For all points `x` in the real plane, if both coordinates of `x` are rational, then `x` is constructible. Furthermore, the following conditions also imply constructibility: 
- The intersection `x` of two non-parallel lines `AB` and `CD`, where `A`, `B`, `C`, and `D` are constructible points.
- The intersection `x` of a non-trivial line `AB` (where `A` and `B` are distinct) and a circle centered at `C` with radius `DE`, where `A`, `B`, `C`, `D`, and `E` are constructible points, and `x` lies on line `AB`.
- The intersection `x` of two distinct circles, one centered at `A` with radius `BC` and the other centered at `D` with radius `EF`, where `A`, `B`, `C`, `D`, `E`, and `F` are constructible points, and the circles are not identical.

### Informal sketch
* The proof involves defining an inductive predicate `constructible` that applies to points in the real plane.
* The base case asserts that points with rational coordinates are constructible.
* The inductive steps cover three main geometric constructions:
  + Intersection of two non-parallel lines: If lines `AB` and `CD` are not parallel and `A`, `B`, `C`, `D` are constructible, then their intersection `x` is constructible.
  + Intersection of a line and a circle: If `A`, `B`, `C`, `D`, `E` are constructible, line `AB` is non-trivial, and `x` is the intersection of line `AB` and the circle centered at `C` with radius `DE`, then `x` is constructible.
  + Intersection of two circles: If `A`, `B`, `C`, `D`, `E`, `F` are constructible, and `x` is the intersection of the circles centered at `A` and `D` with radii `BC` and `EF` respectively, and these circles are distinct, then `x` is constructible.
* Key HOL Light terms involved include `constructible`, `rational`, `parallel`, `is_intersection`, `collinear3`, and `length`.

### Mathematical insight
This definition formalizes the concept of constructible points in geometry, which are points that can be constructed using a compass and straightedge. The conditions cover basic geometric constructions that can be performed with these tools, providing a foundation for more complex constructions. The definition is essential in geometric and algebraic studies, particularly in the context of constructible numbers and geometric theorems.

### Dependencies
#### Theorems and Definitions
* `rational`
* `constructible`
* `parallel`
* `is_intersection`
* `collinear3`
* `length`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how these systems handle inductive definitions, especially those involving geometric predicates and real numbers. Differences in type systems, particularly how real numbers and geometric objects are represented, may require adjustments to the definition and its proofs. Additionally, the use of `new_inductive_definition` in HOL Light may not have a direct analogue in other systems, so understanding how inductive types are defined in the target system is crucial.

---

## RADICAL_LINE_LINE_INTERSECTION

### Name of formal statement
RADICAL_LINE_LINE_INTERSECTION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_LINE_LINE_INTERSACTION = prove
 (`!a b c d x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        ~(parallel (a,b) (c,d)) /\ is_intersection x (a,b) (c,d)
        ==> radical(x$1) /\ radical(x$2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[parallel; collinear3; is_intersection] THEN STRIP_TAC THEN
  MATCH_MP_TAC RADICAL_SIMULTANEOUS_LINEAR_EQUATION THEN
  MAP_EVERY EXISTS_TAC
   [`(b:real^2)$2 - (a:real^2)$2`; `(a:real^2)$1 - (b:real^2)$1`;
    `(a:real^2)$2 * (a$1 - (b:real^2)$1) - (a:real^2)$1 * (a$2 - b$2)`;
    `(d:real^2)$2 - (c:real^2)$2`; `(c:real^2)$1 - (d:real^2)$1`;
    `(c:real^2)$2 * (c$1 - (d:real^2)$1) - (c:real^2)$1 * (c$2 - d$2)`] THEN
  REPLICATE_TAC 6
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING)
```

### Informal statement
For all points `a`, `b`, `c`, `d`, and `x` in the real plane, if `a$1`, `a$2`, `b$1`, `b$2`, `c$1`, `c$2`, `d$1`, and `d$2` are all radical (i.e., their square roots are defined), and the lines defined by points `a` and `b` and by points `c` and `d` are not parallel, and `x` is the intersection of these two lines, then both coordinates `x$1` and `x$2` of `x` are radical.

### Informal sketch
* Start by assuming the premises: `a`, `b`, `c`, `d` are points with radical coordinates, and the lines through `a`, `b` and `c`, `d` are not parallel.
* Use the definition of `is_intersection` to express `x` as the intersection point of the two lines.
* Apply the `RADICAL_SIMULTANEOUS_LINEAR_EQUATION` theorem to establish that the coordinates of `x` satisfy certain linear equations.
* Instantiate the `EXISTS_TAC` with specific values to provide witnesses for the existential quantifiers in `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`.
* Use `REPLICATE_TAC` to apply `CONJ_TAC` and `RADICAL_TAC` to each coordinate of `x`, proving that both `x$1` and `x$2` are radical.
* Finally, use `REPEAT` and `POP_ASSUM` to rearrange and apply the assumptions, and `CONV_TAC REAL_RING` to simplify the resulting expression.

### Mathematical insight
This theorem provides a condition under which the intersection point of two lines, each defined by two points with radical coordinates, also has radical coordinates. This is useful in geometric and algebraic contexts where radical numbers are of interest, such as in the study of constructible numbers or in certain geometric constructions.

### Dependencies
#### Theorems
* `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`
#### Definitions
* `radical`
* `parallel`
* `collinear3`
* `is_intersection`

---

## RADICAL_LINE_CIRCLE_INTERSECTION

### Name of formal statement
RADICAL_LINE_CIRCLE_INTERSECTION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_LINE_CIRCLE_INTERSECTION = prove
 (`!a b c d e x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        radical(e$1) /\ radical(e$2) /\
        ~(a = b) /\ collinear3 a x b /\ length(c,x) = length(d,e)
        ==> radical(x$1) /\ radical(x$2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[length; NORM_EQ; collinear3; parallel] THEN
  SIMP_TAC[CART_EQ; FORALL_2; dot; SUM_2; DIMINDEX_2; VECTOR_SUB_COMPONENT;
           GSYM REAL_POW_2] THEN
  STRIP_TAC THEN MATCH_MP_TAC RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC THEN
  MAP_EVERY EXISTS_TAC
   [`(c:real^2)$1`; `(c:real^2)$2`;
    `((e:real^2)$1 - (d:real^2)$1) pow 2 + (e$2 - d$2) pow 2`;
    `(b:real^2)$2 - (a:real^2)$2`;
    `(a:real^2)$1 - (b:real^2)$1`;
    `a$2 * ((a:real^2)$1 - (b:real^2)$1) - a$1 * (a$2 - b$2)`] THEN
  REPLICATE_TAC 6
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING)
```

### Informal statement
For all points $a$, $b$, $c$, $d$, $e$, and $x$, if the coordinates of $a$, $b$, $c$, $d$, and $e$ are radical (i.e., their components are radical numbers) and $a$ is not equal to $b$, and $a$, $x$, and $b$ are collinear, and the distance from $c$ to $x$ is equal to the distance from $d$ to $e$, then the coordinates of $x$ are also radical.

### Informal sketch
* The proof starts by assuming the premises: $a$, $b$, $c$, $d$, and $e$ have radical coordinates, $a \neq b$, $a$, $x$, and $b$ are collinear, and the distance from $c$ to $x$ equals the distance from $d$ to $e$.
* It then applies various simplifications and rewrites using `REWRITE_TAC` and `SIMP_TAC` to transform the goal into a more manageable form, utilizing properties like `CART_EQ`, `FORALL_2`, `dot`, `SUM_2`, `DIMINDEX_2`, `VECTOR_SUB_COMPONENT`, and `GSYM REAL_POW_2`.
* The `MATCH_MP_TAC` tactic is used with `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC` to find a suitable instantiation for the proof, involving specific constructions with the points' coordinates.
* The proof proceeds with a series of `EXISTS_TAC` and `CONJ_TAC` to establish the radical nature of $x$'s coordinates, leveraging `RADICAL_TAC` and `ASM_REWRITE_TAC` to finalize the argument.
* The final steps involve simplifying and concluding the proof using `REPEAT`, `POP_ASSUM`, `MP_TAC`, and `CONV_TAC` with `REAL_RING`.

### Mathematical insight
This theorem is crucial for geometric constructions involving radical points and lines, ensuring that under specific conditions, the intersection point of a line and a circle (defined by radical points) will also have radical coordinates. This is significant in geometric and algebraic contexts where radical numbers play a central role, such as in the study of constructible numbers and geometric constructions.

### Dependencies
#### Theorems
* `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`
#### Definitions
* `radical`
* `collinear3`
* `length`
* `CART_EQ`
* `FORALL_2`
* `dot`
* `SUM_2`
* `DIMINDEX_2`
* `VECTOR_SUB_COMPONENT`
* `GSYM REAL_POW_2`

---

## RADICAL_CIRCLE_CIRCLE_INTERSECTION

### Name of formal statement
RADICAL_CIRCLE_CIRCLE_INTERSECTION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RADICAL_CIRCLE_CIRCLE_INTERSECTION = prove
 (`!a b c d e f x.
        radical(a$1) /\ radical(a$2) /\
        radical(b$1) /\ radical(b$2) /\
        radical(c$1) /\ radical(c$2) /\
        radical(d$1) /\ radical(d$2) /\
        radical(e$1) /\ radical(e$2) /\
        radical(f$1) /\ radical(f$2) /\
        length(a,x) = length(b,c) /\
        length(d,x) = length(e,f) /\
        ~(a = d /\ length(b,c) = length(e,f))
        ==> radical(x$1) /\ radical(x$2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[length; NORM_EQ; collinear3; parallel] THEN
  SIMP_TAC[CART_EQ; FORALL_2; dot; SUM_2; DIMINDEX_2; VECTOR_SUB_COMPONENT;
           GSYM REAL_POW_2] THEN
  STRIP_TAC THEN MATCH_MP_TAC RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC THEN
  MAP_EVERY EXISTS_TAC
   [`(a:real^2)$1`; `(a:real^2)$2`;
    `((c:real^2)$1 - (b:real^2)$1) pow 2 + (c$2 - b$2) pow 2`;
    `(d:real^2)$1`; `(d:real^2)$2`;
    `((f:real^2)$1 - (e:real^2)$1) pow 2 + (f$2 - e$2) pow 2`] THEN
  REPLICATE_TAC 6
   (CONJ_TAC THENL [RADICAL_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING)
```

### Informal statement
For all points `a`, `b`, `c`, `d`, `e`, `f`, and `x` in a 2D space, if `a`, `b`, `c`, `d`, `e`, and `f` have radical (i.e., irrational) coordinates, and the distances from `a` to `x` and from `b` to `c` are equal, and the distances from `d` to `x` and from `e` to `f` are equal, and it is not the case that `a` equals `d` and the distance from `b` to `c` equals the distance from `e` to `f`, then `x` has radical coordinates.

### Informal sketch
* The proof starts with the assumption of the premises: the radical nature of points `a`, `b`, `c`, `d`, `e`, `f`, and the equalities of distances involving `x`.
* It then applies various `REWRITE_TAC` and `SIMP_TAC` steps to manipulate the expressions and simplify the goal, utilizing theorems such as `length`, `NORM_EQ`, `collinear3`, `parallel`, `CART_EQ`, `FORALL_2`, `dot`, `SUM_2`, `DIMINDEX_2`, `VECTOR_SUB_COMPONENT`, and `GSYM REAL_POW_2`.
* The proof proceeds with `STRIP_TAC` to remove any universal quantifiers and then applies `MATCH_MP_TAC` with `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC` to establish the radical nature of `x`'s coordinates.
* It uses `MAP_EVERY EXISTS_TAC` to provide witnesses for the existential quantifiers, specifically the coordinates of `a`, `d`, and the squared distances between points `b`, `c` and `e`, `f`.
* The proof concludes with `REPLICATE_TAC` to handle the conjunctions, applying `RADICAL_TAC` and `ASM_REWRITE_TAC` to finalize the radical nature of `x`'s coordinates, and `CONV_TAC REAL_RING` to ensure the result is in the real number ring.

### Mathematical insight
This theorem is important because it establishes a property about the intersection points of circles defined by radical (irrational) points in a 2D space. The radical nature of these points implies that their coordinates are not rational numbers, which has implications for the geometric constructions and the algebraic representation of these points. The theorem provides a condition under which the intersection point `x` of two such circles also has radical coordinates, given certain equalities of distances between these points. This has implications for geometric constructions and algebraic geometry, particularly in contexts where rational or irrational coordinates have distinct properties or implications.

### Dependencies
#### Theorems
* `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`
#### Definitions
* `radical`
* `length`
* `CART_EQ`
* `FORALL_2`
* `dot`
* `SUM_2`
* `DIMINDEX_2`
* `VECTOR_SUB_COMPONENT`
* `GSYM REAL_POW_2`

---

## CONSTRUCTIBLE_RADICAL

### Name of formal statement
CONSTRUCTIBLE_RADICAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CONSTRUCTIBLE_RADICAL = prove
 (`!x. constructible x ==> radical(x$1) /\ radical(x$2)`,
  MATCH_MP_TAC constructible_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[RADICAL_RULES];
    MATCH_MP_TAC RADICAL_LINE_LINE_INTERSECTION THEN ASM_MESON_TAC[];
    MATCH_MP_TAC RADICAL_LINE_CIRCLE_INTERSECTION THEN ASM_MESON_TAC[];
    MATCH_MP_TAC RADICAL_CIRCLE_CIRCLE_INTERSECTION THEN ASM_MESON_TAC[]])
```

### Informal statement
For all `x`, if `x` is constructible, then both the first and second coordinates of `x` are radical.

### Informal sketch
* The proof proceeds by induction on the `constructible` property, using `constructible_INDUCT`.
* It first splits the goal into two conjuncts using `CONJ_TAC`, then generalizes the variables and strips the universal quantifier.
* The base case and inductive steps involve applying specific rules and theorems:
  + `RADICAL_RULES` are used for simplification.
  + `RADICAL_LINE_LINE_INTERSECTION`, `RADICAL_LINE_CIRCLE_INTERSECTION`, and `RADICAL_CIRCLE_CIRCLE_INTERSECTION` are applied to cover different intersection cases, leveraging `MATCH_MP_TAC` and `ASM_MESON_TAC` for proof construction.

### Mathematical insight
This theorem establishes a crucial property of constructible points, namely that their coordinates are radical. This is foundational in geometric constructions, as it ensures that points obtained through certain geometric operations (like intersections) have coordinates that can be expressed using radicals, which is a fundamental concept in algebraic geometry.

### Dependencies
#### Theorems
* `RADICAL_LINE_LINE_INTERSECTION`
* `RADICAL_LINE_CIRCLE_INTERSECTION`
* `RADICAL_CIRCLE_CIRCLE_INTERSECTION`
#### Definitions
* `constructible`
* `radical`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how induction is handled, especially the `constructible_INDUCT` rule, as the specific induction tactic might differ. Additionally, ensure that the `RADICAL_RULES` and other theorems about radical numbers and geometric intersections are properly defined and accessible in the target system.

---

## DOUBLE_THE_CUBE_ALGEBRA

### Name of formal statement
DOUBLE_THE_CUBE_ALGEBRA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DOUBLE_THE_CUBE_ALGEBRA = prove
 (`~(?x. radical x /\ x pow 3 = &2)`,
  STRIP_TAC THEN MP_TAC(SPECL [`&0`; `&0`; `-- &2`] CUBIC_ROOT_INTEGER) THEN
  SIMP_TAC[INTEGER_CLOSED; NOT_IMP] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[GSYM real_sub; REAL_SUB_0] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `abs`) THEN
  REWRITE_TAC[REAL_ABS_POW] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[integer]) THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(ARITH_RULE
   `n EXP 3 <= 1 EXP 3 \/ 2 EXP 3 <= n EXP 3 ==> ~(n EXP 3 = 2)`) THEN
  REWRITE_TAC[num_CONV `3`; EXP_MONO_LE; NOT_SUC] THEN ARITH_TAC)
```

### Informal statement
It is not the case that there exists a real number $x$ such that $x$ is radical (i.e., $x$ is not a perfect power of a rational number) and $x^3 = 2$. 

### Informal sketch
* The proof starts by assuming the existence of a real number $x$ such that $x$ is radical and $x^3 = 2$.
* It then uses the `CUBIC_ROOT_INTEGER` theorem to derive a contradiction.
* The `STRIP_TAC` and `MP_TAC` tactics are used to manage assumptions and apply theorems.
* The proof involves rewriting expressions using various theorems such as `INTEGER_CLOSED`, `REAL_MUL_LZERO`, and `REAL_ADD_LID`.
* The `CONJ_TAC` tactic is used to split the proof into two cases, and the `ASM_MESON_TAC` tactic is used to discharge one of the cases.
* The proof then proceeds to use the `abs` function and properties of absolute value to derive further contradictions.
* The `MATCH_MP_TAC` tactic is used to apply an arithmetic rule, and the `ARITH_TAC` tactic is used to perform arithmetic reasoning.

### Mathematical insight
This theorem is a classic result in mathematics, known as the "impossibility of doubling the cube". It states that it is impossible to construct a cube with twice the volume of a given cube using only a compass and straightedge. The theorem has important implications in geometry and algebra, and is often used as a demonstration of the limitations of geometric construction.

### Dependencies
* Theorems:
  * `CUBIC_ROOT_INTEGER`
  * `INTEGER_CLOSED`
  * `REAL_MUL_LZERO`
  * `REAL_ADD_LID`
  * `REAL_ABS_POW`
  * `REAL_ABS_NUM`
  * `REAL_OF_NUM_POW`
  * `REAL_OF_NUM_EQ`
  * `EXP_MONO_LE`
  * `NOT_SUC`
* Definitions:
  * `radical`
  * `abs`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the arithmetic and algebraic libraries are properly aligned. In particular, the `ARITH_TAC` tactic may need to be replaced with a similar tactic in the target system. Additionally, the `MATCH_MP_TAC` tactic may need to be replaced with a similar tactic that applies a rule to a goal. The use of `CONJ_TAC` and `ASM_MESON_TAC` tactics may also require special attention, as they are used to manage assumptions and discharge cases.

---

## DOUBLE_THE_CUBE

### Name of formal statement
DOUBLE_THE_CUBE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DOUBLE_THE_CUBE = prove
 (`!x. x pow 3 = &2 ==> ~(constructible(vector[x; &0]))`,
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONSTRUCTIBLE_RADICAL) THEN
  REWRITE_TAC[VECTOR_2; RADICAL_RULES] THEN
  ASM_MESON_TAC[DOUBLE_THE_CUBE_ALGEBRA]);;
```

### Informal statement
For all x, if x to the power of 3 equals 2, then the vector [x; 0] is not constructible.

### Informal sketch
* The proof starts by assuming `x pow 3 = &2` and aims to show that `vector[x; &0]` is not constructible.
* It applies `GEN_TAC` to generalize the assumption, followed by `DISCH_TAC` to discharge the assumption.
* Then, it uses `DISCH_THEN` with `MP_TAC` and `MATCH_MP CONSTRUCTIBLE_RADICAL` to apply a rule related to constructibility and radicals.
* The proof continues with `REWRITE_TAC` using `VECTOR_2` and `RADICAL_RULES` to rewrite expressions.
* Finally, `ASM_MESON_TAC` is applied with `DOUBLE_THE_CUBE_ALGEBRA` to derive the conclusion.

### Mathematical insight
This theorem is related to the problem of "doubling the cube," a classic problem in geometry where one is asked to construct a cube with twice the volume of a given cube using only a compass and straightedge. The formal statement here touches on the idea that certain constructions are not possible with these limited tools, specifically concerning the constructibility of vectors related to the solution of `x^3 = 2`.

### Dependencies
* Theorems:
  - `CONSTRUCTIBLE_RADICAL`
  - `DOUBLE_THE_CUBE_ALGEBRA`
* Definitions:
  - `constructible`
  - `vector`
  - `pow`
* Other:
  - `VECTOR_2`
  - `RADICAL_RULES`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how each system handles quantifiers, vector operations, and constructibility predicates. The `GEN_TAC`, `DISCH_TAC`, and `DISCH_THEN` tactics may have direct counterparts in other systems, but `MATCH_MP`, `REWRITE_TAC`, and `ASM_MESON_TAC` might require more careful translation due to differences in how these systems handle term matching and meson-style proof search. Additionally, ensure that the ported version correctly captures the mathematical structure of the original proof, including the application of `CONSTRUCTIBLE_RADICAL` and `DOUBLE_THE_CUBE_ALGEBRA`.

---

## COS_TRIPLE

### Name of formal statement
COS_TRIPLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COS_TRIPLE = prove
 (`!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos(x)`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&3 * x = x + x + x`; SIN_ADD; COS_ADD] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;
```

### Informal statement
For all real numbers x, the cosine of 3x is equal to 4 times the cosine of x cubed minus 3 times the cosine of x.

### Informal sketch
* The proof starts by generalizing the statement for all real numbers x using `GEN_TAC`.
* It then applies `REWRITE_TAC` to expand the expression `&3 * x` into `x + x + x` using `REAL_ARITH`, and applies trigonometric identities `SIN_ADD` and `COS_ADD`.
* The proof then uses `MP_TAC` to apply the `SIN_CIRCLE` theorem, specialized for `x:real`, to derive the desired equality.
* Finally, `CONV_TAC REAL_RING` is used to simplify the expression using the properties of real numbers.

### Mathematical insight
This theorem provides a trigonometric identity that relates the cosine of a triple angle to the cosine of the original angle. This is a fundamental result in trigonometry, useful in various mathematical and scientific applications. The proof showcases the use of algebraic manipulations and trigonometric identities to derive the result.

### Dependencies
#### Theorems
* `SIN_CIRCLE`
#### Definitions
* `REAL_ARITH`
* `SIN_ADD`
* `COS_ADD`
* `REAL_RING`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of real numbers and trigonometric functions. The `REAL_ARITH` and `REAL_RING` theorems may need to be replaced with equivalent constructs in the target system. Additionally, the `GEN_TAC` and `MP_TAC` tactics may have different counterparts in other systems, requiring adjustments to the proof script.

---

## COS_PI3

### Name of formal statement
COS_PI3

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COS_PI3 = prove
 (`cos(pi / &3) = &1 / &2`,
  MP_TAC(SPEC `pi / &3` COS_TRIPLE) THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH; COS_PI] THEN
  REWRITE_TAC[REAL_RING
   `-- &1 = &4 * c pow 3 - &3 * c <=> c = &1 / &2 \/ c = -- &1`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN
  MP_TAC(SPEC `pi / &3` COS_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC)
```

### Informal statement
The cosine of one-third of pi is equal to one-half.

### Informal sketch
* The proof starts by applying the `COS_TRIPLE` theorem with `pi / &3` as a special case, using `MP_TAC`.
* It then simplifies the expression using `SIMP_TAC` with various theorems such as `REAL_DIV_LMUL`, `REAL_OF_NUM_EQ`, `ARITH`, and `COS_PI`.
* The proof then applies `REWRITE_TAC` to transform the equation `-- &1 = &4 * c pow 3 - &3 * c` into a disjunction of two equations, and then proceeds with a case analysis using `DISCH_THEN` and `DISJ_CASES_THEN2`.
* The proof also uses `MP_TAC` to apply the `COS_POS_PI` theorem with `pi / &3` as a special case, and `PI_POS` to establish a positivity fact.
* Finally, the proof concludes with `REAL_ARITH_TAC`, which performs real arithmetic to establish the final result.

### Mathematical insight
This theorem is a specific trigonometric identity that relates the cosine function to a rational value. It is likely used as a building block in more complex trigonometric proofs or calculations.

### Dependencies
* Theorems:
  + `COS_TRIPLE`
  + `COS_POS_PI`
  + `PI_POS`
  + `REAL_DIV_LMUL`
  + `REAL_OF_NUM_EQ`
  + `ARITH`
  + `COS_PI`
  + `REAL_RING`
* Tactics:
  + `MP_TAC`
  + `SIMP_TAC`
  + `REWRITE_TAC`
  + `DISCH_THEN`
  + `DISJ_CASES_THEN2`
  + `REAL_ARITH_TAC`

### Porting notes
When porting this theorem to another proof assistant, note that the `REAL_ARITH_TAC` tactic may need to be replaced with a corresponding tactic or set of tactics that perform real arithmetic. Additionally, the `MP_TAC` and `SIMP_TAC` tactics may have different names or behaviors in other systems, and the `REWRITE_TAC` tactic may require a different syntax for specifying the rewrite rules.

---

## TRISECT_60_DEGREES_ALGEBRA

### Name of formal statement
TRISECT_60_DEGREES_ALGEBRA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TRISECT_60_DEGREES_ALGEBRA = prove
 (`~(?x. radical x /\ x pow 3 - &3 * x - &1 = &0)`,
  STRIP_TAC THEN MP_TAC(SPECL [`&0`; `-- &3`; `-- &1`] CUBIC_ROOT_INTEGER) THEN
  SIMP_TAC[INTEGER_CLOSED; NOT_IMP] THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; REAL_MUL_LNEG; GSYM real_sub] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `x pow 3 - &3 * x - &1 = &0 <=> x * (x pow 2 - &3) = &1`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `abs`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[integer]) THEN
  REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC (ARITH_RULE
   `n = 0 \/ n = 1 \/ n = 2 + (n - 2)`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[REAL_ARITH `(&2 + m) pow 2 - &3 = m pow 2 + &4 * m + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_ABS_NUM;
              REAL_OF_NUM_EQ; MULT_EQ_1] THEN
  ARITH_TAC)
```

### Informal statement
There does not exist a real number $x$ that is radical and satisfies the equation $x^3 - 3x - 1 = 0$.

### Informal sketch
* The proof starts by assuming the existence of a real number $x$ that satisfies the given equation and is radical.
* It then applies the `CUBIC_ROOT_INTEGER` theorem with specific values to derive a contradiction.
* The proof involves simplifying the equation using `REAL_ARITH`, and then using `CONJ_TAC` to split the proof into two cases.
* It further applies various rewrite rules, such as `REAL_ADD_ASSOC`, `REAL_MUL_LZERO`, and `REAL_ADD_RID`, to simplify the expressions.
* The proof also uses `ABS` and `REAL_ABS_MUL` to reason about absolute values, and `ARITH_RULE` to perform arithmetic manipulations.
* The final step involves using `CONV_TAC` and `REAL_RAT_REDUCE_CONV` to reduce the expression to a simpler form, and then applying `ARITH_TAC` to derive the contradiction.

### Mathematical insight
This theorem is important because it shows that there is no real number that can be expressed as a radical (i.e., as a root of a polynomial equation with integer coefficients) and also satisfies the equation $x^3 - 3x - 1 = 0$. This has implications for the solvability of cubic equations and the nature of radical numbers.

### Dependencies
* `CUBIC_ROOT_INTEGER`
* `INTEGER_CLOSED`
* `NOT_IMP`
* `REAL_ADD_ASSOC`
* `REAL_MUL_LZERO`
* `REAL_ADD_RID`
* `REAL_MUL_LNEG`
* `GSYM real_sub`
* `REAL_ARITH`
* `ABS`
* `REAL_ABS_MUL`
* `REAL_ABS_NUM`
* `GSYM REAL_POW2_ABS`
* `ARITH_RULE`
* `CONV_TAC`
* `REAL_RAT_REDUCE_CONV`
* `REAL_OF_NUM_ADD`
* `REAL_OF_NUM_MUL`
* `REAL_OF_NUM_POW`
* `REAL_OF_NUM_EQ`
* `MULT_EQ_1`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of radical numbers and the `CUBIC_ROOT_INTEGER` theorem, as the exact formulation and proof of this theorem may vary between systems. Additionally, the use of `ARITH_TAC` and `CONV_TAC` may need to be replaced with equivalent tactics in the target system.

---

## TRISECT_60_DEGREES

### Name of formal statement
TRISECT_60_DEGREES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TRISECT_60_DEGREES = prove
 (`!y. ~(constructible(vector[cos(pi / &9); y]))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CONSTRUCTIBLE_RADICAL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[VECTOR_2] THEN
  DISCH_TAC THEN MP_TAC(SPEC `pi / &9` COS_TRIPLE) THEN
  SIMP_TAC[REAL_ARITH `&3 * x / &9 = x / &3`; COS_PI3] THEN
  REWRITE_TAC[REAL_ARITH
   `&1 / &2 = &4 * c pow 3 - &3 * c <=>
    (&2 * c) pow 3 - &3 * (&2 * c) - &1 = &0`] THEN
  ASM_MESON_TAC[TRISECT_60_DEGREES_ALGEBRA; RADICAL_RULES])
```

### Informal statement
For all `y`, it is not the case that the vector `[cos(pi / 9); y]` is constructible.

### Informal sketch
* The proof starts by assuming the existence of `y` such that the vector is constructible, then applies `CONSTRUCTIBLE_RADICAL` to derive a contradiction.
* It uses `COS_TRIPLE` to establish a relationship involving `cos(pi / 9)`, which is then simplified using `REAL_ARITH` to express the condition in terms of a polynomial equation.
* The proof further simplifies the equation and applies `TRISECT_60_DEGREES_ALGEBRA` and `RADICAL_RULES` to reach a contradiction, thus proving the statement.

### Mathematical insight
This theorem is related to the problem of trisecting an angle of 60 degrees using only a compass and straightedge, which is a classic problem in geometric construction. The theorem likely shows that such a construction is impossible by demonstrating that a certain vector, which would be necessary for the construction, is not constructible.

### Dependencies
* Theorems:
  + `CONSTRUCTIBLE_RADICAL`
  + `COS_TRIPLE`
  + `TRISECT_60_DEGREES_ALGEBRA`
* Definitions:
  + `constructible`
  + `vector`
  + `cos`
  + `pi`
* Axioms/Rules:
  + `RADICAL_RULES`
  + `REAL_ARITH` 

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to handling the `constructible` predicate, the `cos` function, and the `REAL_ARITH` and `RADICAL_RULES` theorems, as these may have different implementations or requirements in other systems. Additionally, the use of `GEN_TAC`, `DISCH_THEN`, and `MP_TAC` tactics may need to be adapted to the target system's tactic language.

---

