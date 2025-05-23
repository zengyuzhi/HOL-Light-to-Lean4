# constructible.ml

## Overview

Number of statements: 49

`constructible.ml` formalizes the non-constructibility of solutions to irrational cubic equations, proving the impossibility of angle trisection and doubling the cube using traditional geometric constructions. The proof, adapted from Dickson, avoids field extensions. It builds upon prime number theory, floor function properties, and transcendental functions defined in imported files.


## STEP_LEMMA

### Name of formal statement
STEP_LEMMA

### Type of the formal statement
theorem

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
  CONV_TAC REAL_RING);;
```

### Informal statement
For any property `P` on real numbers, if `P` holds for all integers, `P` is closed under negation, `P` holds for the inverse of a non-zero real number if it holds for that number, `P` is closed under addition, and `P` is closed under multiplication, then for all real numbers `a`, `b`, `c`, `z`, `u`, `v`, and `s`, if `P` holds for `a`, `b`, and `c`, `z` is a root of the cubic `z^3 + a*z^2 + b*z + c = 0`, `P` holds for `u` and `v`, `P` holds for `s^2`, and `z = u + v*s`, then there exists a real number `w` such that `P` holds for `w` and `w` is a root of the cubic `w^3 + a*w^2 + b*w + c = 0`.

### Informal sketch
The theorem states that if the roots of a cubic equation `z^3 + a*z^2 + b*z + c = 0` can be written as `z = u + v*s`, where `P` holds for `a`, `b`, `c`, `u`, `v` and `s^2`, then there exists another root `w` of the same cubic equation such that `P` holds for `w`.
The proof proceeds by case analysis on `v * s = 0`.
- Case 1: `v * s = 0`. In this case `z = u`, and since `P(u)` is assumed, we are done.
- Case 2: `v * s != 0`.
  - Define `A = a * (s^2) * (v^2) + 3 * (s^2) * u * (v^2) + a * (u^2) + (u^3) +  b * u + c` and `B = (s^2) * (v^3) + 2 * a * u * v + 3 * (u^2) * v + b * v`.
  - Show that `A + B * s = 0` by using the fact that `z` is a root and polynomial arithmetic using the `REAL_RING` tactic.
  - Case split on `P(s)`
    - If `P(s)` holds, then the root `--(a + 2 * u)` is shown to satisfy both the cubic equation and `P`.
    - If `~P(s)` holds, then derive `B = 0` using the field tactic `REAL_FIELD` to derive `s = --A / B`, which leads to a series of arithmetic manipulations. Finally we obtain a contradiction, completing the proof.
The final step concludes by exhibiting `w = -(a + 2*u)` and showing that `P(w)` holds and `w` is a root of the given cubic.

### Mathematical insight
This lemma is a key step in proving the non-constructibility of solutions to cubic equations. It hinges on the idea of a property `P` that is preserved through certain algebraic operations (addition, multiplication, negation, inversion) and shows how such a property restricts the possible roots of a cubic equation. It gives a condition under which the roots of a cubic cannot be expressed using only operations that preserve property `P`.

### Dependencies

**Theorems:**
- `REAL_ADD_RID`
- `GSYM CONTRAPOS_THM`
- `REAL_FIELD`

**Tactics:**
- `REAL_RING`

**Files:**
- `Library/prime.ml`
- `Library/floor.ml`
- `Multivariate/transcendentals.ml`


---

## STEP_LEMMA_SQRT

### Name of formal statement
STEP_LEMMA_SQRT

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[SQRT_POW_2; REAL_POW_2]);;
```

### Informal statement
Given a predicate `P` on real numbers such that:
1. `P(n)` holds for every natural number `n`;
2. If `P(x)` holds, then `P(-x)` holds;
3. If `P(x)` holds and `x` is not zero, then `P(1/x)` holds;
4. If `P(x)` and `P(y)` hold, then `P(x + y)` holds;
5. If `P(x)` and `P(y)` hold, then `P(x * y)` holds;

Then, for all real numbers `a`, `b`, `c`, `z`, `u`, `v`, and `s`, if:
1. `P(a)`, `P(b)`, `P(c)` hold;
2. `z^3 + a * z^2 + b * z + c = 0`;
3. `P(u)`, `P(v)`, `P(s)` hold;
4. `0 <= s`;
5. `z = u + v * sqrt(s)`;

Then, there exists a real number `w` such that:
1. `P(w)` holds;
2. `w^3 + a * w^2 + b * w + c = 0`.

### Informal sketch
The proof proceeds as follows:
- Assume the hypotheses of the theorem, including the predicate `P`'s properties and the existence of `a`, `b`, `c`, `z`, `u`, `v`, `s` satisfying the given conditions.
- Apply `STEP_LEMMA` (presumably a lemma about polynomial roots and field extensions), which likely provides a root `w` expressible in terms of `a`, `b`, `c`.
- Use the assumptions about `P` being closed under negation, inversion, addition, and multiplication of real numbers, along with `P` holding for natural numbers, to show that `P(w)` holds. This involves demonstrating that `w` can be constructed from `a`, `b`, `c`, `u`, `v`, and `s` using operations that preserve `P`. The lemmas `SQRT_POW_2` and `REAL_POW_2` are used to express square roots using exponentiation and thus multiplication.
- Conclude that there exists a `w` such that `P(w)` and `w^3 + a * w^2 + b * w + c = 0`.

### Mathematical insight
This theorem shows that if the coefficients of a cubic polynomial satisfy a predicate `P` closed under basic arithmetic operations and `P` is hereditary for natural numbers, and a root `z` can be expressed using terms satisfying `P` (including square roots of non-negative terms satisfying `P`), then there exists another root `w` also satisfying `P`. This formalizes the idea that if you start with numbers satisfying `P` and can express a root using arithmetic operations and square roots, then at least one root also satisfies `P`.

### Dependencies
- `STEP_LEMMA`
- `SQRT_POW_2`
- `REAL_POW_2`


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
  (!x. radical x /\ &0 <= x ==> radical (sqrt x))`;;
```
### Informal statement
The predicate `radical x` holds if and only if any of the following conditions are met:
- `x` is a rational number.
- `radical (--x)` holds.
- `radical x` holds and `x` is not equal to 0, and `radical (inv x)` holds.
- `radical x` holds and `radical y` holds, and `radical (x + y)` holds.
- `radical x` holds and `radical y` holds, and `radical (x * y)` holds.
- `radical x` holds and `0 <= x`, and `radical (sqrt x)` holds.

### Informal sketch
The definition introduces the set of numbers constructible from rationals using inverse, negation, addition, multiplication, and square roots. This is done via an inductive definition:

- The base case is that any rational number is a `radical`.
- The negation of a `radical` is a `radical`.
- The inverse of a non-zero radical is a `radical`.
- The sum of two `radicals` is a `radical`.
- The product of two `radicals` is a `radical`.
- The square root of a nonnegative `radical` is a `radical`.

These rules form the introduction rules `radical_RULES` for the inductively defined set `radical`. The induction principle `radical_INDUCT` and case analysis principle `radical_CASES` are automatically derived from these rules.

### Mathematical insight
This inductive definition characterizes the field extension of the rationals obtained by repeatedly adjoining square roots. It is a formalization of numbers constructible by radicals involving square roots only.

### Dependencies
- `rational`
- `inv`
- `sqrt`

### Porting notes (optional)
When porting to other proof assistants, ensure the inductive definition mechanism correctly handles the mutual dependencies and generates the corresponding introduction rules, induction principle, and case analysis principle. Pay attention to any differences in how rational numbers, inverses, and square roots are represented and defined.


---

## RADICAL_RULES

### Name of formal statement
RADICAL_RULES

### Type of the formal statement
theorem

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
  ASM_SIMP_TAC[radical_RULES; real_pow; RATIONAL_NUM]);;
```

### Informal statement
The following properties hold for the predicate `radical`:
- For every natural number `n`, `radical(n)` holds.
- For every `x`, if `x` is rational, then `radical(x)` holds.
- For every `x`, if `radical(x)` holds, then `radical(-x)` holds.
- For every `x`, if `radical(x)` holds and `x` is not equal to 0, then `radical(1/x)` holds.
- For every `x` and `y`, if `radical(x)` holds and `radical(y)` holds, then `radical(x + y)` holds.
- For every `x` and `y`, if `radical(x)` holds and `radical(y)` holds, then `radical(x - y)` holds.
- For every `x` and `y`, if `radical(x)` holds and `radical(y)` holds, then `radical(x * y)` holds.
- For every `x` and `y`, if `radical(x)` holds and `radical(y)` holds and `y` is not equal to 0, then `radical(x / y)` holds.
- For every `x` and natural number `n`, if `radical(x)` holds, then `radical(x^n)` holds.
- For every `x`, if `radical(x)` holds and `0 <= x`, then `radical(sqrt(x))` holds.

### Informal sketch
The proof proceeds as follows:
- First, simplification is applied using rules for `real_div`, `real_sub`, `radical_RULES` (likely to handle base cases or simplify expressions involving radicals), and `RATIONAL_NUM` to simplify rational number expressions.
- Then, generalization is applied to remove any assumptions that may be present.
- Next, induction is performed. The induction is likely on a variable implicitly introduced by the generalization tactic, possibly on a natural number.
- Finally, simplification is applied using the assumptions, plus rules for `radical_RULES`, `real_pow`, and `RATIONAL_NUM`, further simplifying the goal based on the induction hypothesis.

### Mathematical insight
The theorem `RADICAL_RULES` expresses the closure properties of the set of "radical" numbers under various arithmetic operations such as addition, subtraction, multiplication, division, exponentiation by natural numbers, negation, reciprocation, and square root (if non-negative). Furthermore, it states that all rational numbers and all natural numbers are “radical”. This theorem essentially defines a subfield of the real numbers that is closed under square roots and contains the rational numbers. Informally a real number is "radical" if it can be obtained from integers using the operations of addition, subtraction, multiplication, division, and taking nth roots.

### Dependencies
- `real_div`
- `real_sub`
- `radical_RULES` (appears to be used recursively, suggesting it breaks down the goal into smaller parts and uses existing rules.)
- `RATIONAL_NUM`
- `real_pow`

### Porting notes (optional)
- The recursive use of `radical_RULES` within the simplification tactics may require careful attention during porting. It might be necessary to adjust the order of simplification or use different techniques to achieve the same effect in another proof assistant.
- Handling the arithmetic operations and rational numbers may depend on the specific libraries available in the target proof assistant.


---

## RADICAL_TAC

### Name of formal statement
RADICAL_TAC

### Type of the formal statement
Theorem-proving tactic

### Formal Content
```ocaml
let RADICAL_TAC =
  REPEAT(MATCH_ACCEPT_TAC (CONJUNCT1 RADICAL_RULES) ORELSE
         (MAP_FIRST MATCH_MP_TAC(tl(tl(CONJUNCTS RADICAL_RULES))) THEN
          REPEAT CONJ_TAC));;
```

### Informal statement
`RADICAL_TAC` is a tactic that repeatedly applies radical simplification rules to a goal. It first attempts to directly apply the first conjunct of `RADICAL_RULES` using `MATCH_ACCEPT_TAC`. If that fails, it attempts to apply the modus ponens rule (`MATCH_MP_TAC`) using the result of the list of conjuncts of `RADICAL_RULES` skipping the first two elements `tl(tl(CONJUNCTS RADICAL_RULES)))`, and then splits the resulting goal into subgoals using `REPEAT CONJ_TAC`.

### Informal sketch
The tactic `RADICAL_TAC` performs the following steps repeatedly:

- Attempt to directly solve the goal using `MATCH_ACCEPT_TAC` with the first conjunct of `RADICAL_RULES`. This likely involves matching the goal exactly with a simplified radical expression. If this succeeds, the goal is solved.

- If direct matching fails, attempt to apply the Modus Ponens rule (`MATCH_MP_TAC`).
  - Consider the list of conjuncts derived from `RADICAL_RULES`, dropping the first two elements (`tl(tl(CONJUNCTS RADICAL_RULES)))`. These conjuncts are likely implications.
  - Apply `MATCH_MP_TAC` to the goal using each of these implications in turn. This attempts to rewrite the goal based on the implications related to radicals (likely of the form P => Q where the expression P has been matched).

- If Modus Ponens application introduces conjunctions (e.g., from applying an implication that simplifies something to a conjunction), split the goal into its constituent conjuncts (`REPEAT CONJ_TAC`). This prepares the subgoals for further simplification.

### Mathematical insight
The tactic aims to simplify expressions involving radicals by repeatedly applying simplification rules. The first conjunct of `RADICAL_RULES` is probably an equational axiom that directly rewrites certain radical expressions. The remaining conjuncts (after skipping the first two elements), which are implications, likely represent conditional simplification rules for radicals. The repeated application and splitting of conjunctions ensure that all parts of the goal are simplified using the given rules. This tactic seems to automate some basic reasoning about radicals.

### Dependencies
- `RADICAL_RULES`
- `MATCH_ACCEPT_TAC`
- `CONJUNCT1`
- `MATCH_MP_TAC`
- `tl`
- `CONJUNCTS`
- `REPEAT`
- `CONJ_TAC`
- `MAP_FIRST`

### Porting notes (optional)
- `MATCH_ACCEPT_TAC` corresponds to `exact` in Coq/Lean, or `simp` in Isabelle.
- `MATCH_MP_TAC` corresponds to `apply` or `refine` in Coq/Lean, or `rule` in Isabelle.
- The tactic combinators like `REPEAT` and `ORELSE` are common across proof assistants but may have subtly different behaviors. The `MAP_FIRST` should be translated with care as the order of rule applications can influence proof search.
- Consider using a list of rewrite rules to encode the RADICAL_RULES for simplifications.


---

## expression_INDUCT,expression_RECURSION

### Name of formal statement
- expression_INDUCT,expression_RECURSION

### Type of the formal statement
- new_type_definition

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
- Define a new type `expression` which can take the following forms:
    - `Constant r`, where `r` is a real number.
    - `Negation e`, where `e` is an `expression`.
    - `Inverse e`, where `e` is an `expression`.
    - `Addition e1 e2`, where `e1` and `e2` are `expressions`.
    - `Multiplication e1 e2`, where `e1` and `e2` are `expressions`.
    - `Sqrt e`, where `e` is an `expression`.
- Simultaneously define two constants `expression_INDUCT` and `expression_RECURSION`, which represent the induction and recursion principles associated with the new type `expression`.

### Informal sketch
- This definition introduces a new algebraic datatype `expression` representing expressions built from real constants and unary/binary operations.
- The `define_type` call automatically derives an induction principle (`expression_INDUCT`) allowing proofs by structural induction over expressions, and a recursion principle (`expression_RECURSION`) to define functions by structural recursion over expression.
- The type definition proceeds by:
    - Defining the type `expression` itself.
    - Proving the distinctness and injectivity lemmas for constructors `Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, and `Sqrt`.
    - Deriving an induction principle `expression_INDUCT` to prove properties of all `expression` terms.
    - Deriving a recursion principle `expression_RECURSION` to define functions operating on `expression` terms.

### Mathematical insight
- This definition provides a formal representation of mathematical expressions, enabling formal reasoning about their properties. It is a standard inductive data type construction. The importance lies in the ability to perform inductive proofs about general expressions, rather than only concrete examples. This is a fundamental step in building a formal system for algebraic manipulation or analysis of expressions.

### Dependencies
- `real`

### Porting notes (optional)
- Most proof assistants have built-in support for defining inductive datatypes and deriving induction principles automatically. In Lean or Coq, the `inductive` or `Inductive` keyword can be used, respectively. The distinctness and injectivity lemmas are usually generated automatically by the system, and the induction principle is typically available as `expression.induct` or a similar name. The recursion principle may require manual definition using pattern matching or similar features.


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
  (value(Sqrt e) = sqrt(value e))`;;
```
### Informal statement
The function `value` is defined recursively on expressions as follows:
- The value of a constant `x` is `x`.
- The value of the negation of an expression `e` is the negation of the value of `e`.
- The value of the inverse of an expression `e` is the inverse of the value of `e`.
- The value of the addition of expressions `e1` and `e2` is the sum of the value of `e1` and the value of `e2`.
- The value of the multiplication of expressions `e1` and `e2` is the product of the value of `e1` and the value of `e2`.
- The value of the square root of an expression `e` is the square root of the value of `e`.

### Informal sketch
The definition of `value` is a primitive recursive definition over an expression datatype.
- The definition provides a case for each constructor of the expression datatype: `Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, and `Sqrt`.
- Each case specifies how to compute the value of an expression built using that constructor, in terms of the values of its subexpressions.

### Mathematical insight
This definition provides a semantic interpretation for expressions by giving them a numerical value. It recursively transforms a symbolic expression into the result of evaluating the expression within the real numbers.

### Dependencies
None (assumes standard arithmetic operators and `sqrt` are defined)

### Porting notes (optional)
This definition can be ported to other proof assistants by defining a suitable expression datatype and then defining the `value` function by structural recursion. In systems like Coq or Lean, the termination of the recursive definition should be automatically provable by the structural descent on the expression datatype. Ensure that the types of the arithmetic operations are appropriately aligned in the target system. Handling the square root function might require some care, depending on how the target system represents real numbers and deals with partial functions.


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
The expression `e` is wellformed if and only if:
- when `e` is a `Constant x`, then `x` is a rational number;
- when `e` is a `Negation e'`, then `e'` is wellformed;
- when `e` is an `Inverse e'`, then the `value` of `e'` is not equal to 0, and `e'` is wellformed;
- when `e` is an `Addition e1 e2`, then `e1` is wellformed and `e2` is wellformed;
- when `e` is a `Multiplication e1 e2`, then `e1` is wellformed and `e2` is wellformed;
- when `e` is a `Sqrt e'`, then 0 is less than or equal to the `value` of `e'`, and `e'` is wellformed.

### Informal sketch
The definition introduces the concept of a well-formed expression, defining it recursively based on the structure of expressions:

- Base case: A `Constant` is well-formed if it represents a rational number.
- Inductive cases:
  - `Negation e` is well-formed if `e` is well-formed.
  - `Inverse e` is well-formed if `e` is well-formed and its value is not zero.
  - `Addition e1 e2` is well-formed if both `e1` and `e2` are well-formed.
  - `Multiplication e1 e2` is well-formed if both `e1` and `e2` are well-formed.
  - `Sqrt e` is well-formed if `e` is well-formed and its value is non-negative.

The definition proceeds by using the `define` keyword in HOL Light, which automatically handles the proof of existence and uniqueness for such recursive definitions. No manual proof is required.

### Mathematical insight
The `wellformed` predicate ensures that expressions satisfy certain conditions depending on their structure. This is similar to a type system, where certain operations require certain properties to hold, such as not taking the inverse of zero or the square root of a negative number. This predicate helps to restrict the domain of expressions to those that are mathematically meaningful, preventing errors or undefined behavior during evaluation.

### Dependencies
- `rational`
- `value`

### Porting notes (optional)
This definition is straightforward to port as it consists of defining a recursive predicate over an algebraic datatype. Most proof assistants will have similar mechanisms for defining such predicates, for example, using `Inductive` in Coq or `inductive` in Isabelle. The key is to ensure that the underlying expression datatype (`Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, `Sqrt`) with its constructors and the `value` function are defined equivalently in the target system.


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
  (radicals(Sqrt e) = e INSERT (radicals e))`;;
```

### Informal statement
The function `radicals` is defined on expressions as follows:
- For a constant `x`, `radicals(x)` is the empty set.
- For a negation `Negation e`, `radicals(Negation e)` is equal to `radicals(e)`.
- For an inverse `Inverse e`, `radicals(Inverse e)` is equal to `radicals(e)`.
- For an addition `Addition e1 e2`, `radicals(Addition e1 e2)` is the union of `radicals(e1)` and `radicals(e2)`.
- For a multiplication `Multiplication e1 e2`, `radicals(Multiplication e1 e2)` is the union of `radicals(e1)` and `radicals(e2)`.
- For a square root `Sqrt e`, `radicals(Sqrt e)` is the set containing `e` and all elements in `radicals(e)`.

### Informal sketch
The definition of `radicals` proceeds by structural recursion on the expression `e`.  The key idea is to accumulate all sub-expressions that appear under a square root.

- Base case: When the expression is a constant `Constant x`, there are no radicals, so the set of radicals is empty.
- Recursive cases:
    - Negation and inverse: `radicals` are the same as in the inner expression.
    - Addition and multiplication: `radicals` comprises the union of radicals of sub-expressions.
    - Square root: The expression under the square root is added to the set of radicals of the sub-expression.
The definition mirrors the structure of the expression data type to accumulate radicals.

### Mathematical insight
This definition identifies the "radicals" within an expression, which are essentially the sub-expressions that appear inside a square root. The definition follows a structural recursion, adding an expression to the set whenever it is found inside a `Sqrt`. This provides a way to track and reason about terms inside square roots, which can be useful for simplification, analysis, and other manipulations of expressions.

### Dependencies
None.

### Porting notes (optional)
When porting this definition to other proof assistants, ensure the target system supports defining functions by recursion on an algebraic datatype. The most direct approach is to define an analogous algebraic datatype for expressions and implement the `radicals` function as a recursive function over this datatype. Some proof assistants provide automated support for defining functions by structural recursion/induction. In systems like Coq or Lean, the `Definition` command or its variants along with pattern matching on the structure of the `e` term should work well.


---

## FINITE_RADICALS

### Name of formal statement
FINITE_RADICALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_RADICALS = prove
 (`!e. FINITE(radicals e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  SIMP_TAC[radicals; FINITE_RULES; FINITE_UNION]);;
```
### Informal statement
For all sets `e`, the set of radicals of `e` is finite.

### Informal sketch
The proof proceeds by induction on the structure of the set `e`.
- Base case: `expression_INDUCT` likely covers base cases like empty set, singleton set, etc., where the radicals are obviously finite.
- Inductive step: Assume that the radicals of the expressions `e1`, `e2`, ... `en` (depending on set structure) are finite.  Then show that the radicals of `e` (formed from `e1` ... `en`) are finite.
- `SIMP_TAC[radicals; FINITE_RULES; FINITE_UNION]` simplifies the goal using the definition of `radicals`, rules for finiteness (`FINITE_RULES`), and the fact that a finite union of finite sets is finite (`FINITE_UNION`).

### Mathematical insight
This theorem formalizes the intuition that if we start with a finite set and repeatedly take roots (extracting radicals), the resulting set of radicals will also be finite, reflecting the constrained nature of algebraic extensions generated this way. The definition of radicals is not provided, but the key idea is to show closure under the radical operation while preserving finiteness.

### Dependencies
- Definitions: `radicals`
- Theorems/Rules: `FINITE_RULES`,`FINITE_UNION`


---

## WELLFORMED_RADICALS

### Name of formal statement
WELLFORMED_RADICALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WELLFORMED_RADICALS = prove
 (`!e. wellformed e ==> !r. r IN radicals(e) ==> &0 <= value r`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; wellformed; NOT_IN_EMPTY; IN_UNION; IN_INSERT] THEN
  MESON_TAC[]);;
```

### Informal statement
For every expression `e`, if `e` is well-formed, then for every `r` in the radicals of `e`, `0` is less than or equal to the value of `r`.

### Informal sketch
The proof proceeds by induction on the structure of the expression `e`.

- **Base Case:** The base case is handled by the inductive tactic `expression_INDUCT`.
- **Inductive Step:**
    - Rewrite using the definitions of `radicals`, `wellformed`, `NOT_IN_EMPTY`, `IN_UNION`, and `IN_INSERT`. This step simplifies the goal, breaking it down based on how `radicals` and `wellformed` are defined for different expression forms.
    - Complete the proof using the MESON tactic, which automatically discharges the remaining subgoals.

### Mathematical insight
This theorem states that if an expression is well-formed, then the value of any radical within that expression must be non-negative. This is a crucial condition for defining real-valued expressions since the square root of a negative number is not real. This theorem ensures that the radicals appearing in well-formed expressions have real values.

### Dependencies
- Definitions: `radicals`, `wellformed`
- Theorems: `NOT_IN_EMPTY`, `IN_UNION`, `IN_INSERT`

### Porting notes (optional)
- The `expression_INDUCT` tactic encapsulates an inductive scheme specific to the `expression` datatype. In other proof assistants, you will need to define a corresponding inductive datatype for expressions and then explicitly perform induction on it.
- The `MESON_TAC` tactic is a powerful automated theorem prover in HOL Light. When porting to other proof assistants, you may need to manually prove the subgoals that `MESON_TAC` automatically handled or use a similar automated tactic if one exists.


---

## RADICALS_WELLFORMED

### Name of formal statement
RADICALS_WELLFORMED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RADICALS_WELLFORMED = prove
 (`!e. wellformed e ==> !r. r IN radicals e ==> wellformed r`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; wellformed; NOT_IN_EMPTY; IN_UNION; IN_INSERT] THEN
  MESON_TAC[]);;
```
### Informal statement
For every expression `e`, if `e` is well-formed, then for every expression `r`, if `r` is in the radicals of `e`, then `r` is well-formed.

### Informal sketch
The proof proceeds by induction on the structure of expressions `e`.

- **Base Case:** The base case follows trivially since `radicals e` is empty for atomic expressions, and hence the implication holds vacuously.
- **Inductive Step:** In the inductive step, we assume `e` is a composite expression and that the theorem holds for its immediate subexpressions. We use rewriting rules to expand the definitions of `radicals` and `wellformed` and then apply the inductive hypothesis to show that if `r` is in `radicals e`, then `r` is well-formed. Finally, we use a MESON proof search to complete the proof.

### Mathematical insight
This theorem establishes that the `radicals` function, when applied to a well-formed expression, only returns well-formed expressions. This is crucial for ensuring that any operations performed on the radicals of an expression are valid and maintain well-formedness.

### Dependencies
- Definitions: `radicals`, `wellformed`
- Theorems: `NOT_IN_EMPTY`, `IN_UNION`, `IN_INSERT`
- Tactics: `MATCH_MP_TAC`, `expression_INDUCT`, `REWRITE_TAC`, `MESON_TAC`


---

## RADICALS_SUBSET

### Name of formal statement
RADICALS_SUBSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RADICALS_SUBSET = prove
 (`!e r. r IN radicals e ==> radicals(r) SUBSET radicals(e)`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; IN_UNION; NOT_IN_EMPTY; IN_INSERT; SUBSET] THEN
  MESON_TAC[]);;
```
### Informal statement
For all sets of expressions `e` and expressions `r`, if `r` is in the set of radicals of `e`, then the set of radicals of `r` is a subset of the set of radicals of `e`.

### Informal sketch
The proof proceeds by induction on the structure of `e` (using `expression_INDUCT`). The base cases and inductive steps involve rewriting with the definitions of `radicals`, `IN_UNION`, `NOT_IN_EMPTY`, `IN_INSERT`, and `SUBSET`. Finally, the proof is completed by a call to the MESON prover. In essence, the proof leverages the inductive structure of expression sets and set-theoretic reasoning to establish the subset relation.

*   The base case handles when `e` is the empty set. In this case, `radicals e` is the empty set. Thus, `r IN radicals e` is false, and the implication is true vacuously.
*   The inductive step involves considering `e` as the insertion of some expression `x` into a set `s` (`INSERT x s`). Rewrite the statement using definitions of `radicals`, `IN_UNION`, `NOT_IN_EMPTY`, `IN_INSERT` and `SUBSET`. The inductive hypothesis states that the theorem holds for `s`. The goal is to prove it for `INSERT x s`. After rewriting, the call to `MESON_TAC` handles the propositional reasoning, combining the inductive hypothesis with the definitions to conclude the proof.

### Mathematical insight
This theorem demonstrates a fundamental property of the `radicals` function. It states that if an expression `r` is a radical of some expression set `e`, then all radicals of `r` are also radicals of `e`. This transitivity-like property is essential for reasoning about dependencies and relationships between expressions within a larger system.

### Dependencies
*   `radicals`
*   `IN_UNION`
*   `NOT_IN_EMPTY`
*   `IN_INSERT`
*   `SUBSET`
*   `expression_INDUCT`


---

## RADICAL_EXPRESSION

### Name of formal statement
RADICAL_EXPRESSION

### Type of the formal statement
theorem

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
    REWRITE_TAC[value; wellformed] THEN SIMP_TAC[radical_RULES]]);;
```

### Informal statement
For all real numbers `x`, `x` is a radical if and only if there exists a well-formed expression `e` such that `x` is equal to the value of `e`.

### Informal sketch
The proof proceeds in two directions to establish the biconditional:

*   **Direction 1 (radical x => ?e. wellformed e /\ x = value e):**
    *   We start with the assumption that `x` is a radical.
    *   We use induction on the definition of the `radical` predicate, which likely specifies basic cases and inductive steps for constructing radicals.
    *   We strip the quantifiers and implications.
    *   We repeatedly substitute using assumptions.
    *   We complete the proof using `ASM_MESON_TAC` with the definitions of `value` and `wellformed`. This step likely resolves the existence of a well-formed expression `e` by examining the cases generated via the induction.
*   **Direction 2 (?e. wellformed e /\ x = value e => radical x):**
    *   We begin by simplifying using `LEFT_IMP_EXISTS_THM`, swapping quantifiers with `SWAP_FORALL_THM`, rewriting implications as conjunctions using `IMP_CONJ`, moving quantifiers using `RIGHT_FORALL_IMP_THM` and `LEFT_FORALL_IMP_THM` and simplifying `EXISTS_REFL`.
    *   We use induction on the structure of expressions using `expression_INDUCT`.
    *   We then rewrite with the definitions of `value` and `wellformed`.
    *   We simplify with the radical rules defined in `radical_RULES`.

### Mathematical insight
This theorem establishes the equivalence between the predicate `radical x` and the existence of a well-formed expression `e` whose value is `x`.  It bridges the gap between a direct definition of radicals and a definition based on evaluating symbolic expressions. This highlights that every radical can be represented as the value of some expression, thus connecting semantic meaning to syntactic form.

### Dependencies
*   `radical_INDUCT`
*   `value`
*   `wellformed`
*   `LEFT_IMP_EXISTS_THM`
*   `SWAP_FORALL_THM`
*   `IMP_CONJ`
*   `RIGHT_FORALL_IMP_THM`
*   `LEFT_FORALL_IMP_THM`
*   `EXISTS_REFL`
*   `expression_INDUCT`
*   `radical_RULES`


---

## LT_MAX

### Name of formal statement
LT_MAX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LT_MAX = prove
 (`!a b c. a < MAX b c <=> a < b \/ a < c`,
  ARITH_TAC);;
```

### Informal statement
For all real numbers `a`, `b`, and `c`, `a` is less than the maximum of `b` and `c` if and only if `a` is less than `b` or `a` is less than `c`.

### Informal sketch
The proof is carried out using `ARITH_TAC`, an arithmetic decision procedure, which automatically proves the theorem based on the properties of inequalities and the definition of the `MAX` function. The tactic uses standard arithmetic reasoning about inequalities and disjunctions to establish the equivalence.

### Mathematical insight
This theorem expresses a fundamental property regarding the comparison of a number with the maximum of two other numbers. It states that `a` is less than the maximum of `b` and `c` exactly when `a` is less than at least one of `b` or `c`. This is a basic and useful property when dealing with inequalities involving maxima, and it can be conveniently used in various mathematical arguments and proofs.

### Dependencies
- `ARITH_TAC` (Tactic for automatic theorem proving in arithmetic)

### Porting notes (optional)
This theorem should be straightforward to port to other proof assistants. The main effort would likely be in ensuring that the target system has appropriate automated reasoning capabilities for arithmetic. In systems like Coq or Isabelle, the built-in arithmetic tactics (`lia` in Coq, `arith` in Isabelle) should be sufficient to prove this theorem with minimal manual intervention. In Lean, `linarith` or `norm_num` should suffice.


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
The function `depth` mapping expressions to natural numbers is defined recursively as follows:
- The depth of a `Constant x` is 0.
- The depth of `Negation e` is the depth of `e`.
- The depth of `Inverse e` is the depth of `e`.
- The depth of `Addition e1 e2` is the maximum of the depth of `e1` and the depth of `e2`.
- The depth of `Multiplication e1 e2` is the maximum of the depth of `e1` and the depth of `e2`.
- The depth of `Sqrt e` is 1 plus the depth of `e`.

### Informal sketch
The definition introduces a function `depth` through primitive recursion over the structure of expressions. Each clause corresponds to a different constructor of the expression type. The definition can be justified by showing that the arguments to the recursive calls are structurally smaller. Note that `Negation`, `Inverse`, `Addition`, `Multiplication`, and `Sqrt` are constructors in the expression type. The function computes the depth (or nesting level) of an expression.

### Mathematical insight
The `depth` function computes the maximum nesting level of the `Sqrt` operator within an expression. This is a measure of the structural complexity of the expression. The depth function is useful for inductive proofs about expressions, as it provides a well-founded ordering.

### Dependencies
None

### Porting notes (optional)
This definition should be straightforward to port to other proof assistants supporting recursive function definitions over algebraic datatypes. The main challenge might be in defining the expression type if it is not already available. One must declare the datatype representing the expression and its constructors (`Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, `Sqrt`) and then define the function `depth` by structural recursion on this type. You need to ensure that the `MAX` function is already defined for natural numbers.


---

## IN_RADICALS_SMALLER

### Name of formal statement
IN_RADICALS_SMALLER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IN_RADICALS_SMALLER = prove
 (`!r s. s IN radicals(r) ==> depth(s) < depth(r)`,
  MATCH_MP_TAC expression_INDUCT THEN REWRITE_TAC[radicals; depth] THEN
  REWRITE_TAC[IN_UNION; NOT_IN_EMPTY; IN_INSERT; LT_MAX] THEN
  MESON_TAC[ARITH_RULE `s = a \/ s < a ==> s < 1 + a`]);;
```

### Informal statement
For all `r` and `s`, if `s` is in the set of radicals of `r`, then the depth of `s` is less than the depth of `r`.

### Informal sketch
The proof proceeds by induction on the structure of the expression `r` using `expression_INDUCT`.
- The base cases (variables and constants) are handled implicitly
- Inductive steps involve rewriting using the definitions of `radicals` and `depth`. Specifically, we expand the definition of `radicals(r)` which involves unions and insertions and use `NOT_IN_EMPTY` and `IN_INSERT` to simplify membership assertions. Also, we appeal to `LT_MAX` and the definition of `depth`.
- Finally, `MESON_TAC` is used with an arithmetic rule `s = a \/ s < a ==> s < 1 + a` to discharge the goal.

### Mathematical insight
This theorem formalizes the intuition that the "radicals" of an expression, obtained by repeatedly extracting arguments of functions and operands of operators, have a strictly smaller depth than the original expression. The depth of an expression is defined as the maximum nesting depth of operators and function applications, so extracting a component necessarily reduces this depth.

### Dependencies
- Definitions: `radicals`, `depth`
- Theorems/Rules: `expression_INDUCT`, `IN_UNION`, `NOT_IN_EMPTY`, `IN_INSERT`, `LT_MAX`, `ARITH_RULE s = a \/ s < a ==> s < 1 + a`


---

## NOT_IN_OWN_RADICALS

### Name of formal statement
NOT_IN_OWN_RADICALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_IN_OWN_RADICALS = prove
 (`!r. ~(r IN radicals r)`,
  MESON_TAC[IN_RADICALS_SMALLER; LT_REFL]);;
```
### Informal statement
For all `r`, it is not the case that `r` is in `radicals r`.

### Informal sketch
The theorem states that no element is in the set of its own radicals. The proof uses `IN_RADICALS_SMALLER` which states that if `x` is in `radicals r`, then `x < r`. It also uses `LT_REFL` that implies `~(r < r)`. Combining `IN_RADICALS_SMALLER` and `LT_REFL` yields the result.

*   Assume `r IN radicals r`.
*   By `IN_RADICALS_SMALLER` (if `x IN radicals r` then `x < r`), derive `r < r`.
*   By `LT_REFL`, `~(r < r)`.
*   Contradiction.
*   Therefore, `~(r IN radicals r)`.

### Mathematical insight
The theorem ensures that the definition of `radicals` yields only elements strictly smaller than the original element. This property is crucial for ensuring the termination of algorithms based on repeated decomposition into radicals.

### Dependencies
- Theorems: `IN_RADICALS_SMALLER`, `LT_REFL`


---

## RADICALS_EMPTY_RATIONAL

### Name of formal statement
RADICALS_EMPTY_RATIONAL

### Type of the formal statement
theorem

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
For any expression `e`, if `e` is well-formed and the set of radicals of `e` is empty, then the value of `e` is a rational number.

### Informal sketch
The proof proceeds by induction on the structure of expressions `e`.

- The inductive step involves rewriting using definitions of `wellformed`, `value`, and `radicals`, along with lemmas about empty sets (`EMPTY_UNION`, `NOT_INSERT_EMPTY`).
- After applying the inductive hypothesis and discharging assumptions, the goal is simplified using `RATIONAL_CLOSED`, which asserts that rational numbers are closed under the arithmetic operations used in the expression.

### Mathematical insight
This theorem establishes a key property: if a well-formed expression does not contain any radicals (such as square roots, cube roots, etc. represented in the formalization), then its value must be a rational number. This is a fundamental result connecting the syntactic structure of expressions to the nature of their numerical values.

### Dependencies
- Definitions: `radicals`, `value`, `wellformed`
- Theorems: `RATIONAL_CLOSED`, `EMPTY_UNION`, `NOT_INSERT_EMPTY`

### Porting notes (optional)
- The main challenge in porting this theorem lies in correctly representing the inductive type of expressions and the associated functions (`radicals`, `value`, `wellformed`). Ensure that these functions are defined in a way that is compatible with the arithmetic operations within your target proof assistant.
- The `expression_INDUCT` tactic in HOL Light performs induction over the expression syntax tree. Other proof assistants will likely have corresponding induction tactics or methods for inductive types. Recreate the induction scheme faithfully.
- The `RATIONAL_CLOSED` theorem is crucial for the final simplification. Ensure that a similar theorem, stating the closure of rational numbers under relevant operations, is available or provable in the target environment.


---

## FINITE_MAX

### Name of formal statement
FINITE_MAX

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_MAX = prove
 (`!s. FINITE s ==> ~(s = {}) ==> ?b:num. b IN s /\ !a. a IN s ==> a <= b`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:num->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; UNWIND_THM2; LE_REFL] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;
```

### Informal statement
For all sets `s` of natural numbers, if `s` is finite and `s` is non-empty, then there exists a natural number `b` such that `b` is in `s` and for all natural numbers `a`, if `a` is in `s`, then `a` is less than or equal to `b`.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `s`.

- Base case: If `s` is empty, the premise `~(s = {})` is false, so the implication holds trivially.

- Inductive step: Assume `FINITE s ==> ~(s = {}) ==> ?b. b IN s /\ !a. a IN s ==> a <= b` holds for all subsets of `s`. We want to show that `FINITE (INSERT x s) ==> ~(INSERT x s = {}) ==> ?b. b IN INSERT x s /\ !a. a IN INSERT x s ==> a <= b`.

    - We consider two cases with `ASM_CASES_TAC`: either `s` is empty or `s` is not empty.
        - If `s` is empty, `INSERT x s` is `{x}` which is not empty. We want to show that there exists a `b` such that `b` is in `{x}` and for all `a` in `{x}`, `a <= b`. We can take `b` to be `x`.
        - If `s` is not empty, we know that `FINITE s` and `~(s = {})`, so by the inductive hypothesis, there exists a `b` such that `b IN s /\ !a. a IN s ==> a <= b`. We must show that there exists a `b'` such that `b' IN INSERT x s /\ !a. a IN INSERT x s ==> a <= b'`. We can take `b'` to be the maximum of `x` and `b`, relying on `LE_CASES` for `x <= b or b <= x`.

### Mathematical insight
This theorem formalizes the intuition that a non-empty finite set of natural numbers has a maximum element. It's a fundamental property used when working with finite sets and is essential in many number-theoretic arguments. The constructive existence of the maximum is proven, not merely its uniqueness.

### Dependencies
- `FINITE`
- `NOT_INSERT_EMPTY`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `LE_REFL`
- `RIGHT_OR_DISTRIB`
- `EXISTS_OR_THM`
- `LE_CASES`
- `LE_TRANS`
- `FINITE_INDUCT_STRONG`

### Porting notes (optional)
The main challenge in porting this to other proof assistants is likely to be replicating the strong induction principle and potentially the automation provided by `MESON_TAC`. Ensure that the finiteness and set membership predicates are suitably defined in the target system. Reconstructing the automated proof search may need some manual intervention or adjustments to the automated tactics available in the target system. The `UNWIND_THM` tactics are custom tactics for unfolding definitions and may require careful handling.


---

## RADICAL_TOP

### Name of formal statement
RADICAL_TOP

### Type of the formal statement
theorem

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
  MESON_TAC[IN_RADICALS_SMALLER; NOT_LT]);;
```

### Informal statement
For any set `e` of sets, if the set of radicals of `e` is non-empty, then there exists an element `r` that is in the radicals of `e` such that for all `s`, if `s` is in the radicals of `e`, then `r` is not in the radicals of `s`.

### Informal sketch
The proof proceeds by induction on the depth of the elements in `radicals e`.

- We assume that `radicals e` is non-empty.
- Consider the image of `depth` applied to `radicals e`. The maximal element under this image implies that one of the radicals `r : radicals e` has minimal depth of its radicals.
- Using the definition of `FINITE_MAX` we may pick an element `r` of `radicals e` such that the `depth` of all its radicals are smaller than `depth r`.
- We assume that for some `s` in `radicals e`, `r` is in `radicals s`.
- Then `depth r < depth s` because `r IN radicals s` and by `IN_RADICALS_SMALLER` we know that `depth r < depth s`.
- However, this contradicts the assumption that `depth s < depth r`. Thus, it cannot be the case that `r IN radicals s`.

### Mathematical insight
This theorem establishes that given a non-empty set of sets `e`, there exists an element within its radicals that is not itself present within the radicals of any other element in `e`. This represents a minimality property within the radical structure.

### Dependencies
- `IMAGE_EQ_EMPTY`
- `FINITE_IMAGE`
- `FINITE_RADICALS`
- `EXISTS_IN_IMAGE`
- `FORALL_IN_IMAGE`
- `IN_RADICALS_SMALLER`
- `NOT_LT`


---

## RADICAL_CANONICAL_TRIVIAL

### Name of formal statement
RADICAL_CANONICAL_TRIVIAL

### Type of the formal statement
theorem

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
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN SET_TAC[]]);;
```

### Informal statement
For all expressions `e` and radicals `r`, if the following two conditions hold:
1. `r` is an element of the set of radicals of `e` implies that there exist expressions `a` and `b` such that `a` is wellformed, `b` is wellformed, the value of `e` is equal to the value of `a` plus the value of `b` times the square root of the value of `r`, the radicals of `a` are a subset of the radicals of `e` excluding `r`, the radicals of `b` are a subset of the radicals of `e` excluding `r`, and the radicals of `r` are a subset of the radicals of `e` excluding `r`,
then it follows that:
if `e` is wellformed, then there exist expressions `a` and `b` such that `a` is wellformed, `b` is wellformed, the value of `e` is equal to the value of `a` plus the value of `b` times the square root of the value of `r`, the radicals of `a` are a subset of the radicals of the union of the radicals of `e` and the radicals of `r` excluding `r`, the radicals of `b` are a subset of the radicals of the union of the radicals of `e` and the radicals of `r` excluding `r`, and the radicals of `r` are a subset of the radicals of the union of the radicals of `e` and the radicals of `r` excluding `r`.

### Informal sketch
The proof proceeds by considering two cases:
- Case 1: `r IN radicals e`
    - Assume `r` is in `radicals e`.
    - Apply the hypothesis (the implication about expressing `e` in terms of `a`, `b`, and `r`) using `ASM_CASES_TAC`.
    - Use `ASM_SIMP_TAC` for simplification.
    - Repeatedly apply `MONO_EXISTS` and generalize to complete the proof in this case.
- Case 2: `~(r IN radicals e)`
    - Assume `r` is not in `radicals e`.
    - Construct expressions `a` and `b` such that `a` is `e` and `b` is `Constant(&0)`.
    - Use `ASM_REWRITE_TAC` to simplify using definitions of `wellformed`, `value`, and `radicals`.
    - Rewrite using `RATIONAL_NUM`, `REAL_MUL_LZERO`, and `REAL_ADD_RID` (real number arithmetic) to show that the value equation holds.
    - Apply `NOT_IN_OWN_RADICALS` and `SET_TAC` to complete the proof.

### Mathematical insight
The theorem states that if an expression `e` can be decomposed with respect to a radical `r` (i.e., expressed as `a + b * sqrt(r)`), then regardless of whether `r` is initially considered to be in the radicals of `e`, we can always find such a decomposition `a + b * sqrt(r)` where the radicals of `a` and `b` are subsets of the radicals of `e` along with `r`, but excluding `r` itself.  In other words, if `r` was *not* initially in the radicals of `e`, we can trivially include it in the decomposition without changing the value of `e`. This justifies treating radical expressions in a canonical way by making it possible to represent the same value in different forms, including forms where all relevant radicals are explicitly present.

### Dependencies
- Definitions:
    - `wellformed`
    - `value`
    - `radicals`
- Theorems:
    - `MONO_EXISTS`
    - `NOT_IN_OWN_RADICALS`
    - `RATIONAL_NUM`
    - `REAL_MUL_LZERO`
    - `REAL_ADD_RID`


---

## RADICAL_CANONICAL

### Name of formal statement
RADICAL_CANONICAL

### Type of the formal statement
theorem

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
    MP_TAC(SPEC `r:expression` NOT_IN_OWN_RADICALS) THEN ASM SET_TAC[]]);;
```
### Informal statement
For every expression `e`, if `e` is well-formed and the set of radicals of `e` is non-empty, then there exists an expression `r` such that `r` is in the set of radicals of `e`, and there exist expressions `a` and `b` such that the expression `Addition a (Multiplication b (Sqrt r))` is well-formed, the value of `e` equals the value of `Addition a (Multiplication b (Sqrt r))`, the set of radicals of `a` is a subset of the set of radicals of `e` with `r` removed, the set of radicals of `b` is a subset of the set of radicals of `e` with `r` removed, and the set of radicals of `r` is a subset of the set of radicals of `e` with `r` removed.

### Informal sketch
The proof proceeds by induction on the structure of expressions:

- The base cases involve constants and variables.
- The inductive steps consider negation, inverse, addition, multiplication, and square root.
- A key step involves selecting a radical `r` from the input expression `e`. In the case that `e` is `Sqrt(r)` the condition `&0 <= value r /\ wellformed r` must be proved.
- The goal is to find expressions `a` and `b` such that `value e = value(Addition a (Multiplication b (Sqrt r)))`. Various algebraic manipulations are performed to determine appropriate expressions for `a` and `b`, depending on the form of the initial expression `e`. For example, special cases must be considered for `value b * sqrt(value r) = value a` and `e1 = &0`.
- The proof uses rewriting with properties of `wellformed`, `value`, and `radicals`, as well as arithmetic reasoning.
- In the cases for addition and multiplication, the induction hypotheses are used to express the component expressions in the required `a + b * sqrt(r)` form, and then these are combined algebraically to represent the whole expression in that form.
- Theorems such as `NOT_IN_OWN_RADICALS` and `RADICALS_SUBSET` are used to establish subset relations between radical sets of the new expressions.

### Mathematical insight
This theorem provides a canonical form for expressions containing radicals. It states that any well-formed expression containing radicals can be rewritten into the form `a + b * sqrt(r)`, where `r` is one of the radicals in the original expression, and `a` and `b` are expressions whose radicals are a subset of the original radicals excluding `r`. This is an important step in simplifying and normalizing expressions, allowing for easier comparison and manipulation.

### Dependencies
- `RADICAL_TOP`
- `MONO_EXISTS`
- `WELLFORMED_RADICALS`
- `RADICALS_WELLFORMED`
- `IMP_IMP`
- `wellformed`
- `value`
- `GSYM CONJ_ASSOC`
- `expression_INDUCT`
- `radicals`
- `NOT_IN_EMPTY`
- `IN_INSERT`
- `IN_UNION`
- `LEFT_IMP_EXISTS_THM`
- `EMPTY_SUBSET`
- `CONJ_ASSOC`
- `UNION_SUBSET`
- `SQRT_POW_2`
- `RADICAL_CANONICAL_TRIVIAL`
- `LEFT_AND_EXISTS_THM`
- `RIGHT_AND_EXISTS_THM`
- `NOT_IN_OWN_RADICALS`
- `RADICALS_SUBSET`
- `RATIONAL_NUM`
### Porting notes (optional)
- The proof relies heavily on rewriting and arithmetic reasoning, so a proof assistant with strong automation in these areas would be beneficial.
- The induction scheme `expression_INDUCT` would need to be re-established based on how expressions are represented in the target proof assistant
- The tactic `ASM_CASES_TAC` may be difficult to directly replicate, and may require a careful decomposition into more basic case splits based on derived equalities.


---

## CUBIC_ROOT_STEP

### Name of formal statement
CUBIC_ROOT_STEP

### Type of the formal statement
theorem

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
  ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;
```

### Informal statement
For all real numbers `a`, `b`, and `c`, if `a`, `b`, and `c` are rational, then for any expression `e` such that `e` is well-formed, the set of radicals in `e` is non-empty, and `(value e)^3 + a * (value e)^2 + b * (value e) + c = 0`, there exists an expression `e'` such that `e'` is well-formed, the set of radicals in `e'` is a proper subset of the set of radicals in `e`, and `(value e')^3 + a * (value e')^2 + b * (value e') + c = 0`.

### Informal sketch
The proof proceeds by:
- Assuming `a`, `b`, and `c` are rational numbers and that `e` is a well-formed expression with a non-empty set of radicals such that `(value e)^3 + a * (value e)^2 + b * (value e) + c = 0`.
- Applying `RADICAL_CANONICAL` to rewrite `e` to a canonical form containing a specific radical `r`.
- Choosing such a radical `r` in `e`.
- Using `STEP_LEMMA_SQRT`, which asserts the existence of an expression `ex` for every real number `x` such that `ex` is well-formed, its radicals are a subset of the radicals of `e` with `r` removed, and its value is `x`.
- Proving that the condition `radicals ex SUBSET (radicals e DELETE r)` is satisfied by constructing expressions for numerical constants, negation, inverse, addition, and multiplication, and showing their radicals are included in  `(radicals e) DELETE r)`.
- Instantiate assumptions of the `STEP_LEMMA_SQRT` with appropriate terms.
- Choosing `e'` to satisfy the conditions by existentially quantifying over the variable `e'`.
- Simplifying and applying set theory.

### Mathematical insight
This theorem is a key step in showing that roots of cubic polynomials can be expressed using radicals. It states that if `e` is an expression (involving radicals) which is a root of a cubic polynomial with rational coefficients, and `e` contains at least one radical, then we can find another expression `e'` that is also a root of the same cubic, but contains strictly fewer radicals. This allows for an inductive argument to eventually find a root expressed without radicals (or with a minimal number of radicals). The overall goal is to decompose the solution into simpler radical expressions.

### Dependencies
- `RADICAL_CANONICAL`
- `STEP_LEMMA_SQRT`
- `wellformed`
- `radicals`
- `value`
- `RATIONAL_NUM`
- `EMPTY_SUBSET`
- `RATIONAL_NUM`
- `UNION_SUBSET`
- `MONO_EXISTS`


---

## CUBIC_ROOT_RADICAL_INDUCT

### Name of formal statement
CUBIC_ROOT_RADICAL_INDUCT

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[]]);;
```
### Informal statement
For all real numbers `a`, `b`, and `c`, if `a`, `b`, and `c` are rational numbers, then for all expressions `e` and natural numbers `n`, if `e` is well-formed, the cardinality of the set of radicals in `e` is `n`, and `(value e)^3 + a*(value e)^2 + b*(value e) + c = 0`, then there exists a rational number `x` such that `x^3 + a*x^2 + b*x + c = 0`.

### Informal sketch
The theorem is proved by induction on the number of radicals `n` in the expression `e`.

- Base case: `radicals e = {}`. This means `e` contains no radicals, hence `value e` is rational. We use the theorem `RADICALS_EMPTY_RATIONAL` and conclude that `value e` satisfies the required cubic equation.
- Inductive step: Assume the theorem holds for `n`. Suppose `CARD (radicals e) = n + 1`. From `CUBIC_ROOT_STEP` we have that there exists an expression `e'` such that `value e = value e'`, `e'` is well-formed and `CARD (radicals e') = n`. Since `(value e)^3 + a*(value e)^2 + b*(value e) + c = 0` and `value e=value e'`, we have `(value e')^3 + a*(value e')^2 + b*(value e') + c = 0`.  We can then apply the inductive hypothesis to `e'` to obtain a rational `x` satisfying the condition. The cardinality shrinks by one, which justifies applying the inductive hypothesis. The proof also involves showing that if `radicals e' ` is a proper subset of `radicals e` and `radicals e` is finite, then  `CARD (radicals e') < CARD (radicals e)`.

### Mathematical insight
The theorem states that a cubic equation with rational coefficients and a solution expressible in terms of radicals has a rational root. The proof uses induction on the number of radicals to show the existence of this rational root.

### Dependencies
- `RADICALS_EMPTY_RATIONAL`
- `CUBIC_ROOT_STEP`
- `CARD_PSUBSET`
- `FINITE_RADICALS`

### Porting notes (optional)
The theorem uses the concept of `radicals` and `expressions` which would need to be defined or imported into another proof assistant. The proof relies on induction over natural numbers, which should be straightforward to port. The `CUBIC_ROOT_STEP` theorem is likely crucial and will need to be available. The handling of real numbers and rational numbers should be standard across most proof assistants, but the definitions might need adaptation.


---

## CUBIC_ROOT_RATIONAL

### Name of formal statement
CUBIC_ROOT_RATIONAL

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[]);;
```
### Informal statement
For all real numbers `a`, `b`, and `c`, if `a`, `b`, and `c` are rational numbers, and there exists a radical expression `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero, then there exists a rational number `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting using `RADICAL_EXPRESSION`.
- Repeatedly strip the goal, applying `STRIP_TAC`.
- Apply `CUBIC_ROOT_RADICAL_INDUCT` after specializing it to `a`, `b`, and `c`, using `MP_TAC`. This likely sets up an inductive argument on the structure of radical expressions.
- Rewrite using assumptions with `ASM_REWRITE_TAC`.
- Discharge the assumption using `DISCH_THEN MATCH_MP_TAC`.
- Apply an existence tactic using `MAP_EVERY EXISTS_TAC` with the cardinality of the radical expressions `CARD(radicals e)` and the expression `e` which likely introduces existential quantifiers based on the induction.
- Finally, solve the goal using `ASM_MESON_TAC`.

### Mathematical insight
The theorem states that if a cubic equation with rational coefficients has a root that can be expressed as a radical expression, then it also has a rational root. This is a statement about the nature of solutions to cubic equations and connects the concepts of radical expressions and rational numbers.

### Dependencies
- Theorem: `CUBIC_ROOT_RADICAL_INDUCT`
- Definition: `RADICAL_EXPRESSION`


---

## CUBIC_ROOT_INTEGER

### Name of formal statement
CUBIC_ROOT_INTEGER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBIC_ROOT_INTEGER = prove
 (`!a b c. integer a /\ integer b /\ integer c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. integer x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RATIONAL) THEN
  ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
  ASM_MESON_TAC[RATIONAL_ROOT_INTEGER]);;
```
### Informal statement
For all real numbers `a`, `b`, and `c`, such that `a`, `b`, and `c` are integers, if there exists a radical number `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero, then there exists an integer `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero.

### Informal sketch
The proof proceeds as follows:
- Specialize the theorem `CUBIC_ROOT_RATIONAL` to `a`, `b`, and `c`. The theorem `CUBIC_ROOT_RATIONAL` states that if there exists a rational `x` satisfying the cubic equation then there exists a rational solution to the same equation when `a`, `b`, `c` are integers.
- Simplify using `RATIONAL_INTEGER`. This step likely uses `RATIONAL_INTEGER` to show that if a number is rational and satisfies the mentioned existential quantifier (`?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0`), it implies the existence of a rational number that satisfies the cubic equation. This step removes the radical condition and relaxes it to being rational.
- Use `ASM_MESON_TAC` with `RATIONAL_ROOT_INTEGER` to conclude the proof. Given that we know that: `a`, `b`, and `c` are integers; there exists a rational number `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero, and that `RATIONAL_ROOT_INTEGER` says that if there is a rational root of such a monic polynomial, then the root is in fact an integer, we can conclude that there exists an integer `x` such that `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals zero.

### Mathematical insight
The theorem asserts that if a monic cubic polynomial with integer coefficients has a radical root, it must have an integer root. This is a specific case of the rational root theorem, specialized to cubic polynomials and extended to radical roots.  The rational root theorem is a standard result in algebra which helps to determine possible rational roots of a polynomial with integer coefficients.

### Dependencies
- `CUBIC_ROOT_RATIONAL`
- `RATIONAL_INTEGER`
- `RATIONAL_ROOT_INTEGER`
---
### Name of formal statement
RATIONAL_LOWEST_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBIC_ROOT_INTEGER = prove
 (`!a b c. integer a /\ integer b /\ integer c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. integer x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RATIONAL) THEN
  ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
  ASM_MESON_TAC[RATIONAL_ROOT_INTEGER]);;
```
### Informal statement
For all numbers `p` and `q`, if `q` is not equal to 0, then there exist numbers `p'` and `q'` such that `q'` is not equal to 0, `p'` and `q'` are coprime, and `p` times `q'` equals `p'` times `q`.

### Informal sketch
The proof shows that any rational number p/q, with q != 0, can be expressed in an equivalent form p'/q' where p' and q' are coprime, and q' != 0.
- Start by rewriting the goal with `SWAP_FORALL_THM` to move the existential quantifiers to the front. Then apply `MATCH_MP_TAC num_WF`.
- Introduce p and q via `X_GEN_TAC`, discharging the assumptions.
- Perform case distinction on whether `p` and `q` are coprime.
  - If `coprime(p, q)` holds, then the existence of `p'` and `q'` are clear, and the proof is completed by a trivial application of the assumption with `ASM_MESON_TAC[]`
  - Otherwise, if `coprime(p, q)` does *not* hold, we rewrite using the definition of coprime via `coprime` and decompose using `NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC`. Then there exists a common divisor `d` such that `d` divides `p` and `d` divides `q` using `X_CHOOSE_THEN`. Perform case distinction on `d = 0`. If it is, we get a contradiction so, `d` must not be zero
  - Introduce `p'` and `q'` as `p/d` and `q/d` respectively. Show that `p'` and `q'` are coprime.
- Simplify using arithmetic facts via `NUM_RING` and complete the proof

### Mathematical insight
This lemma states that any rational number can be expressed in its lowest terms, i.e., as a fraction where the numerator and denominator are coprime. This is a fundamental property of rational numbers.

### Dependencies
- `SWAP_FORALL_THM`
- `coprime`
- `NOT_FORALL_THM`
- `NOT_IMP`
- `GSYM`
- `CONJ_ASSOC`
- `DIVIDES_ZERO`
- `divides`
- `MULT_EQ_0`
- `DE_MORGAN_THM`
- `ARITH_RULE`
- `LT_MULT_RCANCEL`
- `NUM_RING`
- `MONO_EXISTS`
---
### Name of formal statement
RATIONAL_LOWEST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBIC_ROOT_INTEGER = prove
 (`!a b c. integer a /\ integer b /\ integer c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. integer x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RATIONAL) THEN
  ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
  ASM_MESON_TAC[RATIONAL_ROOT_INTEGER]);;
```
### Informal statement
For all `x`, `x` is a rational number if and only if there exist numbers `p` and `q` such that `q` is not equal to 0, `p` and `q` are coprime, and the absolute value of `x` equals `p` divided by `q`.

### Informal sketch
The proof establishes the equivalence between a number being rational and the existence of a coprime representation for its absolute value.
- The proof starts by rewriting with `RATIONAL_ALT`. This likely expands the initial definition of `rational x` to an equivalent form involving the existence of `p` and `q` such that `x = p / q`.
- The proof then utilizes `EQ_TAC` to split the proof into two directions:
  - One direction is done by `ALL_TAC`,
  - The other direction is dispatched with `MESON_TAC[]`.
- In the remaining part of the proof we proceed by `STRIP_TAC` which likely decomposes the goal.
- Then it applies the `RATIONAL_LOWEST_LEMMA`, which guarantees the existence of a coprime representation. The conclusion utilizes `ASM_REWRITE_TAC[]` to rewrite the goal using assumptions.
- Existential variables are introduced gradually using `REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC)`.
- `UNDISCH_TAC` lifts the assumption `~(q = 0)`.
- The proof concludes by rewriting and simplifying using standard arithmetic rules like `GSYM REAL_OF_NUM_EQ`, `GSYM REAL_OF_NUM_MUL`, and `REAL_FIELD`.

### Mathematical insight
This theorem formalizes a crucial property of rational numbers: any rational number can be uniquely represented (up to sign) as a fraction `p/q` where `p` and `q` are coprime. Taking the absolute value ensures uniqueness, since both `p/q` and `-p/q` represent the same rational number in magnitude.

### Dependencies
- `RATIONAL_ALT`
- `RATIONAL_LOWEST_LEMMA`
- `REAL_OF_NUM_EQ`
- `REAL_OF_NUM_MUL`
- `REAL_FIELD`
---
### Name of formal statement
RATIONAL_ROOT_INTEGER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CUBIC_ROOT_INTEGER = prove
 (`!a b c. integer a /\ integer b /\ integer c /\
           (?x. radical x /\ x pow 3 + a * x pow 2 + b * x + c = &0)
           ==> (?x. integer x /\ x pow 3 + a * x pow 2 + b * x + c = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`] CUBIC_ROOT_RATIONAL) THEN
  ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
  ASM_MESON_TAC[RATIONAL_ROOT_INTEGER]);;
```
### Informal statement
For all `a`, `b`, `c`, and `x`, if `a`, `b`, and `c` are integers, `x` is a rational number, and `x` cubed plus `a` times `x` squared plus `b` times `x` plus `c` equals 0, then `x` is an integer.

### Informal sketch
The theorem states that if `x` is a rational root of a monic cubic polynomial with integer coefficients, then `x` must be an integer.

- Rewrite `rational x` using `RATIONAL_LOWEST` to express x as `p/q` where `p` and `q` are coprime and `abs(x) = &p / &q`. Also, convert nums to reals using `GSYM REAL_OF_NUM_EQ`.
- Eliminate all the assumptions via `REPEAT STRIP_TAC`.
- Handle the absolute value by considering both cases, `x = p/q` and `x = -p/q`, using `REAL_ARITH` and `DISJ_CASES_THEN SUBST_ALL_TAC`.
- Use `REAL_FIELD` to simplify the equation `x pow 3 + a * x pow 2 + b * x + c = &0` in terms of `p`, `q`, `a`, `b`, and `c` for both cases. This step involves clearing denominators, and rearranging the equation.
- From this it follows that `q` divides `p pow 3`, using the assumption that `a`, `b`, and `c` are integers as proved by `INTEGER_CLOSED`.
- Since `p` and `q` are coprime, so are `p pow 3` and `q` (using `COPRIME_EXP` and `COPRIME_SYM`).
- Do case analysis on `q = 1`.
  - If `q = 1`, conclude `x` is an integer because `x = p/1 = p`.
  - Otherwise, it is a contradiction using `divides` and `DIVIDES_REFL`.

### Mathematical insight
This theorem is a specific case of the rational root theorem for polynomials with integer coefficients. It is an important result in number theory and algebra as it provides a way to find integer roots of polynomials.

### Dependencies
- `RATIONAL_LOWEST`
- `REAL_OF_NUM_EQ`
- `REAL_ARITH`
- `REAL_FIELD`
- `INTEGER_CLOSED`
- `COPRIME_SYM`
- `COPRIME_EXP`
- `divides`
- `DIVIDES_REFL`


---

## length

### Name of formal statement
length

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let length = new_definition
  `length(a:real^2,b:real^2) = norm(b - a)`;;
```

### Informal statement
The length of the line segment between two points `a` and `b` in the real plane (`real^2`) is defined to be the norm of the vector `b - a`.

### Informal sketch
- The definition `length` is defined directly by the expression `norm(b - a)`. There is no proof involved.
- The norm function is just the standard Euclidean norm.

### Mathematical insight
This definition provides a way to calculate the length of a line segment connecting two points in a 2D Euclidean space. It aligns with the standard geometric understanding of distance, where the length is computed as the magnitude (norm) of the vector representing the displacement between the two points. This definition is fundamental in geometry and provides a basis for further reasoning about distances and geometric properties.

### Dependencies
- `norm`


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
        (a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)`;;
```

### Informal statement
The line through points `a` and `b` is parallel to the line through points `c` and `d` if and only if `(a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)`, where `$1` and `$2` denote the first and second coordinates of a point in `real^2`, respectively.

### Informal sketch
The definition introduces the concept of parallelism between two lines defined by pairs of points in the Euclidean plane. The condition `(a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)` is equivalent to saying that the slopes `(a$2 - b$2) / (a$1 - b$1)` and `(c$2 - d$2) / (c$1 - d$1)` are equal, which is the standard condition for parallelism. Note that the condition also handles the cases where one or both of the lines are vertical (i.e. the denominator `(a$1 - b$1)` or `(c$1 - d$1)` is zero).

### Mathematical insight
This definition captures the standard geometric notion of parallel lines in the Euclidean plane using an algebraic condition. The condition avoids explicit division, making it more suitable for formal reasoning in settings where handling division by zero is cumbersome. The definition supports reasoning about relationships between lines given by pairs of points.

### Dependencies
None

### Porting notes (optional)
This definition should be straightforward to port to other proof assistants. The main challenge is ensuring that the notation for accessing the coordinates of a point is properly defined and handled. The underlying arithmetic operations on real numbers must also be correctly defined.


---

## collinear3

### Name of formal statement
- collinear3

### Type of the formal statement
- new_definition

### Formal Content
- The full HOL Light statement will be inserted here **after generation**.
```ocaml
let collinear3 = new_definition
  `collinear3 (a:real^2) b c <=> parallel (a,b) (a,c)`;;
```

### Informal statement
- For any points `a`, `b`, and `c` in the real plane (`real^2`), `collinear3 a b c` is defined to be true if and only if the line through `a` and `b` is parallel to the line through `a` and `c`.

### Informal sketch
- The definition introduces the predicate `collinear3` to characterize when three points are collinear.
- The collinearity of points `a`, `b`, and `c` is defined in terms of the `parallel` predicate applied to the lines defined by `(a, b)` and `(a, c)`.
- The definition directly links a geometric concept (`collinear3`) to a previously defined notion of `parallel`.

### Mathematical insight
- This definition provides a formal way to reason about collinearity within the HOL Light system. It leverages the existing definition of `parallel` lines, which is likely defined in terms of vectors and scalar multiples. The predicate `collinear3` is fundamental in geometry, allowing formal statements and proofs about arrangements of points in the plane.

### Dependencies
- Definitions:
    - `parallel`


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
The predicate `is_intersection p (a, b) (c, d)` holds if and only if the point `p` is collinear with the points `a` and `b`, and `p` is collinear with the points `c` and `d`.

### Informal sketch
The definition `is_intersection` is defined directly using the `collinear3` predicate. There is nothing to prove; it simply introduces a shorthand for the specified condition.

### Mathematical insight
The `is_intersection` predicate checks if a point lies on two lines defined by pairs of points. Specifically, it checks if the given point lies on the line defined by points `a` and `b`, and also lies on the line defined by points `c` and `d`, using the `collinear3` predicate to verify collinearity in each case.

### Dependencies
- Definitions: `collinear3`


---

## on_circle

### Name of formal statement
`on_circle`

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let on_circle = new_definition
 `on_circle x (centre,pt) <=> length(centre,x) = length(centre,pt)`;;
```
### Informal statement
For any point `x` and any pair `(centre, pt)`, `on_circle x (centre, pt)` is true if and only if the length of the line segment from `centre` to `x` is equal to the length of the line segment from `centre` to `pt`.

### Informal sketch
The definition introduces a predicate `on_circle` that determines whether a point lies on a circle.
- Given a point `x` and a circle defined by its center `centre` and a point `pt` on its circumference, `x` lies on the circle if and only if the distance from `centre` to `x` is equal to the distance from `centre` to `pt`.
- This definition directly formalizes the geometric concept of a point lying on a circle.

### Mathematical insight
This definition formalizes the geometric notion of a point lying on a circle in terms of distances. Given a circle defined by its center and a point on the circle, a point lies on the circle if and only if its distance to the center equals the distance of the given point on the circle to the center (i.e., the radius). This definition is a standard way to represent circles in a formal system using distances.

### Dependencies
- Definition: `length`


---

## SQRT_CASES_LEMMA

### Name of formal statement
SQRT_CASES_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SQRT_CASES_LEMMA = prove
 (`!x y. y pow 2 = x ==> &0 <= x /\ (sqrt(x) = y \/ sqrt(x) = --y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
  MP_TAC(SPEC `y:real` (GEN_ALL POW_2_SQRT)) THEN
  MP_TAC(SPEC `--y` (GEN_ALL POW_2_SQRT)) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers `x` and `y`, if `y` raised to the power of 2 is equal to `x`, then `0` is less than or equal to `x`, and either the square root of `x` is equal to `y` or the square root of `x` is equal to the negation of `y`.

### Informal sketch
The proof proceeds as follows:
- Assume `y pow 2 = x`.
- Rewrite using `REAL_POW_2` and `REAL_LE_SQUARE` to show that `0 <= x`.
- Instantiate the theorem `POW_2_SQRT` with `y` to obtain `y pow 2 = (sqrt (y pow 2)) pow 2 \/ y pow 2 = (-- (sqrt (y pow 2))) pow 2`.
- Instantiate the theorem `POW_2_SQRT` with `--y` to obtain `(--y) pow 2 = (sqrt ((--y) pow 2)) pow 2 \/ (--y) pow 2 = (-- (sqrt ((--y) pow 2))) pow 2`.
- Rewrite with `REAL_POW_NEG` to obtain `(--y) pow 2 = (sqrt ((--y) pow 2)) pow 2 \/ (--y) pow 2 = (-- (sqrt ((--y) pow 2))) pow 2`.
- Simplify using arithmetic to show that `sqrt(x) = y \/ sqrt(x) = --y`.
- Use real arithmetic reasoning to complete the proof.

### Mathematical insight
This lemma states a fundamental property of the square root function. Namely, if `y^2 = x`, then `sqrt(x)` must be either `y` or `-y`. Note that `x` must be non-negative for `sqrt(x)` to be defined in the reals.

### Dependencies
- `REAL_POW_2`
- `REAL_LE_SQUARE`
- `POW_2_SQRT`
- `REAL_POW_NEG`
- `ARITH`
- `REAL_ARITH_TAC`


---

## RADICAL_LINEAR_EQUATION

### Name of formal statement
RADICAL_LINEAR_EQUATION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RADICAL_LINEAR_EQUATION = prove
 (`!a b x. radical a /\ radical b /\ ~(a = &0 /\ b = &0) /\ a * x + b = &0
           ==> radical x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(a = &0) /\ x = --b / a`
   (fun th -> ASM_SIMP_TAC[th; RADICAL_RULES]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;
```
### Informal statement
For all real numbers `a`, `b`, and `x`, if `a` and `b` are radical, `a` and `b` are not both zero, and `a * x + b = 0`, then `x` is radical.

### Informal sketch
The proof proceeds by showing that under the assumption `~(a = &0 /\ b = &0)`, if `a*x + b = &0`, then `~(a = &0) /\ x = --b / a`. This is then used along with the radical rules (likely defining which numbers are radical) to show that `x` must be radical. The proof employs the following steps:

- Assume `radical a`, `radical b`, `~(a = &0 /\ b = &0)` and `a * x + b = &0`.
- Introduce the subgoal `~(a = &0) /\ x = --b / a`.
- Simplify using assumptions and `RADICAL_RULES` to prove this subgoal.
- Discharge the subgoal using assumption introduction and modus ponens, effectively using the simplified form of `x` to prove `radical x`.
- Apply real field tactics (`REAL_FIELD`) to complete the proof using real arithmetic.

### Mathematical insight
This theorem shows that solutions to linear equations with radical coefficients are themselves radical, given that the coefficients are not both zero. This can be viewed as closure property regarding radical numbers. Equations of this form are very basic, so this theorem shows rudimentary closure of operations definining "radical" numbers.

### Dependencies
- Definitions: `radical`
- Theorems: `RADICAL_RULES`


---

## RADICAL_SIMULTANEOUS_LINEAR_EQUATION

### Name of formal statement
RADICAL_SIMULTANEOUS_LINEAR_EQUATION

### Type of the formal statement
theorem

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
    ASM_SIMP_TAC[RADICAL_RULES]]);;
```

### Informal statement
For all real numbers `a`, `b`, `c`, `d`, `e`, `f`, and `x`, if `a`, `b`, `c`, `d`, `e`, and `f` are radicals and it is not the case that `a * e = b * d` and `a * f = c * d` and `e * c = b * f`, and `a * x + b * y = c` and `d * x + e * y = f`, then `x` and `y` are radicals.

### Informal sketch
The proof proceeds by first assuming the hypotheses of the theorem and simplifying. The goal is to show `radical(x)` and `radical(y)`. The next step introduces the condition that `~(a * e - b * d = &0)` and the explicit solutions for `x` and `y` given by `x = (e * c - b * f) / (a * e - b * d)` and `y = (a * f - d * c) / (a * e - b * d)`. The proof then uses real field simplification and the radical rules (`RADICAL_RULES`) to derive `radical(x)` and `radical(y)`.

### Mathematical insight
This theorem shows that under certain conditions (specifically that the coefficients `a`, `b`, `c`, `d`, `e`, `f` are radical numbers, and a non-degeneracy condition on the coefficients to ensure a unique solution exists), if a system of two linear equations with two unknowns (`x` and `y`) has radical coefficients and constants, then the solutions `x` and `y` are also radical numbers. The non-degeneracy condition `~(a * e = b * d /\ a * f = c * d /\ e * c = b * f)` ensures the system has a unique solution and prevents indeterminate cases, and it is reformulated to `~(a * e - b * d = &0)` for use in the proof.

### Dependencies
- `RADICAL_RULES`


---

## RADICAL_QUADRATIC_EQUATION

### Name of formal statement
RADICAL_QUADRATIC_EQUATION

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[] THEN RADICAL_TAC THEN ASM_REWRITE_TAC[]]);;
```

### Informal statement
For all real numbers `a`, `b`, `c`, and `x`, if `a`, `b`, and `c` are radical (i.e., can be expressed using integers and nth roots), and `a * x^2 + b * x + c = 0`, and it is not the case that `a = 0` and `b = 0` and `c = 0`, then `x` is radical.

### Informal sketch
The proof proceeds by:
- Case splitting on whether `a = 0`.
  - If `a = 0`, then the equation reduces to a linear equation `b * x + c = 0`. The proof then relies on the theorem `RADICAL_LINEAR_EQUATION`, that states "if b and c are radical and b*x+c=0, then x is radical"
  - If `a != 0`, then we use the quadratic formula.
    - The main step involves showing that `0 <= b^2 - 4 * a * c` and that either `2 * a * x + (b - sqrt(b^2 - 4 * a * c)) = 0` or `2 * a * x + (b + sqrt(b^2 - 4 * a * c)) = 0`.
    - Use the assumption `a * x^2 + b * x + c = 0` along with algebraic manipulation and `SQRT_CASES_LEMMA` to prove the above claim.
    - The goal state is simplified by introducing witnesses `b - sqrt(b pow 2 - &4 * a * c)` and `b + sqrt(b pow 2 - &4 * a * c)`.
    - The proof then relies on the `RADICAL_TAC` tactic to show that if the square root is radical and the coefficients are radical, then the root is radical.

### Mathematical insight
This theorem captures a fundamental property of radical numbers: the roots of a quadratic equation with radical coefficients are themselves radical. It demonstrates that the set of radical numbers is closed under solving quadratic equations.

### Dependencies
- `RADICAL_LINEAR_EQUATION`
- `RADICAL_RULES`
- `REAL_ENTIRE`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `SQRT_CASES_LEMMA`
- `real_sub`
- `REAL_ARITH`
- `REAL_EQ_NEG2`

### Porting notes (optional)
- The `RADICAL_TAC` tactic encapsulates a significant component of the reasoning about radical numbers. It might be necessary to replicate its functionality in the target proof assistant.
- The proof relies heavily on real number arithmetic (`REAL_ARITH`, `REAL_RING`), which should be available or easily definable in most proof assistants.


---

## RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC

### Name of formal statement
RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC

### Type of the formal statement
theorem

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
   CONV_TAC REAL_RING));;
```
### Informal statement
For all real numbers `a`, `b`, `c`, `d`, `e`, `f`, and `x`, if `a`, `b`, `c`, `d`, `e`, and `f` are radical, and it is not the case that `d = 0`, `e = 0`, and `f = 0`, and `(x - a)^2 + (y - b)^2 = c` and `d * x + e * y = f`, then `x` and `y` are radical.

### Informal sketch

The proof proceeds by:
- Substituting `x` from the linear equation `d * x + e * y = f` into the quadratic equation `(x - a)^2 + (y - b)^2 = c`. This will result in a quadratic equation in `y`.
- Then, the theorem `RADICAL_QUADRATIC_EQUATION` is used to show that the solution `y` is radical.
- A similar argument is constructed for showing that `x` is radical.
- The appropriate values for arguments of the invoked theorems are derived by equational reasoning, algebraic manipulation and rewriting using theorems for real numbers `REAL_RING` and `REAL_SOS_EQ_0`.
- The tactic `REPEAT STRIP_TAC` removes the top-level structure of the goal.
- `MP_TAC` instantiates the variables of the theorem `RADICAL_QUADRATIC_EQUATION` and then applies it as a modus ponens inference
- `EXISTS_TAC` introduces witnesses that give specific forms for the parameters.
- `RADICAL_TAC` proves that a number is radical and `ASM_REWRITE_TAC` rewrites the assumptions.

### Mathematical insight
This theorem provides the condition where the variables in a simultaneous linear and quadratic equation system will have radical number solutions. The condition that `d`, `e`, and `f` are not all simultaneously equal to zero ensures that the linear equation is non-trivial. The predicate `radical` means the number is constructible, by using only a compass and straightedge.

### Dependencies
- `RADICAL_QUADRATIC_EQUATION`
- `RADICAL_TAC`
- `REAL_RING`
- `REAL_SOS_EQ_0`


---

## RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC

### Name of formal statement
RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC

### Type of the formal statement
theorem

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
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;
```

### Informal statement
For all real numbers `a`, `b`, `c`, `d`, `e`, `f`, `x`, and `y`, if `a`, `b`, `c`, `d`, `e`, and `f` are radical numbers, and it is not the case that `a = d`, `b = e`, and `c = f` all hold simultaneously, and `(x - a)^2 + (y - b)^2 = c` and `(x - d)^2 + (y - e)^2 = f`, then `x` and `y` are radical numbers.

### Informal sketch
The proof demonstrates that if two circles with radical parameters intersect, their intersection points also have radical coordinates. The proof proceeds as follows:

- Assume all radicals, the inequality, and the two circle equations.
- Apply the theorem `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`. To do this, transform the system of two quadratic equations into a system of a linear equation and a quadratic equation. This is done by subtracting the two equations from each other, which eliminates the quadratic terms in `x` and `y`, yielding a linear equation.
- Introduce existential variables using `EXISTS_TAC` to match the assumption required for `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`. Specifically, existentially quantify `a`, `b`, `c`, `2 * (d - a)`, `2 * (e - b)`, and `(d^2 - a^2) + (e^2 - b^2) + (c - f)`.
- Simplify using assumptions with `ASM_REWRITE_TAC`.
- Repeatedly separate conjunctions, prove radical-ness for each component using the `RADICAL_TAC`, simplifies assumptions by rewriting, and solves other trivial goals.
- Repeatedly deduce by modus ponens using assumptions with `POP_ASSUM MP_TAC`.
- Apply the ring tactic `REAL_RING` to clear out the remaining goal.

### Mathematical insight
This theorem shows that the intersection points of two circles whose parameters are radical numbers are also radical numbers. This is a significant result in geometry and demonstrates the closure properties of radical numbers under certain geometric constructions. The condition `~(a = d /\ b = e /\ c = f)` ensures that the two circles are not the same, otherwise there would not be a unique intersection point.

### Dependencies
- `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`
- `RADICAL_TAC`
- `REAL_RING`

### Porting notes (optional)
- The theorem `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC` will need to be ported first.
- The `RADICAL_TAC` tactic encapsulates the properties needed to establish that a number is radical, which can be rebuilt in different proof assistants by using those properties.
- The `REAL_RING` is a decision procedure for real-number ring equalities, and can typically be replaced by semiring or ring decision procedures built-in in other assistants, or by calling an external solver.


---

## constructible_RULES,constructible_INDUCT,constructible_CASES

### Name of formal statement
`constructible_RULES`,`constructible_INDUCT`,`constructible_CASES`

### Type of the formal statement
`new_inductive_definition`

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
                   ==> constructible x)`;;
```
### Informal statement
The predicate `constructible` on real number pairs (points in the plane) is inductively defined as follows:
1. If the x and y coordinates of a point are both rational numbers, then the point is `constructible`.
2. If points `a`, `b`, `c`, and `d` are `constructible` and the line through `a` and `b` is not parallel to the line through `c` and `d`, and `x` is the intersection of the line through `a` and `b` and the line through `c` and `d`, then `x` is `constructible`.
3. If points `a`, `b`, `c`, `d`, and `e` are `constructible`, `a` is not equal to `b`, `a`, `x`, and `b` are collinear, and the distance between `c` and `x` is equal to the distance between `d` and `e`, then `x` is `constructible`.
4. If points `a`, `b`, `c`, `d`, `e`, and `f` are `constructible`, `a = d` implies that the distance between `b` and `c` is not equal to the distance between `e` and `f`, the distance between `a` and `x` is equal to the distance between `b` and `c`, and the distance between `d` and `x` is equal to the distance between `e` and `f`, then `x` is `constructible`.

### Informal sketch
This is an inductive definition of the `constructible` points in the plane, based on classical geometric constructions with ruler and compass.
- The base case states that any point with rational coordinates is constructible.
- The inductive cases correspond to the three classical construction steps:
    - Intersection of two lines.
    - Intersection of a line and a circle.
    - Intersection of two circles.
The conditions attached to each rule ensure geometric validity (e.g., lines are not parallel, circles and lines/circles actually intersect).

The definition simultaneously defines `constructible_RULES` (the list of inference rules), `constructible_INDUCT` (the induction principle for `constructible`), and `constructible_CASES` (the case analysis principle for `constructible`).

### Mathematical insight
This inductive definition provides a rigorous, analytic characterization of geometric constructibility. It's a cornerstone in connecting algebraic properties (rational coordinates) with geometric constructions. It formalizes the classical notion of what points can be constructed using a compass and straightedge, starting from an initial set of points. This definition is important because it allows us to prove formally which geometric constructions are possible, and which are not (e.g., squaring the circle, trisecting an angle).

### Dependencies
- `rational`
- `parallel`
- `is_intersection`
- `collinear3`
- `length`


---

## RADICAL_LINE_LINE_INTERSECTION

### Name of formal statement
RADICAL_LINE_LINE_INTERSECTION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RADICAL_LINE_LINE_INTERSECTION = prove
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
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;
```

### Informal statement
Given points `a`, `b`, `c`, `d`, and `x` in the real plane (`real^2`), if `a`, `b`, `c`, and `d` all satisfy the `radical` predicate (meaning their coordinates are real numbers), and it is not the case that the line defined by `a` and `b` is parallel to the line defined by `c` and `d`, and `x` is the intersection of the lines defined by `a` and `b` and `c` and `d`, then `x` also satisfies the `radical` predicate.

### Informal sketch
The proof proceeds as follows:
- Rewrite the statement using the definitions of `parallel` and `is_intersection` in terms of collinearity.
- Instantiate the theorem `RADICAL_SIMULTANEOUS_LINEAR_EQUATION` which solves simultaneous linear equations while preserving `radical`. This theorem requires the appropriate existential instantiations.
- Provide the explicit terms `(b:real^2)$2 - (a:real^2)$2`, `(a:real^2)$1 - (b:real^2)$1`, `(a:real^2)$2 * (a$1 - (b:real^2)$1) - (a:real^2)$1 * (a$2 - b$2)`, `(d:real^2)$2 - (c:real^2)$2`, `(c:real^2)$1 - (d:real^2)$1`, `(c:real^2)$2 * (c$1 - (d:real^2)$1) - (c:real^2)$1 * (c$2 - d$2)` as witnesses for the existentially quantified variables in the instantiated version of `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`.
- Verify that the provided instances satisfy the assumptions of `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`, discharging the goals by using the assumption that `a`, `b`, `c`, and `d` satisfy the radical predicate and by simplification.
- Apply real ring conversions to complete the proof.

### Mathematical insight
This theorem establishes that if two lines defined by points with real coordinates intersect, then their point of intersection also has real coordinates, given that the lines are not parallel. It leverages the fact that solving systems of linear equations with real coefficients yields real solutions. The `radical` predicate formally constrains coordinates to the real numbers.

### Dependencies
- Definitions: `parallel`, `collinear3`, `is_intersection`
- Theorems: `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`, `RADICAL_TAC`


---

## RADICAL_LINE_CIRCLE_INTERSECTION

### Name of formal statement
RADICAL_LINE_CIRCLE_INTERSECTION

### Type of the formal statement
theorem

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
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;
```

### Informal statement
Given points `a`, `b`, `c`, `d`, `e`, and `x` in a 2-dimensional real vector space, if:
- `x` lies on the radical line of two circles whose centers are determined according to the predicate `radical` and indexed by 1 and 2, respectively (also for points `a`, `b`, `c`, `d`, `e`).
- `a` is not equal to `b`.
- `a`, `x`, and `b` are collinear.
- The distance between `c` and `x` equals the distance between `d` and `e`.

Then, `x` also lies on the radical line of the two circles defined by the predicate `radical` and indexed by 1 and 2, respectively.

### Informal sketch
The proof proceeds as follows:
- Assume the hypotheses:  `radical(a$1)`, `radical(a$2)`, `radical(b$1)`, `radical(b$2)`, `radical(c$1)`, `radical(c$2)`, `radical(d$1)`, `radical(d$2)`, `radical(e$1)`, `radical(e$2)`, `~(a = b)`, `collinear3 a x b`, and `length(c,x) = length(d,e)`.
- Rewrite using the definitions of `length`, `NORM_EQ`, `collinear3`, and `parallel`.
- Simplify using `CART_EQ`, `FORALL_2`, `dot`, `SUM_2`, `DIMINDEX_2`, `VECTOR_SUB_COMPONENT`, and `GSYM REAL_POW_2`.
- Use `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC` lemma to establish relationships between radicals over simultaneous equations.
- Instantiate existential quantifiers with specific terms involving the components of the points `c`, `d`, `e`, `a`, and `b`.
- Apply `RADICAL_TAC` and assumption rewriting repeatedly to eliminate many terms.
- Use real ring simplification to complete the proof.

### Mathematical insight
This theorem states that if a point `x` lies on the radical line of two circles and satisfies some additional geometric conditions related to collinearity and distances, then it also lies on the radical line of another pair of circles determined by the predicate radical. Essentially, this provides a way to prove that a point lies on a radical line given sufficient geometric constraints. The length constraint acts like another simultaneous equation.

### Dependencies
- Definitions: `length`, `collinear3`, `parallel`, `dot`, `NORM_EQ`, `CART_EQ`, `FORALL_2`, `SUM_2`, `DIMINDEX_2`, `VECTOR_SUB_COMPONENT`.
- Theorems: `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`

### Porting notes (optional)
- The tactic `RADICAL_TAC` encapsulates a specific method for dealing with the radical condition, which may require custom implementation in other proof assistants. The `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC` lemma is also important and may need to be proven independently.
- The `REAL_RING` conversion tactic is heavily used for simplification; other proof assistants will need a comparable facility for real-field reasoning.


---

## RADICAL_CIRCLE_CIRCLE_INTERSECTION

### Name of formal statement
RADICAL_CIRCLE_CIRCLE_INTERSECTION

### Type of the formal statement
theorem

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
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING);;
```
### Informal statement
For all points `a`, `b`, `c`, `d`, `e`, `f`, and `x` in the 2-dimensional real vector space, if `a`, `b`, `c`, `d`, `e`, and `f` are all radical points (lie on the radical axis between two circles), and the distance between `a` and `x` is equal to the distance between `b` and `c`, and the distance between `d` and `x` is equal to the distance between `e` and `f`, and it is not the case that `a` is equal to `d` and the distance between `b` and `c` equals the distance between `e` and `f`, then `x` is a radical point.

### Informal sketch
The theorem states that if distances `length(a,x)` and `length(d,x)` are constrained via `length(b,c)` and `length(e,f)` respectively, and `a,b,c,d,e,f` are radical points, then `x` must be a radical point.

- The proof starts by rewriting using definitions of `length`, `NORM_EQ`, `collinear3`, and `parallel`.
- Then, it simplifies the expression involving `CART_EQ`, `FORALL_2`, `dot`, `SUM_2`, `DIMINDEX_2`, `VECTOR_SUB_COMPONENT`, and `GSYM REAL_POW_2`.
- The main proof step is an invocation of `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`, which likely embodies the core geometric argument.
- Existential variables for the components of `a`, `d` and squares of `length(b,c)` and `length(e,f)` are introduced using `EXISTS_TAC`.
- The goal and assumptions are manipulated with repeated application of `RADICAL_TAC` and `ASM_REWRITE_TAC`.
- The proof concludes with real field simplification using `REAL_RING`.

### Mathematical insight
This theorem relates the geometrical constraints on points defined by equality of distances (`length`) with the property of being a radical point. The condition `~(a = d /\ length(b,c) = length(e,f))` suggests that `a` and `d` and `length(b,c)` and `length(e,f)` cannot be same, thus, `x` is uniquely determined. This suggests that the point `x` is uniquely determined by the intersection of radicals.

### Dependencies
#### Theorems
- `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`

#### Definitions
- `length`
- `NORM_EQ`
- `collinear3`
- `parallel`
- `CART_EQ`
- `FORALL_2`
- `dot`
- `SUM_2`
- `DIMINDEX_2`
- `VECTOR_SUB_COMPONENT`
- `REAL_POW_2`
- `radical`

### Porting notes (optional)
The main challenge in porting this theorem probably lies in recreating `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`, which likely encapsulates the algebraic core of the argument. The other dependencies should be straightforward to port.


---

## CONSTRUCTIBLE_RADICAL

### Name of formal statement
CONSTRUCTIBLE_RADICAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONSTRUCTIBLE_RADICAL = prove
 (`!x. constructible x ==> radical(x$1) /\ radical(x$2)`,
  MATCH_MP_TAC constructible_INDUCT THEN REPEAT CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[RADICAL_RULES];
    MATCH_MP_TAC RADICAL_LINE_LINE_INTERSECTION THEN ASM_MESON_TAC[];
    MATCH_MP_TAC RADICAL_LINE_CIRCLE_INTERSECTION THEN ASM_MESON_TAC[];
    MATCH_MP_TAC RADICAL_CIRCLE_CIRCLE_INTERSECTION THEN ASM_MESON_TAC[]]);;
```
### Informal statement
For every point `x` in the Euclidean plane, if `x` is constructible, then both its x-coordinate (`x$1`) and y-coordinate (`x$2`) are radical numbers.

### Informal sketch
The proof proceeds by induction (`constructible_INDUCT`) on the definition of `constructible` points. The base cases and inductive steps need to show that the coordinates of the new points are radical numbers, assuming the coordinates of the existing points are radical.

- Base Case: Points (0,0) and (1,0) are constructible and have radical coordinates. This trivial case is handeled by simplification with `RADICAL_RULES`
- Inductive Steps: We have to demonstrate that intersections of lines and circles give radical coordinates.
  - Line-Line Intersection: If the coordinates of two points defining two lines are radical, their intersection has again radical coordinates. This is proved using `RADICAL_LINE_LINE_INTERSECTION`.
  - Line-Circle Intersection: If the line is defined by points with radical coordinates and the circle is also defined by points with radical coordinates, the intersection points have radical coordinates (proved by `RADICAL_LINE_CIRCLE_INTERSECTION`).
  - Circle-Circle Intersection: If two circles are defined by points with radical coordinates, their intersection points have radical coordinates (proved by `RADICAL_CIRCLE_CIRCLE_INTERSECTION`).

### Mathematical insight
This theorem demonstrates a key property of constructible numbers: they are a subset of radical numbers. A real number is radical if it can be obtained from the integers by finitely many additions, subtractions, multiplications, divisions, and taking square roots. The theorem implies that geometrical constructibility is limited to algebraic numbers that can be expressed using square roots.

### Dependencies
- `constructible`
- `radical`
- `RADICAL_RULES`
- `RADICAL_LINE_LINE_INTERSECTION`
- `RADICAL_LINE_CIRCLE_INTERSECTION`
- `RADICAL_CIRCLE_CIRCLE_INTERSECTION`
- `constructible_INDUCT`


---

## DOUBLE_THE_CUBE_ALGEBRA

### Name of formal statement
DOUBLE_THE_CUBE_ALGEBRA

### Type of the formal statement
theorem

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
  REWRITE_TAC[num_CONV `3`; EXP_MONO_LE; NOT_SUC] THEN ARITH_TAC);;
```

### Informal statement
It is not the case that there exists a real number `x` such that `x` is constructible (radical) and `x` cubed equals 2.

### Informal sketch
The proof proceeds by contradiction:
- Assume that there exists a constructible number `x` such that `x` cubed equals 2.
- Instantiate the existence of `x` with the cube root of 2.
- Simplify using properties of integers, and rewriting rules for arithmetic operations involving zero.
- Split the goal into two subgoals; the first is discharged using `ASM_MESON_TAC`; the second is solved trivially by `ALL_TAC`.
- Eliminate assumptions using `POP_ASSUM_LIST`.
- Clear the assumption using `STRIP_TAC`
- Apply the absolute value function to `x`.
- Rewrite using the property that the absolute value of a number raised to a power is equal to the absolute value of the number, raised to that power.
- Perform case split of the hypothesis, utilizing the fact that `integer` implies `real_of_num` where `n` is the underlying natural number.
- Rewrite using properties of `real_of_num` and exponentiation to reduce the problem to arithmetic on natural numbers.
- Use an arithmetic rule to show that `n^3 <= 1^3` or `2^3 <= n^3` implies that `n^3 != 2`.
- Simplify using rules of arithmetic (`3`) and monotonicity of exponentiation and properties of the successor function.
- Solve the remaining goal using an arithmetic tactic.

### Mathematical insight
The theorem formalizes the geometric impossibility of doubling the cube using only a compass and straightedge. This is a classic problem in Greek geometry, and this theorem demonstrates that no algebraic number that can be expressed using square roots over the rationals yields `x^3 = 2`.

### Dependencies
- `INTEGER_CLOSED`
- `NOT_IMP`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `GSYM real_sub`
- `REAL_SUB_0`
- `REAL_ABS_POW`
- `integer`
- `REAL_ABS_NUM`
- `REAL_OF_NUM_POW`
- `REAL_OF_NUM_EQ`
- `EXP_MONO_LE`
- `NOT_SUC`
- `CUBIC_ROOT_INTEGER`

### Porting notes (optional)
The `RADICAL` predicate may need to be defined in the target proof assistant, capturing the notion of constructible numbers. The proof relies heavily on arithmetic and algebraic simplification.


---

## DOUBLE_THE_CUBE

### Name of formal statement
DOUBLE_THE_CUBE

### Type of the formal statement
theorem

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
For all x, if x cubed equals 2, then x is not constructible.

### Informal sketch
The proof proceeds as follows:
- Assume `x pow 3 = &2`.
- Assume, for contradiction, that `constructible(vector[x; &0])` holds.
- Apply `CONSTRUCTIBLE_RADICAL` to deduce that x can be obtained by a finite sequence of square roots starting from the rationals.
- Use `VECTOR_2` and `RADICAL_RULES` to simplify the hypothesis `constructible(vector[x; &0])` based on the properties of constructing field extensions by square roots in `RADICAL_RULES` and the definition of vector.
- Apply `DOUBLE_THE_CUBE_ALGEBRA` which is a previously proven algebraic result (likely involving field extensions and degrees) to derive a contradiction and complete the proof. The tactic `ASM_MESON_TAC` is used to automatically discharge the proof, using classical reasoning and any assumptions generated or already present.

### Mathematical insight
This theorem demonstrates that the cube root of 2 is not a constructible number. In geometric terms, this means it is impossible to construct a line segment whose length is the cube root of 2 using only a compass and straightedge, starting from a given unit length. This impossibility is a classical result in field theory and is related to the fact that adjoining the cube root of 2 to the rational numbers creates a field extension of degree 3, which is not a power of 2. Constructible numbers are those that lie in field extensions of degree a power of 2 over the rationals.

### Dependencies
- Theorem: `CONSTRUCTIBLE_RADICAL`
- Theorem: `DOUBLE_THE_CUBE_ALGEBRA`
- Theorem: `RADICAL_RULES`
- Theorem: `VECTOR_2`


---

## COS_TRIPLE

### Name of formal statement
COS_TRIPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COS_TRIPLE = prove
 (`!x. cos(&3 * x) = &4 * cos(x) pow 3 - &3 * cos(x)`,
  GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&3 * x = x + x + x`; SIN_ADD; COS_ADD] THEN
  MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN CONV_TAC REAL_RING);;
```
### Informal statement
For all real numbers `x`, `cos(3 * x) = 4 * cos(x)^3 - 3 * cos(x)`.

### Informal sketch
The proof proceeds by:
- Expanding `cos(3 * x)` as `cos(x + x + x)`.  This is achieved using the rewrite tactic with the arithmetic equality `&3 * x = x + x + x`.
- Applying trigonometric identities for the cosine and sine of sums, specifically `SIN_ADD` and `COS_ADD`, to expand `cos(x + x + x)` into an expression involving `cos(x)` and `sin(x)`.
- Using the trigonometric identity `sin(x)^2 + cos(x)^2 = 1` (invoked with `MP_TAC(SPEC \`x:real\` SIN_CIRCLE)`) to eliminate the `sin(x)` terms.
- Simplifying the resulting expression using real number ring properties, via the `REAL_RING` conversion.

### Mathematical insight
This theorem expresses `cos(3x)` in terms of `cos(x)`. This identity is crucial in understanding the solutions to cubic equations and the impossibility of trisecting angles using only a compass and straightedge.

### Dependencies
- Theorems:
  - `SIN_ADD`
  - `COS_ADD`
  - `SIN_CIRCLE`
- Definitions:
  - `cos`
  - `sin`
- Conversions:
  - `REAL_RING`
- Tactics:
  - `REAL_ARITH`


---

## COS_PI3

### Name of formal statement
COS_PI3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COS_PI3 = prove
 (`cos(pi / &3) = &1 / &2`,
  MP_TAC(SPEC `pi / &3` COS_TRIPLE) THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH; COS_PI] THEN
  REWRITE_TAC[REAL_RING
   `-- &1 = &4 * c pow 3 - &3 * c <=> c = &1 / &2 \/ c = -- &1`] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ACCEPT_TAC MP_TAC) THEN
  MP_TAC(SPEC `pi / &3` COS_POS_PI) THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;
```
### Informal statement
Prove that the cosine of $\pi / 3$ equals $1/2$.

### Informal sketch
The proof proceeds as follows:
- Apply the cosine triple angle formula (`COS_TRIPLE`) to `pi / &3`.
- Perform simplification using `REAL_DIV_LMUL`, `REAL_OF_NUM_EQ`, `ARITH`, and `COS_PI`. This simplifies the expression and substitutes the value of cos(pi).
- Rewrite using the real ring tactic and the algebraic identity `-- &1 = &4 * c pow 3 - &3 * c <=> c = &1 / &2 \/ c = -- &1`,which is used here to find roots of the cubic equation derived from `COS_TRIPLE`.
- Perform a case split, and each case leads to acceptance. The case split is derived from the roots of the equation.
- Apply `COS_POS_PI` to `pi / &3` which returns that `cos(pi / &3)` is positive, then apply that `pi` is positive by `PI_POS`.
- Use real arithmetic to conclude the proof.

### Mathematical insight
The theorem expresses the well-known trigonometric value of the cosine function at $\pi / 3$ (60 degrees). It's a fundamental result in trigonometry and appears frequently in various mathematical contexts. The proof relies on the triple angle formula for cosine and algebraic manipulation to arrive at the result.

### Dependencies
- Theorems: `COS_TRIPLE`, `COS_POS_PI`, `PI_POS`
- Definitions: `REAL_DIV_LMUL`, `REAL_OF_NUM_EQ`, `ARITH`, `COS_PI`, `REAL_RING`


---

## TRISECT_60_DEGREES_ALGEBRA

### Name of formal statement
TRISECT_60_DEGREES_ALGEBRA

### Type of the formal statement
theorem

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
  ARITH_TAC);;
```
### Informal statement
It is not the case that there exists a real number `x` such that `x` is radical and `x` cubed minus 3 times `x` minus 1 equals 0.

### Informal sketch
The proof demonstrates that the cubic equation `x^3 - 3x - 1 = 0` has no radical solutions.

- First, it's shown that if there were a radical solution, then the cubic equation would have an integer root; this uses the theorem `CUBIC_ROOT_INTEGER`.
- The proof proceeds by contradiction. It is assumed that there exists a number `x` that is radical such that `x^3 - 3x - 1 = 0`. Basic algebraic simplification occurs using identities such as `REAL_ADD_ASSOC`, `REAL_MUL_LZERO`, `REAL_ADD_RID`, `REAL_MUL_LNEG`, and `real_sub`.
- Then, it's shown that `x * (x^2 - 3) = 1`. This uses `REAL_ARITH` to rearrange the cubic equation.
- Taking the absolute value of both sides, we have `abs(x * (x^2 - 3)) = abs(1)`.
- Using properties of absolute values and squares such as `REAL_ABS_MUL`, `REAL_ABS_NUM`, and `REAL_POW2_ABS`.
- Then, assume `x` is an integer `n` after choosing an integer representation of `x`.
- Perform case analysis on `n`, considering `n = 0`, `n = 1`, and `n >= 2`. The third case is handled by rewriting `n` as `2 + (n - 2)`.
- Reduce rational expressions to canonical forms using `REAL_RAT_REDUCE_CONV` and algebraic identities such as `REAL_OF_NUM_ADD`, `REAL_OF_NUM_MUL`, `REAL_OF_NUM_POW`, `REAL_ABS_NUM`, `REAL_OF_NUM_EQ`, and `MULT_EQ_1`.
- Finally, the proof concludes with `ARITH_TAC`, which uses arithmetic reasoning to complete the proof.

### Mathematical insight
This theorem demonstrates the impossibility of trisecting a 60-degree angle using only a compass and straightedge. A 60-degree angle can be easily constructed. Trisecting it would require constructing a 20-degree angle. The cosine of 20 degrees is a root of the cubic equation `8x^3 - 6x - 1 = 0`, or equivalently, `x^3 - 3/4*x - 1/8 = 0`. By scaling `x` by a factor of two we arrive at `x^3 - 3x - 1 = 0`. The theorem proves that this latter equation has no solution expressible by radicals. Hence, a 20-degree angle cannot be constructed with compass and straightedge because that would require to solve a cubic equation with no radical solution. 

### Dependencies
- `INTEGER_CLOSED`
- `NOT_IMP`
- `REAL_ADD_ASSOC`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`
- `REAL_MUL_LNEG`
- `real_sub`
- `REAL_ARITH`
- `REAL_ABS_MUL`
- `REAL_ABS_NUM`
- `REAL_POW2_ABS`
- `integer`
- `REAL_RAT_REDUCE_CONV`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_POW`
- `REAL_ABS_NUM`
- `REAL_OF_NUM_EQ`
- `MULT_EQ_1`
- `CUBIC_ROOT_INTEGER`


---

## TRISECT_60_DEGREES

### Name of formal statement
TRISECT_60_DEGREES

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[TRISECT_60_DEGREES_ALGEBRA; RADICAL_RULES]);;
```

### Informal statement
For all real numbers `y`, it is not the case that the vector with components `cos(pi / 9)` and `y` is constructible.

### Informal sketch
The proof demonstrates that it is impossible to construct a vector with components `cos(pi/9)` and any `y`. The main steps are:
- Assume that the vector with components `cos(pi/9)` and some `y` is constructible.
- Apply the theorem `CONSTRUCTIBLE_RADICAL`, which states that if a real number is constructible, it must be obtainable from the rationals by taking square roots.
- Use `CONJUNCT1` to state that if `(x, y)` is constructible, then `x` is constructible.
- Rewrite the constructible vector `(cos(pi/9), y)` to `cos(pi/9)` for further simplification.
- Instantiate `COS_TRIPLE`, which provides a trigonometric identity for `cos(3x)` in terms of `cos(x)`, with `x = pi/9`.
- Simplify using arithmetic and the identity `cos(pi/3) = 1/2`. Transform the resulting equation into a cubic equation of the form `(2c)^3 - 3(2c) - 1 = 0` where `c = cos(pi/9)`.
- Use `ASM_MESON_TAC` along with `TRISECT_60_DEGREES_ALGEBRA` and `RADICAL_RULES`. This step combines the algebraic representation of the constructibility of `cos(pi/9)` with established rules about radicals, ultimately leading to a contradiction since solutions to the cubic equation are not constructible via radicals.

### Mathematical insight
This theorem demonstrates the impossibility of trisecting a 60-degree angle using only a compass and straightedge. Since constructing the angle `pi/9` (20 degrees) is equivalent to constructing `cos(pi/9)`, and `cos(pi/9)` is a root of an irreducible cubic equation, it cannot be constructed using only compass and straightedge, hence trisecting 60 degrees is impossible.

### Dependencies
- `CONSTRUCTIBLE_RADICAL`
- `VECTOR_2`
- `COS_TRIPLE`
- `TRISECT_60_DEGREES_ALGEBRA`
- `RADICAL_RULES`
- `COS_PI3`
- `REAL_ARITH`

### Porting notes (optional)
- The `ASM_MESON_TAC` tactic in HOL Light performs automated reasoning using the given assumptions and theorems. Replicating its behavior in other proof assistants might require more explicit steps or a different automation strategy.
- The proof relies on algebraic manipulations and facts about constructible numbers using radicals. Porting this may require ensuring that the target proof assistant has comparable algebraic reasoning capabilities and facts about radical extensions.


---

