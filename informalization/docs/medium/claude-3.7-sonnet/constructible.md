# constructible.ml

## Overview

Number of statements: 49

This file formalizes the impossibility of solving certain geometric construction problems using straight-edge and compass, specifically the trisection of an angle and the duplication of a cube. It implements an elementary proof based on Dickson's "First Course in the Theory of Equations" that demonstrates the non-constructibility of irrational solutions to cubic equations. The formalization uses number-theoretic concepts from `prime.ml` and `floor.ml` rather than field extension theory, providing a more elementary approach to these classic impossibility results.

## STEP_LEMMA

### STEP_LEMMA

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
  CONV_TAC REAL_RING);;
```

### Informal statement
Let $P$ be a property of real numbers such that:
1. $P(n)$ holds for all natural numbers $n$
2. If $P(x)$ holds, then $P(-x)$ also holds
3. If $P(x)$ holds and $x \neq 0$, then $P(1/x)$ also holds
4. If $P(x)$ and $P(y)$ hold, then $P(x+y)$ holds
5. If $P(x)$ and $P(y)$ hold, then $P(xy)$ holds

Then for any real numbers $a$, $b$, $c$, $z$, $u$, $v$, and $s$, if:
- $P(a)$, $P(b)$, and $P(c)$ hold
- $z^3 + az^2 + bz + c = 0$
- $P(u)$, $P(v)$, and $P(s^2)$ hold
- $z = u + vs$

Then there exists a real number $w$ such that $P(w)$ holds and $w^3 + aw^2 + bw + c = 0$.

### Informal proof
The proof proceeds by case analysis.

* First, we check the case where $vs = 0$:
  - If $vs = 0$, then $z = u$, and we already know that $P(u)$ holds and $u^3 + au^2 + bu + c = 0$
  - So we can choose $w = u$ and the result follows immediately

* For the main case where $vs \neq 0$:
  - Substitute $z = u + vs$ into the cubic equation $z^3 + az^2 + bz + c = 0$
  - Define:
    * $A = as^2v^2 + 3s^2uv^2 + au^2 + u^3 + bu + c$
    * $B = s^2v^3 + 2auv + 3u^2v + bv$
  - The cubic equation, after expansion and rearrangement, gives us $A + Bs = 0$

  - We now consider two subcases based on whether $P(s)$ holds:
    
    1. If $P(s)$ holds, the result follows trivially from our assumptions
    
    2. If $P(s)$ does not hold:
      - We show that $B = 0$ by contradiction
      - If $B \neq 0$, then from $A + Bs = 0$ we get $s = -A/B$
      - But this would imply $P(s)$ holds since:
        * $P(A)$ holds from our closure properties and assumptions
        * $P(B)$ holds from our closure properties and assumptions
        * $P(-A)$ holds by property 2
        * $P(1/B)$ holds by property 3
        * $P(-A/B)$ holds by property 5
      - This contradicts our assumption that $P(s)$ does not hold
      - Therefore $B = 0$
      
  - With $B = 0$ established, we claim that $w = -(a + 2u)$ satisfies the required conditions
  - By the closure properties, $P(w)$ holds
  - Using algebraic manipulation, we can verify that $w^3 + aw^2 + bw + c = 0$

### Mathematical insight
This lemma is a crucial step in proving results about the non-constructibility of certain numbers using ruler and compass constructions. The property $P$ can be interpreted as "constructible by ruler and compass operations," with the five axioms corresponding to the basic operations possible in such constructions.

The lemma shows that if a cubic equation has one root that can be expressed in a certain form where $P$ holds for the components, then it must have another root for which $P$ directly holds. This will ultimately be used to show that certain cubic equations, like those arising from angle trisection or cube duplication, have roots that cannot be constructed using ruler and compass.

The proof technique is particularly elegant because it avoids the machinery of field extensions and Galois theory that is often used for such results, instead relying on more elementary algebraic manipulations.

### Dependencies
- Algebraic manipulations
- Properties of real numbers
- Basic logic and case analysis

### Porting notes
When porting this proof:
- The proof relies heavily on algebraic manipulations, most of which are handled in HOL Light by the `REAL_RING` conversion
- The case analysis structure should be preserved
- Careful attention should be paid to the definitions of $A$ and $B$, as they are crucial to the proof

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
For any predicate $P$ on real numbers, if:
- $P(n)$ holds for all natural numbers $n$,
- $P(x)$ implies $P(-x)$ for all real $x$,
- $P(x)$ and $x \neq 0$ implies $P(1/x)$ for all real $x$,
- $P(x)$ and $P(y)$ implies $P(x + y)$ for all real $x, y$,
- $P(x)$ and $P(y)$ implies $P(x \cdot y)$ for all real $x, y$,

then for all real numbers $a, b, c, z, u, v, s$ where:
- $P(a)$, $P(b)$, and $P(c)$ hold,
- $z^3 + a \cdot z^2 + b \cdot z + c = 0$,
- $P(u)$, $P(v)$, and $P(s)$ hold,
- $s \geq 0$,
- $z = u + v \cdot \sqrt{s}$,

there exists a real number $w$ such that:
- $P(w)$ holds, and
- $w^3 + a \cdot w^2 + b \cdot w + c = 0$.

### Informal proof
This theorem is proved by applying a more general result `STEP_LEMMA` and specializing it to the case involving square roots.

- We start with assuming the premises of the theorem for an arbitrary predicate $P$.
- We apply `STEP_LEMMA` to these assumptions, which provides the general form of the conclusion.
- For the specific case involving square roots, we use `SQRT_POW_2` (which states that $(\sqrt{s})^2 = s$ for $s \geq 0$) and `REAL_POW_2` (which defines the square of a number).
- The automated reasoner `ASM_MESON_TAC` combines these facts with our assumptions to prove that there exists a $w$ with the required properties.

### Mathematical insight
This theorem is essentially a specialized version of `STEP_LEMMA` for numbers of the form $u + v\sqrt{s}$ where $s \geq 0$. It shows that if $z = u + v\sqrt{s}$ is a root of a cubic polynomial with coefficients satisfying a predicate $P$, then another root $w$ of the same polynomial exists that also satisfies $P$.

This result is important in the theory of algebraic numbers and field extensions. It demonstrates that certain algebraic structures are closed under the operations defined by the predicate $P$, which includes standard arithmetic operations. In the context of cubic equations, this theorem helps establish that if one root has a particular form, another root with similar properties can be found.

### Dependencies
- `STEP_LEMMA`: The general lemma about predicates preserved by field operations
- `SQRT_POW_2`: Theorem that $(\sqrt{s})^2 = s$ for $s \geq 0$
- `REAL_POW_2`: Definition or theorem about the second power of real numbers

### Porting notes
When porting this theorem:
- Ensure the target system has a good representation of square roots and their properties.
- The proof relies heavily on automation (`ASM_MESON_TAC`), so in systems with less powerful automation, you may need to provide more explicit reasoning steps.
- The handling of predicates over reals might differ between systems; adjust accordingly.
- Make sure the dependencies, especially `STEP_LEMMA`, are properly ported first.

---

## radical_RULES,radical_INDUCT,radical_CASES

### Name of formal statement
radical_RULES, radical_INDUCT, radical_CASES

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
The inductive definition `radical` characterizes the set of numbers definable by radicals involving square roots only. It is defined by the following rules:

1. If $x$ is rational, then $x$ is radical.
2. If $x$ is radical, then $-x$ is radical.
3. If $x$ is radical and $x \neq 0$, then $\frac{1}{x}$ is radical.
4. If $x$ and $y$ are radical, then $x + y$ is radical.
5. If $x$ and $y$ are radical, then $x \cdot y$ is radical.
6. If $x$ is radical and $x \geq 0$, then $\sqrt{x}$ is radical.

### Informal proof
This is an inductive definition, not a theorem with a proof. The definition establishes the set of radical numbers as the smallest set satisfying the six closure properties listed above.

### Mathematical insight
This definition characterizes numbers that can be constructed from the rational numbers using only the field operations (addition, multiplication, negation, and reciprocal) and square roots. These are precisely the numbers that can be expressed using nested radicals with rational coefficients.

The definition is important in relation to classical problems in algebra such as the solvability of polynomial equations. Numbers expressible by radicals represent those that can be obtained as solutions to equations that can be solved by applying a sequence of field operations and taking square roots.

Unlike the more general concept of "numbers expressible by radicals" (which would include cube roots, fourth roots, etc.), this definition is restricted to square roots only, making it a proper subset of the algebraic numbers.

### Dependencies
None explicitly listed in the provided dependency information.

### Porting notes
When porting this definition to other proof assistants:
1. Ensure that the target system supports inductive definitions of predicates on real numbers
2. The definition relies on having a formal representation of rational numbers (`rational`) and square roots (`sqrt`)
3. Note that this definition produces three constants: 
   - `radical_RULES`: The collection of rules defining the predicate
   - `radical_INDUCT`: An induction principle for proving properties of radical numbers
   - `radical_CASES`: A case analysis principle for radical numbers

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
This theorem establishes a collection of closure properties for radical numbers:

1. For any integer $n$, $n$ is a radical number.
2. Any rational number is a radical number.
3. If $x$ is a radical number, then $-x$ is also a radical number.
4. If $x$ is a radical number and $x \neq 0$, then $\frac{1}{x}$ is also a radical number.
5. If $x$ and $y$ are radical numbers, then $x + y$ is also a radical number.
6. If $x$ and $y$ are radical numbers, then $x - y$ is also a radical number.
7. If $x$ and $y$ are radical numbers, then $x \times y$ is also a radical number.
8. If $x$ and $y$ are radical numbers and $y \neq 0$, then $\frac{x}{y}$ is also a radical number.
9. If $x$ is a radical number and $n$ is any natural number, then $x^n$ is also a radical number.
10. If $x$ is a radical number and $x \geq 0$, then $\sqrt{x}$ is also a radical number.

### Informal proof
The proof proceeds by simplification and induction:

1. First, we simplify using the definitions of real division (`real_div`), real subtraction (`real_sub`), basic properties of radical numbers (`radical_RULES`), and the fact that all integers are rational (`RATIONAL_NUM`).

2. For the last part concerning powers, we use induction on the exponent $n$:
   - Base case: For $n = 0$, $x^0 = 1$ which is rational and thus radical.
   - Inductive step: Assuming $x^n$ is radical, we show that $x^{n+1} = x \times x^n$ is also radical by using the closure of radical numbers under multiplication.

The proof relies on the basic properties of radical numbers and the fact that all rational numbers are radical.

### Mathematical insight
Radical numbers form an important extension of the rational numbers, consisting of numbers that can be constructed from integers using the field operations (addition, subtraction, multiplication, division) and taking square roots of non-negative numbers. This theorem establishes that radical numbers form a field that is closed under taking square roots of non-negative elements.

Radical numbers are important in the history of mathematics as they represent numbers that can be expressed using a finite number of radicals (square roots, cube roots, etc.) and are thus "constructible" in a sense. They are closely related to the classical problem of which numbers can be constructed with straightedge and compass.

This theorem provides a formal verification that radical numbers behave as expected with respect to basic arithmetic operations and taking square roots.

### Dependencies
#### Theorems
- `RATIONAL_NUM`: All integers are rational numbers
- `radical_RULES`: Basic properties of radical numbers

#### Definitions
- `real_div`: Real number division
- `real_sub`: Real number subtraction
- `real_pow`: Real number exponentiation

### Porting notes
When porting this theorem to another system:
1. Ensure that the concept of radical numbers is defined in the target system.
2. The proof might be simplified in systems with better automation for algebraic reasoning.
3. Different systems might have different ways of handling the natural number induction for the power case.

---

## RADICAL_TAC

### Name of formal statement
RADICAL_TAC

### Type of the formal statement
tactic definition

### Formal Content
```ocaml
let RADICAL_TAC =
  REPEAT(MATCH_ACCEPT_TAC (CONJUNCT1 RADICAL_RULES) ORELSE
         (MAP_FIRST MATCH_MP_TAC(tl(tl(CONJUNCTS RADICAL_RULES))) THEN
          REPEAT CONJ_TAC));;
```

### Informal statement
`RADICAL_TAC` is a tactic that attempts to prove goals of the form `radical t` by repeatedly applying the rules from `RADICAL_RULES`. It first tries to directly apply the rule that integers are radical numbers. If that fails, it tries to apply any of the other radical rules (except for the rational number rule), and then breaks down any resulting conjunctions.

### Informal proof
This is a tactic definition rather than a theorem, so it doesn't have a formal proof. The tactic works as follows:

The tactic repeatedly tries:
1. First, match and accept the first conjunct of `RADICAL_RULES` (which states that all integers are radical numbers) using `MATCH_ACCEPT_TAC (CONJUNCT1 RADICAL_RULES)`.
2. If that fails, it tries to apply one of the remaining rules from `RADICAL_RULES` (excluding the first two rules) using `MAP_FIRST MATCH_MP_TAC(tl(tl(CONJUNCTS RADICAL_RULES)))`.
3. After applying one of these rules, it breaks down any resulting conjunctions using `REPEAT CONJ_TAC`.

The implementation skips the second rule of `RADICAL_RULES` (which states that rational numbers are radical) by using `tl(tl(CONJUNCTS RADICAL_RULES))`, which drops the first two conjuncts.

### Mathematical insight
This tactic implements a decision procedure for proving that certain numbers are radical (also known as constructible numbers). The radical numbers form a field that includes integers and is closed under basic arithmetic operations and square roots of non-negative numbers.

The tactic automates the application of the closure properties of radical numbers, making it easier to prove that particular expressions represent radical numbers. It's designed to be easier to use than manually applying the individual rules from `RADICAL_RULES`.

By skipping the rule that states all rational numbers are radical, the tactic forces the user to build up radical expressions from integers and operations, rather than directly asserting that a rational number is radical.

### Dependencies
#### Theorems
- `RADICAL_RULES` - A theorem containing all the closure properties of radical numbers:
  - All integers are radical numbers
  - All rational numbers are radical numbers
  - Radicals are closed under negation
  - Radicals are closed under reciprocal (when nonzero)
  - Radicals are closed under addition
  - Radicals are closed under subtraction
  - Radicals are closed under multiplication
  - Radicals are closed under division (when denominator nonzero)
  - Radicals are closed under integer powers
  - Radicals are closed under square roots (when non-negative)

### Porting notes
When porting this tactic to another proof assistant:
1. You'll need to first implement or port the concept of radical/constructible numbers.
2. The analogous tactic should use the system's mechanisms for applying rules and managing subgoals.
3. Consider whether the target system has better ways to handle algebraic structures with closure properties (e.g., typeclasses in systems like Lean or Coq) which might provide more elegant alternatives.
4. Note that in some systems, you might want to create a type for radical numbers rather than a predicate, which would change the nature of the tactic entirely.

---

## expression_INDUCT,expression_RECURSION

### Name of formal statement
expression_INDUCT, expression_RECURSION

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
This defines a new inductive type `expression` representing symbolic mathematical expressions with the following constructors:
- `Constant r` for a real constant $r$
- `Negation e` for the negation of an expression $e$
- `Inverse e` for the multiplicative inverse of an expression $e$
- `Addition e₁ e₂` for the addition of expressions $e₁$ and $e₂$
- `Multiplication e₁ e₂` for the multiplication of expressions $e₁$ and $e₂$
- `Sqrt e` for the square root of an expression $e$

The definition automatically generates two theorems:
- `expression_INDUCT`: an induction principle for the `expression` type
- `expression_RECURSION`: a recursion principle for the `expression` type

### Informal proof
This is a type definition, not a theorem, so there is no proof. The system automatically generates the induction and recursion principles for the inductive datatype.

### Mathematical insight
This type definition creates a formal representation of symbolic mathematical expressions involving real numbers and basic operations (negation, inverse, addition, multiplication, and square root). Such a representation is useful for:

1. Performing inductive proofs about properties of expressions
2. Defining recursive functions on expressions (e.g., evaluation, simplification)
3. Supporting formal reasoning about mathematical formulas

The type serves as a syntactic representation of expressions, separating their structure from their semantic meaning. This is a common approach in formal verification of mathematical operations and algorithms.

The generated induction principle allows proving properties for all possible expressions by considering each constructor case, while the recursion principle enables defining functions that operate on expressions by specifying the behavior for each constructor.

### Dependencies
None explicitly listed.

### Porting notes
When porting to other systems:
1. In dependently typed systems like Coq or Lean, this would typically be defined as an inductive datatype.
2. In Isabelle/HOL, this would be a datatype definition.
3. Some systems might require explicitly stating that `real` is the type of constants.
4. The naming conventions for the automatically generated theorems may differ:
   - Lean might use names like `expression.induction` and `expression.rec`
   - Isabelle might use names like `expression.induct` and `expression.rec`
   - Coq might generate these principles implicitly

---

## value

### Name of formal statement
`value`

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
`value` is a recursive function that evaluates constructible expressions to their numerical values:

- `value(Constant x) = x`: The value of a constant expression is the constant itself.
- `value(Negation e) = -value(e)`: The value of a negation expression is the negation of the value of the expression.
- `value(Inverse e) = 1/value(e)`: The value of an inverse expression is the reciprocal of the value of the expression.
- `value(Addition e1 e2) = value(e1) + value(e2)`: The value of an addition expression is the sum of the values of the two expressions.
- `value(Multiplication e1 e2) = value(e1) × value(e2)`: The value of a multiplication expression is the product of the values of the two expressions.
- `value(Sqrt e) = √value(e)`: The value of a square root expression is the square root of the value of the expression.

### Informal proof
This is a definition, not a theorem, so no proof is required.

### Mathematical insight
This function interprets constructible expressions by evaluating them to their corresponding real values. In mathematics, constructible numbers are those that can be constructed using a straightedge and compass, which corresponds to operations like addition, multiplication, and taking square roots of positive numbers.

The `value` function is crucial in the formalization of constructible numbers because it bridges the gap between the syntactic representation of constructible expressions and their semantic meaning as real numbers. This allows us to reason about constructible numbers in terms of their algebraic properties. 

The definition is structured recursively based on the structure of constructible expressions, reflecting the algebraic operations that can be performed in compass and straightedge constructions: starting from constants, one can add, multiply, negate, take reciprocals, and extract square roots.

### Dependencies
#### Definitions
- `value`: The recursive function being defined that evaluates constructible expressions

### Porting notes
When porting this definition:
1. Ensure that the target system has a definition for constructible expressions (`Constant`, `Negation`, etc.) as an inductive type
2. The target system should support recursive definitions on this inductive type
3. Functions like negation (`--`), inverse (`inv`), addition (`+`), multiplication (`*`), and square root (`sqrt`) should be available in the target system

---

## wellformed

### wellformed

### Type of the formal statement
Definition (new_definition)

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
The `wellformed` predicate defines when a constructible expression is well-formed:

- A constant expression `Constant x` is well-formed if and only if `x` is rational.
- A negation expression `Negation e` is well-formed if and only if `e` is well-formed.
- An inverse expression `Inverse e` is well-formed if and only if `e` is well-formed and the value of `e` is not equal to 0.
- An addition expression `Addition e1 e2` is well-formed if and only if both `e1` and `e2` are well-formed.
- A multiplication expression `Multiplication e1 e2` is well-formed if and only if both `e1` and `e2` are well-formed.
- A square root expression `Sqrt e` is well-formed if and only if `e` is well-formed and the value of `e` is non-negative.

### Informal proof
This is a definition, not a theorem, so there is no proof.

### Mathematical insight
This definition captures the conditions under which algebraic expressions representing constructible numbers are mathematically meaningful. It ensures that:

1. We start with rational numbers as our base field
2. Division by zero is avoided by requiring non-zero values for inverses
3. Square roots are only taken of non-negative values

This definition, coupled with the `value` function, formalizes the field of constructible numbers - those that can be constructed using straightedge and compass operations from rational numbers. These are precisely the numbers that can be expressed through a finite sequence of arithmetic operations (addition, subtraction, multiplication, division) and square roots.

The concept of "well-formedness" ensures that we're only working with expressions that have a meaningful value in the real number system, avoiding undefined operations like division by zero or square roots of negative numbers.

### Dependencies
- **Definitions**:
  - `value`: Evaluates the value of a constructible expression
  - `rational`: Predicate for rational numbers

### Porting notes
When porting this definition to other proof assistants:
1. Ensure that the type of constructible expressions is properly defined first with its constructors (`Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, `Sqrt`)
2. Make sure the `value` function is defined before `wellformed`, as the latter depends on it
3. The definition uses mutual recursion between `value` and `wellformed` - some systems might require special handling for this relationship

---

## radicals

### radicals

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
The function `radicals` maps an expression to the set of all radical expressions (square roots) used within it, defined recursively as follows:

- $\text{radicals}(\text{Constant}\ x) = \emptyset$ (Constants have no radicals)
- $\text{radicals}(\text{Negation}\ e) = \text{radicals}(e)$ (Negation preserves radicals)
- $\text{radicals}(\text{Inverse}\ e) = \text{radicals}(e)$ (Inversion preserves radicals)
- $\text{radicals}(\text{Addition}\ e_1\ e_2) = \text{radicals}(e_1) \cup \text{radicals}(e_2)$ (Addition combines radicals)
- $\text{radicals}(\text{Multiplication}\ e_1\ e_2) = \text{radicals}(e_1) \cup \text{radicals}(e_2)$ (Multiplication combines radicals)
- $\text{radicals}(\text{Sqrt}\ e) = \{e\} \cup \text{radicals}(e)$ (Square root adds the expression to the radical set)

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition captures the set of all subexpressions that appear under a square root in a given expression. It's a useful concept when working with constructible numbers, which are numbers that can be expressed using only the four basic operations and square roots.

The definition recursively collects all expressions that appear as arguments to the square root operation. For the base case (constants), there are no radicals. For unary operations like negation and inverse, the radicals remain the same as in the operand. For binary operations like addition and multiplication, the radicals are the union of the radicals of the operands. Finally, when taking a square root of an expression, we add that expression itself to the set of radicals, in addition to any radicals already contained within the expression.

This definition is particularly important in the context of field theory and constructible numbers, where understanding which expressions appear under radicals helps determine whether a number is constructible with ruler and compass.

### Dependencies
#### Definitions
- `radicals`: The definition itself, defining the set of radical expressions in an algebraic expression

### Porting notes
When implementing this in another proof assistant, ensure that the expression datatype is already defined with constructors for constants, negation, inverse, addition, multiplication, and square root. The recursive definition structure should be straightforward to port, but you'll need to ensure that the set operations (empty set, insertion, and union) have appropriate equivalents in your target system.

---

## FINITE_RADICALS

### FINITE_RADICALS

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
For any expression $e$, the set of radicals $\text{radicals}(e)$ is finite.

### Informal proof
The proof uses induction on the structure of expressions. 

- We apply `expression_INDUCT` to perform structural induction on algebraic expressions.
- Then we simplify using the definition of `radicals` and apply theorems about finiteness of sets:
  - For constant expressions, $\text{radicals}(\text{Constant}(x)) = \{\}$, which is finite.
  - For negation and inverse, $\text{radicals}(\text{Negation}(e)) = \text{radicals}(e)$ and $\text{radicals}(\text{Inverse}(e)) = \text{radicals}(e)$, which are finite by the induction hypothesis.
  - For addition and multiplication, $\text{radicals}(\text{Addition}(e_1, e_2)) = \text{radicals}(e_1) \cup \text{radicals}(e_2)$ and $\text{radicals}(\text{Multiplication}(e_1, e_2)) = \text{radicals}(e_1) \cup \text{radicals}(e_2)$, which are finite by the induction hypothesis and the fact that the union of finite sets is finite.
  - For square root, $\text{radicals}(\text{Sqrt}(e)) = \{e\} \cup \text{radicals}(e)$, which is finite as singleton sets are finite and the union of finite sets is finite.

### Mathematical insight
The theorem establishes that for any algebraic expression containing square roots, the set of subexpressions under radicals is finite. This is an important foundation for proving properties about constructible numbers and field extensions in algebraic number theory. Understanding which expressions appear under radicals is crucial for analyzing constructible numbers and determining which numbers are constructible using straightedge and compass.

### Dependencies
- **Definitions**: `radicals` - defines how to collect all subexpressions appearing under radicals in an algebraic expression
- **Tactics and rules**: 
  - `expression_INDUCT` - induction principle for algebraic expressions
  - `FINITE_RULES` - collection of rules about finite sets
  - `FINITE_UNION` - theorem stating that the union of finite sets is finite

### Porting notes
When porting this theorem to other systems:
- Ensure the algebraic expression datatype has a similar inductive structure
- Check that the system has a well-developed library of results about finite sets
- The proof is relatively straightforward and should translate easily to other systems that support structural induction

---

## WELLFORMED_RADICALS

### WELLFORMED_RADICALS
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

### Formal Content
```ocaml
let WELLFORMED_RADICALS = prove
 (`!e. wellformed e ==> !r. r IN radicals(e) ==> &0 <= value r`,
  MATCH_MP_TAC expression_INDUCT THEN
  REWRITE_TAC[radicals; wellformed; NOT_IN_EMPTY; IN_UNION; IN_INSERT] THEN
  MESON_TAC[]);;
```

### Informal statement
For any expression $e$, if $e$ is well-formed, then for all expressions $r$ in the set of radicals of $e$, the value of $r$ is non-negative: $\forall e. \text{wellformed}(e) \Rightarrow \forall r. r \in \text{radicals}(e) \Rightarrow 0 \leq \text{value}(r)$.

### Informal proof
This theorem is proved by induction on the structure of expressions. 

- We begin with `MATCH_MP_TAC expression_INDUCT` which sets up structural induction on expressions.
- Then we rewrite using the definitions of `radicals`, `wellformed`, and set membership operations.
- Finally, we use `MESON_TAC[]` to complete the proof by automated reasoning.

The proof essentially works through each constructor of expressions:
- For constants, the set of radicals is empty, so the property holds vacuously.
- For negations and inverses, the radicals are the same as the subexpression, and well-formedness ensures the property holds.
- For addition and multiplication, the radicals are the union of the radicals of the subexpressions, and well-formedness of both ensures the property.
- For square roots, the expression itself is added to its radicals, and well-formedness requires that its value is non-negative.

### Mathematical insight
This theorem establishes an important property of well-formed expressions: all of their radicals (i.e., expressions under square roots) must have non-negative values. This is a natural mathematical constraint since square roots of negative numbers aren't constructible numbers.

In the context of constructible numbers, this theorem ensures that all square root operations in a well-formed expression are defined over non-negative values, maintaining the integrity of the constructible field. This is crucial for the proper definition and manipulation of constructible numbers, which are built from rational numbers using field operations and square roots.

### Dependencies
- Definitions:
  - `wellformed`: Defines when an expression is well-formed
  - `radicals`: Defines the set of expressions under square roots in an expression
  - `value`: Evaluates an expression to its real value

### Porting notes
When porting to other systems, ensure that:
1. The expression datatype with constants, negations, inverses, additions, multiplications, and square roots is properly defined.
2. The inductive nature of the proof is preserved.
3. The requirement that square roots are only applied to non-negative values is enforced in the well-formedness definition.
4. Set operations (empty set, union, insert) have equivalent definitions.

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
For any expression $e$, if $e$ is well-formed, then for any expression $r$ in the set of radicals of $e$, $r$ is also well-formed.

In notation: $\forall e. \text{wellformed}(e) \Rightarrow \forall r. r \in \text{radicals}(e) \Rightarrow \text{wellformed}(r)$

### Informal proof
The proof uses structural induction on expressions and follows these steps:

* Apply structural induction on expressions using the `expression_INDUCT` tactic.
* Rewrite using the definitions of `radicals` and `wellformed`.
* The base case (for constants) is trivial since `radicals(Constant x) = {}`, so there are no radicals to check.
* For the inductive cases:
  * For negation and inverse operations, the radicals of the resulting expression are the same as the radicals of the operand.
  * For addition and multiplication, the radicals are the union of the radicals of the operands.
  * For the square root operation, the radicals include the operand itself plus all radicals of the operand.
* The `MESON_TAC[]` completes the proof by automatically handling the logical implications for each case, showing that well-formedness of the original expression ensures well-formedness of all its radicals.

### Mathematical insight
This theorem establishes an important property of well-formed expressions and their radicals: if an expression is well-formed, then all expressions appearing inside square roots within it (its radicals) are also well-formed.

In the context of constructible numbers, this theorem helps ensure that operations on constructible expressions preserve well-formedness throughout the expression tree. This is particularly important when working with nested radical expressions, as it guarantees that at each level of nesting, the expressions remain mathematically valid (rational, non-zero when inverted, non-negative when square rooted, etc.).

### Dependencies
#### Definitions
- `wellformed`: Defines when an expression is mathematically valid
- `radicals`: Collects all expressions appearing inside square roots within an expression

#### Tactics and Proof Methods
- `expression_INDUCT`: Structural induction on expressions
- `REWRITE_TAC`: Rewrites using given definitions
- `MESON_TAC`: Automated reasoning with first-order logic

### Porting notes
When porting this theorem:
- Ensure that the definition of expressions, well-formedness, and radicals are correctly established first
- The inductively defined data type for expressions needs to match HOL Light's definition
- The induction principle `expression_INDUCT` would need an equivalent in the target system

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
For any expression $e$ and any element $r$, if $r \in \text{radicals}(e)$, then $\text{radicals}(r) \subseteq \text{radicals}(e)$.

### Informal proof
The proof proceeds by induction on the structure of the expression $e$ using `expression_INDUCT`. 

We consider all cases of the `radicals` definition:
- For constants: $\text{radicals}(\text{Constant}(x)) = \emptyset$, so the premise $r \in \text{radicals}(e)$ is false, making the implication trivially true.
- For negation: $\text{radicals}(\text{Negation}(e)) = \text{radicals}(e)$, so the result follows from the inductive hypothesis.
- For inverse: $\text{radicals}(\text{Inverse}(e)) = \text{radicals}(e)$, so similarly follows from the inductive hypothesis.
- For addition: $\text{radicals}(\text{Addition}(e_1, e_2)) = \text{radicals}(e_1) \cup \text{radicals}(e_2)$. If $r \in \text{radicals}(e_1) \cup \text{radicals}(e_2)$, then $r \in \text{radicals}(e_1)$ or $r \in \text{radicals}(e_2)$, so by the inductive hypothesis, $\text{radicals}(r) \subseteq \text{radicals}(e_1)$ or $\text{radicals}(r) \subseteq \text{radicals}(e_2)$, which means $\text{radicals}(r) \subseteq \text{radicals}(e_1) \cup \text{radicals}(e_2) = \text{radicals}(\text{Addition}(e_1, e_2))$.
- For multiplication: Similar to addition.
- For square root: $\text{radicals}(\text{Sqrt}(e)) = \{e\} \cup \text{radicals}(e)$. If $r \in \{e\} \cup \text{radicals}(e)$, then either $r = e$ or $r \in \text{radicals}(e)$. If $r = e$, then $\text{radicals}(r) = \text{radicals}(e) \subseteq \text{radicals}(\text{Sqrt}(e))$. If $r \in \text{radicals}(e)$, then by the inductive hypothesis, $\text{radicals}(r) \subseteq \text{radicals}(e) \subseteq \text{radicals}(\text{Sqrt}(e))$.

The `MESON_TAC[]` tactic automatically handles the logical reasoning required to complete these cases.

### Mathematical insight
This theorem establishes an important containment property of the `radicals` function, which collects all subexpressions that appear under square roots in a given expression. It states that if an expression $r$ appears in the radicals of another expression $e$, then all of $r$'s own radicals must also appear in $e$'s radicals.

This property is important for analyzing the structure of expressions involving nested radicals and is likely used in the formalization of constructible numbers or in proofs about algebraic expressions.

The theorem captures the intuitive idea that when working with nested radical expressions, the "inner" radicals are contained within the set of all radicals in the full expression.

### Dependencies
#### Definitions
- `radicals` - Function that collects all subexpressions appearing under square roots in an expression

#### Tactics and proof tools
- `expression_INDUCT` - Induction principle for expressions
- `REWRITE_TAC` - Rewriting tactic
- `MESON_TAC` - Automated reasoning tactic

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
For any real number $x$, $x$ is a radical number if and only if there exists a well-formed expression $e$ such that $x = \text{value}(e)$.

This theorem establishes the equivalence between the inductive definition of radical numbers and the existence of a well-formed expression that evaluates to the number.

### Informal proof
The proof proceeds by proving both directions of the equivalence:

* Forward direction ($\Rightarrow$): We use induction on radical numbers via `radical_INDUCT`. For each case in the inductive definition of radical numbers, we show that there exists a corresponding well-formed expression. This follows directly from the definitions of `value` and `wellformed`, as each radical number can be constructed from basic expressions.

* Backward direction ($\Leftarrow$): We assume there exists a well-formed expression $e$ such that $x = \text{value}(e)$, and prove that $x$ is a radical number. The proof proceeds by induction on the structure of expressions using `expression_INDUCT`. For each type of expression (constant, negation, inverse, addition, multiplication, and square root), we show that if the components are well-formed, then the resulting value is a radical number according to `radical_RULES`.

### Mathematical insight
This theorem establishes an important characterization of radical numbers: they are precisely the values that can be expressed using a formal language of well-formed expressions involving rational constants, arithmetic operations, and square roots.

This equivalence allows us to work with radical numbers either through their inductive definition (which might be more convenient for theoretical results) or through their representation as expressions (which might be more practical for computational purposes).

The theorem bridges the gap between the abstract mathematical concept of radical numbers and their concrete representation as expressions built from basic operations.

### Dependencies
- Definitions:
  - `value`: Evaluates expressions to real numbers
  - `wellformed`: Defines when an expression has a valid interpretation

- Theorems:
  - `radical_INDUCT`: Induction principle for radical numbers
  - `radical_RULES`: Basic construction rules for radical numbers
  - `expression_INDUCT`: Induction principle for expressions

### Porting notes
When porting this theorem to other systems:
1. Ensure that the inductive definitions of expressions and radical numbers are properly set up
2. The proof relies on bidirectional induction principles (on both radical numbers and expressions), so ensure these principles are available in the target system
3. The equivalence proof might benefit from automation for handling the various cases in the inductive definitions

---

## LT_MAX

### LT_MAX

### Type of formal statement
theorem

### Formal Content
```ocaml
let LT_MAX = prove
 (`!a b c. a < MAX b c <=> a < b \/ a < c`,
  ARITH_TAC);;
```

### Informal statement
For all real numbers $a$, $b$, and $c$:
$$a < \max(b, c) \Leftrightarrow a < b \lor a < c$$

This theorem states that a number is less than the maximum of two numbers if and only if it is less than at least one of those numbers.

### Informal proof
This is proved using the arithmetic decision procedure (`ARITH_TAC`), which automatically handles linear arithmetic facts in HOL Light.

The proof follows from the definition of maximum:
- If $a < \max(b, c)$, then since $\max(b, c) = b$ when $b \geq c$ and $\max(b, c) = c$ when $c > b$, we must have either $a < b$ or $a < c$.
- Conversely, if $a < b$, then $a < \max(b, c)$ since $\max(b, c) \geq b$. Similarly, if $a < c$, then $a < \max(b, c)$ since $\max(b, c) \geq c$.

### Mathematical insight
This theorem captures an essential property of the maximum function: an element is less than the maximum of a set if and only if it is less than at least one element in the set. In the case of two elements, this simplifies to the given statement.

This property is frequently used in proofs involving bounds and inequalities. For instance, when establishing upper bounds for expressions involving maximums.

### Dependencies
- `ARITH_TAC`: HOL Light's arithmetic decision procedure that automatically proves theorems about linear arithmetic over integers and reals.

### Porting notes
This theorem should be straightforward to port to other proof assistants. Most systems have built-in tactics for arithmetic reasoning that can handle this type of statement automatically. If a system doesn't have such automation, the proof can be constructed by case analysis on whether $b \geq c$ or $c > b$.

---

## depth

### depth
- `depth`

### Type of the formal statement
- new_definition

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
The `depth` function is defined recursively on expressions as follows:

- $\text{depth}(\text{Constant}(x)) = 0$
- $\text{depth}(\text{Negation}(e)) = \text{depth}(e)$
- $\text{depth}(\text{Inverse}(e)) = \text{depth}(e)$
- $\text{depth}(\text{Addition}(e_1, e_2)) = \max(\text{depth}(e_1), \text{depth}(e_2))$
- $\text{depth}(\text{Multiplication}(e_1, e_2)) = \max(\text{depth}(e_1), \text{depth}(e_2))$
- $\text{depth}(\text{Sqrt}(e)) = 1 + \text{depth}(e)$

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
The `depth` function defines a measure of complexity for expressions in the constructible numbers formalization. It specifically tracks the nesting depth of square root operations in an expression:

- Constants have depth 0
- Negation and inverse operations preserve the depth of their operand
- Addition and multiplication take the maximum depth of their operands
- Square root increases the depth by 1

This depth measure is particularly useful for induction proofs involving constructible expressions, as it provides a well-founded measure that increases only with square root operations. This captures the intuition that the complexity of constructible numbers primarily comes from nested square roots rather than from basic arithmetic operations.

### Dependencies
None explicitly listed, but implicitly depends on:
- The inductive type definition for constructible number expressions (`Constant`, `Negation`, `Inverse`, `Addition`, `Multiplication`, `Sqrt`)
- The `MAX` function for determining the maximum of two values

### Porting notes
When porting this definition:
1. Ensure that the target system has an equivalent inductive type for constructible expressions with the same constructors
2. If the target system doesn't have a built-in `MAX` function, you may need to define it
3. The recursive definition should be straightforward to port, as it follows a simple pattern matching structure on the expression constructors

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
For any expressions $r$ and $s$, if $s$ is in the set of radicals of $r$ (denoted as $s \in \text{radicals}(r)$), then the depth of $s$ is less than the depth of $r$ (i.e., $\text{depth}(s) < \text{depth}(r)$).

### Informal proof
The proof proceeds by structural induction on the expression $r$ using the induction principle for expressions.

1. We first rewrite using the definitions of `radicals` and `depth`.
   
2. After rewriting, we simplify set operations: 
   - Elements of union: $x \in (A \cup B) \iff x \in A \lor x \in B$
   - Empty set: $x \notin \emptyset$ is always true
   - Elements of insertion: $x \in (a \text{ INSERT } A) \iff x = a \lor x \in A$
   - The property of maximum: $a < \max(b,c) \iff a < b \lor a < c$

3. Finally, we complete the proof using the following arithmetic fact:
   $s = a \lor s < a \Rightarrow s < 1 + a$
   
   This handles the case where $s \in \text{radicals}(\text{Sqrt}(e))$, which means either $s = e$ or $s \in \text{radicals}(e)$. In either case, we need to show $\text{depth}(s) < \text{depth}(\text{Sqrt}(e)) = 1 + \text{depth}(e)$.

### Mathematical insight
This theorem establishes an important structural property of the radical expressions: any radical appearing in an expression has strictly smaller depth than the expression itself. This is a form of well-foundedness that enables inductive reasoning on expressions based on their depth.

The result is particularly useful for algorithms or proofs that need to process radical expressions recursively, as it ensures termination by showing that the depth strictly decreases at each recursive step through the radicals.

The theorem confirms that the definitions of `depth` and `radicals` work together coherently, which is essential for the formal treatment of constructible numbers represented by nested radical expressions.

### Dependencies
#### Theorems:
- `LT_MAX`: For any $a$, $b$, and $c$, $a < \max(b,c) \iff a < b \lor a < c$

#### Definitions:
- `radicals`: Defines the set of radical expressions contained in an expression
- `depth`: Defines the depth of an expression (measure of nesting of square roots)

#### Induction principles:
- `expression_INDUCT`: Structural induction principle for expressions

### Porting notes
When porting this theorem:
- Ensure that the representation of expressions and the definitions of `radicals` and `depth` are consistent with the original.
- The proof relies on structural induction, so the target system should have good support for inductive definitions and proofs.
- The rewriting steps are straightforward, but you may need to adjust the tactics depending on how set operations are handled in the target system.
- The final step uses a simple arithmetic fact that should be easy to prove in most systems, but you might need to state and prove it explicitly if automation doesn't handle it.

---

## NOT_IN_OWN_RADICALS

### NOT_IN_OWN_RADICALS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_IN_OWN_RADICALS = prove
 (`!r. ~(r IN radicals r)`,
  MESON_TAC[IN_RADICALS_SMALLER; LT_REFL]);;
```

### Informal statement
For any expression $r$, $r$ is not contained in the set of radicals of $r$. Formally:

$$\forall r. r \not\in \text{radicals}(r)$$

Where $\text{radicals}(r)$ represents the set of expressions that appear under square roots in the expression $r$.

### Informal proof
This theorem follows directly from the theorem `IN_RADICALS_SMALLER`, which states that if $s \in \text{radicals}(r)$, then $\text{depth}(s) < \text{depth}(r)$.

If we assume that $r \in \text{radicals}(r)$, then by `IN_RADICALS_SMALLER`, we would have $\text{depth}(r) < \text{depth}(r)$, which contradicts the reflexivity of the less-than relation (a number cannot be less than itself).

Therefore, $r \not\in \text{radicals}(r)$.

### Mathematical insight
This theorem establishes an important structural property of expressions with radicals: an expression cannot be a radical of itself. This is a foundational result that prevents circular definitions in the structure of algebraic expressions.

In the context of constructible numbers, this theorem confirms that we don't have pathological cases where an expression appears within its own radical decomposition, which could lead to circular reasoning when analyzing the structure of algebraic expressions.

The result might seem obvious intuitively, but formalizing it is essential for rigorous treatment of expressions involving radicals and their properties.

### Dependencies
- **Theorems**:
  - `IN_RADICALS_SMALLER`: If $s \in \text{radicals}(r)$, then $\text{depth}(s) < \text{depth}(r)$
  - `LT_REFL`: The less-than relation is irreflexive (implied in the proof)

- **Definitions**:
  - `radicals`: Defines the set of expressions that appear under square roots in an expression

### Porting notes
When porting this theorem to other proof assistants, the key is ensuring that:
1. The representation of expressions and the definition of `radicals` is properly set up
2. The depth function for expressions is similarly defined
3. The irreflexivity of the less-than relation is available

The proof is straightforward once these components are in place.

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
For any expression $e$, if $e$ is well-formed and contains no radicals (i.e., $\text{radicals}(e) = \emptyset$), then the value of $e$ is a rational number.

### Informal proof
The proof proceeds by induction on the structure of expressions.

* We start by applying induction on the expression structure using `MATCH_MP_TAC expression_INDUCT`.

* We then unfold the definitions of `wellformed`, `value`, and `radicals` and simplify using rewriting tactics `REWRITE_TAC` with the facts that the union of empty sets is empty (`EMPTY_UNION`), and that an insertion operation cannot result in the empty set (`NOT_INSERT_EMPTY`).

* For each case in the induction, we need to show that if the expression has no radicals, its value is rational:
  - For `Constant x`: From `wellformed(Constant x)`, we know that `x` is rational, so `value(Constant x) = x` is rational.
  - For `Negation e`, `Inverse e`, `Addition e1 e2`, and `Multiplication e1 e2`: If the subexpressions have no radicals and are rational, then their combinations remain rational by the properties of rational numbers.
  - For `Sqrt e`: This case is vacuously true, since `radicals(Sqrt e) = e INSERT (radicals e)` cannot be empty.

* The final step applies `RATIONAL_CLOSED`, which provides the closure properties of rational numbers (under addition, subtraction, multiplication, division, etc.), to complete the proof that operations on rational values result in rational values.

### Mathematical insight
This theorem establishes that expressions without square roots always evaluate to rational numbers, which is fundamental in the theory of constructible numbers. In particular, this shows that the class of rational numbers is precisely characterized by expressions that don't involve any radical operations.

In a broader context, this result helps lay the groundwork for understanding which numbers can be constructed using only arithmetic operations, and which require the introduction of square roots. It forms part of the foundation for studying constructible numbers in the context of classical geometric problems such as doubling the cube, trisecting an angle, and squaring the circle.

### Dependencies
#### Theorems
- `RATIONAL_CLOSED`: States that rational numbers are closed under various operations including addition, subtraction, multiplication, division, powers, negation, reciprocal, and absolute value.

#### Definitions
- `value`: Recursively defines the value of expressions (constants, negations, inverses, additions, multiplications, and square roots).
- `wellformed`: Defines when an expression is well-formed (e.g., no division by zero, square roots of non-negative values).
- `radicals`: Identifies the set of radical expressions contained in an expression.

### Porting notes
When porting this theorem to another proof assistant, ensure that:
1. The representation of expressions and their operations is properly defined
2. The induction principle for expressions is correctly established
3. The set operations like `UNION` and `INSERT` have equivalent definitions
4. The closure properties of rational numbers under various operations are established

The proof relies heavily on structural induction over expressions, which should be handled similarly in most proof assistants.

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
For any finite, non-empty set $s$ of natural numbers, there exists a maximum element $b \in s$ such that for all elements $a \in s$, we have $a \leq b$.

### Informal proof
The proof uses induction on finite sets:

- We apply the strong finite induction principle (`FINITE_INDUCT_STRONG`), which allows us to prove a property for all finite sets by showing it holds for the empty set and is preserved by element insertion.
- After simplifying with the fact that an inserted set is not empty (`NOT_INSERT_EMPTY`) and the definition of set membership (`IN_INSERT`), we consider two cases:
  - If $s = \emptyset$, then we can simplify using the fact that nothing belongs to the empty set (`NOT_IN_EMPTY`).
  - If $s \neq \emptyset$, we have an inductive case where we consider inserting a new element into a non-empty set.
- We use the unwind theorem (`UNWIND_THM2`) to simplify the existential statement.
- Finally, we appeal to basic properties of the order relation on natural numbers:
  - The trichotomy of the ordering relation (`LE_CASES`): for any natural numbers $a$ and $b$, either $a \leq b$ or $b \leq a$
  - Reflexivity of $\leq$ (`LE_REFL`): for any natural number $a$, $a \leq a$
  - Transitivity of $\leq$ (`LE_TRANS`): for any natural numbers $a$, $b$, and $c$, if $a \leq b$ and $b \leq c$, then $a \leq c$

The proof thus shows that given a non-empty finite set, we can always find its maximum element by comparing the newly inserted element with the maximum of the existing set.

### Mathematical insight
This theorem establishes the existence of a maximum element in any finite, non-empty set of natural numbers. It's a fundamental property that distinguishes finite sets from infinite ones (which may not have a maximum element). The result is used extensively in many areas of mathematics and computer science whenever we need to reason about bounds or extremal elements in finite collections.

The proof illustrates the power of induction on finite sets, showing how we can build up from simple cases to establish properties of more complex structures.

### Dependencies
- Theorems:
  - `FINITE_INDUCT_STRONG`: Strong induction principle for finite sets
  - `NOT_INSERT_EMPTY`: A set with an element inserted is not empty
  - `IN_INSERT`: Membership definition for inserted sets
  - `NOT_IN_EMPTY`: No element belongs to the empty set
  - `UNWIND_THM2`: Simplification theorem for existential quantifiers
  - `LE_REFL`: Reflexivity of the less-than-or-equal relation
  - `LE_CASES`: Totality of the order on natural numbers
  - `LE_TRANS`: Transitivity of the less-than-or-equal relation
  - `RIGHT_OR_DISTRIB`: Distributivity of disjunction
  - `EXISTS_OR_THM`: Distributivity of existential quantification over disjunction

### Porting notes
When porting to other systems:
- Ensure the target system has a strong induction principle for finite sets
- The proof relies on the totality of the order on natural numbers, which is standard but should be verified
- The `MESON_TAC` step at the end handles some reasoning about ordering relationships; you may need to make this reasoning more explicit in systems with different automation capabilities

---

## RADICAL_TOP

### RADICAL_TOP
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any expression $e$, if the set of radicals $\text{radicals}(e)$ is non-empty, then there exists a radical $r \in \text{radicals}(e)$ such that for all $s \in \text{radicals}(e)$, $r \notin \text{radicals}(s)$.

In other words, if an expression has any radicals at all, then at least one of these radicals is "maximal" in the sense that it doesn't appear inside any other radical of the expression.

### Informal proof
The proof identifies a maximal element based on the "depth" function:

1. We start with a non-empty set of radicals $\text{radicals}(e)$.

2. Consider the set $\{\text{depth}(r) \mid r \in \text{radicals}(e)\}$, which is the image of the depth function applied to all elements in $\text{radicals}(e)$.

3. By `FINITE_RADICALS`, we know that $\text{radicals}(e)$ is finite, which implies that the image of depths is also finite.

4. By `FINITE_MAX`, a finite non-empty set of natural numbers has a maximum element. So there exists some radical $r \in \text{radicals}(e)$ whose depth is maximal.

5. If $r$ were in $\text{radicals}(s)$ for some $s \in \text{radicals}(e)$, then by `IN_RADICALS_SMALLER`, we would have $\text{depth}(r) < \text{depth}(s)$.

6. But this contradicts the maximality of $\text{depth}(r)$.

7. Therefore, $r \notin \text{radicals}(s)$ for any $s \in \text{radicals}(e)$.

### Mathematical insight
This theorem identifies a "top-level" radical in an algebraic expression that contains nested radicals. It shows that there's always at least one radical that doesn't appear inside any other radical of the expression.

This property is important for structural induction on expressions containing radicals, as it identifies radicals that can be "eliminated first" in a systematic reduction process. In the theory of constructible numbers, this helps in showing that any computation involving nested radicals can be performed in a structured, terminating manner.

The theorem essentially provides a well-founded ordering on the radicals within an expression, which is crucial for proving termination in algorithms that manipulate such expressions.

### Dependencies
- Theorems:
  - `FINITE_RADICALS`: Shows that for any expression e, the set of radicals in e is finite
  - `IN_RADICALS_SMALLER`: If s is in the radicals of r, then the depth of s is less than the depth of r
  - `FINITE_MAX`: A finite non-empty set of natural numbers has a maximum element

- Definitions:
  - `radicals`: Defines the set of radical subexpressions within an expression
  - `depth`: Measures the nesting depth of an expression, particularly increasing for each Sqrt operation

### Porting notes
When porting this theorem:
1. Ensure that your target system has corresponding definitions for `radicals` and `depth` functions
2. The proof relies on well-founded induction on the depth measure, so verify that your target system has appropriate support for this reasoning pattern
3. The contradiction through `NOT_LT` depends on the properties of the ordering on natural numbers, which should be standard in most systems

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
For any expressions $e$ and $r$, if we assume that:
- Whenever $r \in \text{radicals}(e)$, there exist expressions $a$ and $b$ such that:
  - $a$ and $b$ are well-formed
  - $\text{value}(e) = \text{value}(a) + \text{value}(b) \cdot \sqrt{\text{value}(r)}$
  - $\text{radicals}(a) \subseteq \text{radicals}(e) \setminus \{r\}$
  - $\text{radicals}(b) \subseteq \text{radicals}(e) \setminus \{r\}$
  - $\text{radicals}(r) \subseteq \text{radicals}(e) \setminus \{r\}$
- And $e$ is well-formed

Then, there exist expressions $a$ and $b$ such that:
- $a$ and $b$ are well-formed
- $\text{value}(e) = \text{value}(a) + \text{value}(b) \cdot \sqrt{\text{value}(r)}$
- $\text{radicals}(a) \subseteq (\text{radicals}(e) \cup \text{radicals}(r)) \setminus \{r\}$
- $\text{radicals}(b) \subseteq (\text{radicals}(e) \cup \text{radicals}(r)) \setminus \{r\}$
- $\text{radicals}(r) \subseteq (\text{radicals}(e) \cup \text{radicals}(r)) \setminus \{r\}$

### Informal proof
The proof proceeds by case analysis on whether $r \in \text{radicals}(e)$ or not:

- **Case 1**: If $r \in \text{radicals}(e)$:
  * By the first assumption, there exist well-formed expressions $a$ and $b$ such that 
    $\text{value}(e) = \text{value}(a) + \text{value}(b) \cdot \sqrt{\text{value}(r)}$
    with the required subset conditions on the radicals.
  * These same $a$ and $b$ satisfy the conclusion, since 
    $\text{radicals}(e) \setminus \{r\} \subseteq (\text{radicals}(e) \cup \text{radicals}(r)) \setminus \{r\}$.
    This is proven using basic set theory.

- **Case 2**: If $r \not\in \text{radicals}(e)$:
  * We choose $a = e$ and $b = \text{Constant}(0)$.
  * $e$ is well-formed by assumption.
  * $\text{Constant}(0)$ is well-formed because rational numbers are well-formed, and $0$ is rational.
  * $\text{value}(e) = \text{value}(e) + \text{value}(\text{Constant}(0)) \cdot \sqrt{\text{value}(r)}$ 
    holds because $\text{value}(\text{Constant}(0)) = 0$ and $0 \cdot \sqrt{\text{value}(r)} = 0$.
  * For the subset conditions, we use the fact that $r \not\in \text{radicals}(e)$ and 
    $r \not\in \text{radicals}(r)$ (from the `NOT_IN_OWN_RADICALS` theorem).
  * This satisfies all the required conditions.

### Mathematical insight
This theorem establishes a canonical form for expressions involving radicals. It shows that any well-formed expression can be expressed in terms of a specific radical $r$ by writing it in the form $a + b\sqrt{r}$, where $a$ and $b$ are expressions that don't contain $r$ in their radicals.

This is particularly useful for inductive arguments about constructible numbers, as it allows us to express more complex expressions in a standard form where we've "factored out" a particular radical. The theorem covers both cases - when $r$ appears in the expression's radicals and when it doesn't.

The name "canonical trivial" suggests this is a basic building block for establishing canonical forms of expressions with nested radicals, which is crucial for analyzing constructible numbers.

### Dependencies
- Definitions:
  - `value`: Maps expressions to their real number values
  - `wellformed`: Defines when an expression is well-formed
  - `radicals`: Returns the set of radical expressions contained in an expression
- Theorems:
  - `RATIONAL_NUM`: Establishes that numeric literals are rational
  - `NOT_IN_OWN_RADICALS`: States that an expression is not in its own radicals set

### Porting notes
When porting this theorem:
1. Ensure your system has a corresponding mechanism to represent expressions with radicals
2. The DELETE operation in HOL Light corresponds to set difference - ensure your system has an equivalent notion
3. The proof relies heavily on set operations and tactics like SET_TAC - you may need to expand these into more elementary steps in systems with less powerful set automation

---

## RADICAL_CANONICAL

### RADICAL_CANONICAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any well-formed expression $e$ with non-empty radicals set, there exists a radical expression $r \in \text{radicals}(e)$ such that $e$ can be written in the canonical form $a + b\sqrt{\text{value}(r)}$, where:

- $a$ and $b$ are well-formed expressions
- $\text{value}(e) = \text{value}(a) + \text{value}(b) \cdot \sqrt{\text{value}(r)}$
- The radicals sets of $a$, $b$, and $r$ are all proper subsets of $\text{radicals}(e) \setminus \{r\}$

This means any well-formed expression with radicals can be rewritten to isolate one of its radicals as a top-level square root.

### Informal proof
The proof proceeds by structural induction on expressions:

1. First, we apply `RADICAL_TOP` to $e$, which gives us a radical expression $r \in \text{radicals}(e)$ that is maximal in the sense that $r$ is not contained in the radicals set of any other element of $\text{radicals}(e)$.

2. We establish that $r$ is well-formed and that $\text{value}(r) \geq 0$, which follows from `WELLFORMED_RADICALS` and `RADICALS_WELLFORMED`.

3. The proof then proceeds by induction on the structure of expressions:

   - For negation $e = \text{Negation}(e_1)$: If $e_1$ can be written as $a_1 + b_1\sqrt{\text{value}(r)}$, then $e = -e_1 = (-a_1) + (-b_1)\sqrt{\text{value}(r)}$.
   
   - For inverse $e = \text{Inverse}(e_1)$: If $e_1 = a_1 + b_1\sqrt{\text{value}(r)}$, we have two cases:
     * If $\text{value}(b_1) \cdot \sqrt{\text{value}(r)} = \text{value}(a_1)$, then $e_1 = 2 \cdot \text{value}(a_1)$ and $e = \text{Inverse}(2a_1)$.
     * Otherwise, we use the identity $(a + b\sqrt{r})^{-1} = \frac{a}{a^2 - b^2r} - \frac{b}{a^2 - b^2r}\sqrt{r}$

   - For addition $e = \text{Addition}(e_1, e_2)$: We apply the induction hypothesis to both $e_1$ and $e_2$, writing them in the form $a_i + b_i\sqrt{\text{value}(r)}$ for $i=1,2$. Then $e = (a_1 + a_2) + (b_1 + b_2)\sqrt{\text{value}(r)}$.
   
   - For multiplication $e = \text{Multiplication}(e_1, e_2)$: Similarly, applying the induction hypothesis to both operands and using the identity $(a_1 + b_1\sqrt{r})(a_2 + b_2\sqrt{r}) = (a_1a_2 + b_1b_2r) + (a_1b_2 + a_2b_1)\sqrt{r}$.
   
   - For square root $e = \text{Sqrt}(e_1)$: When $r = e$, we can directly represent $e$ as $0 + 1 \cdot \sqrt{\text{value}(r)}$.

4. At each step, we verify that the radicals of the constructed $a$ and $b$ expressions are proper subsets of $\text{radicals}(e) \setminus \{r\}$, using properties like `NOT_IN_OWN_RADICALS` and `RADICALS_SUBSET`.

### Mathematical insight
This theorem establishes a canonical form for expressions involving nested radicals. It demonstrates that any well-formed expression containing radicals can be rewritten to explicitly extract one of its radicals in the form $a + b\sqrt{r}$, where $a$ and $b$ are simpler expressions not containing $r$.

This result is fundamentally important for simplifying and normalizing radical expressions. It's part of the constructible number theory, showing how complex expressions with nested radicals can be systematically reduced to a canonical form. The theorem provides a structural induction approach to manipulating radical expressions, which is crucial for formalization of constructible numbers in geometric contexts.

In classical mathematics, this corresponds to the process of rationalizing denominators and simplifying radical expressions, but formalized in a rigorous, recursive manner.

### Dependencies
- Theorems:
  - `RATIONAL_NUM`: Every integer is rational
  - `WELLFORMED_RADICALS`: Elements in the radicals set of a well-formed expression have non-negative values
  - `RADICALS_WELLFORMED`: Elements in the radicals set of a well-formed expression are themselves well-formed
  - `RADICALS_SUBSET`: The radicals of any element in radicals(e) form a subset of radicals(e)
  - `NOT_IN_OWN_RADICALS`: No expression is in its own radicals set
  - `RADICAL_TOP`: For non-empty radicals, there exists a maximal element
  - `RADICAL_CANONICAL_TRIVIAL`: A technical lemma for the trivial case

- Definitions:
  - `value`: Evaluates the real value of an expression
  - `wellformed`: Defines when an expression is well-formed
  - `radicals`: Collects all the radical subexpressions

### Porting notes
When porting this theorem:
1. You'll need to first establish the expression datatype with constructors for each operation
2. Carefully handle the definitions of wellformed, value, and radicals functions
3. The proof relies heavily on set operations (SUBSET, DELETE, UNION, etc.) so ensure that your target system has good support for these operations
4. The mathematical proof structure is clearer than the HOL Light tactic script - implement the induction and case analysis according to the informal proof rather than trying to follow the tactic script exactly

---

## CUBIC_ROOT_STEP

### CUBIC_ROOT_STEP
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem states that for any rational coefficients $a$, $b$, and $c$, and for any well-formed expression $e$ with non-empty set of radicals (square roots) such that $(\text{value}(e))^3 + a \cdot (\text{value}(e))^2 + b \cdot \text{value}(e) + c = 0$, there exists another well-formed expression $e'$ with a strictly smaller set of radicals than $e$ (i.e., $\text{radicals}(e') \subset \text{radicals}(e)$) such that $(\text{value}(e'))^3 + a \cdot (\text{value}(e'))^2 + b \cdot \text{value}(e') + c = 0$.

In other words, if a cubic equation with rational coefficients has a solution expressible using nested square roots, then there exists a solution to the same equation that uses fewer square roots.

### Informal proof
The proof proceeds as follows:

* We start with a well-formed expression $e$ that contains at least one radical and satisfies the cubic equation.

* We apply the `RADICAL_CANONICAL` theorem to $e$. This gives us a radical $r \in \text{radicals}(e)$ and expressions $e_u$ and $e_v$ such that:
  - $\text{value}(e) = \text{value}(e_u + e_v \cdot \sqrt{\text{value}(r)})$
  - The radicals in $e_u$, $e_v$, and $r$ are all subsets of $\text{radicals}(e) \setminus \{r\}$

* We then apply the `STEP_LEMMA_SQRT` theorem with a specific predicate $P(x)$ defined as: "there exists a well-formed expression $e_x$ such that $\text{radicals}(e_x) \subseteq \text{radicals}(e) \setminus \{r\}$ and $\text{value}(e_x) = x$".

* We verify that this predicate satisfies all the conditions required by `STEP_LEMMA_SQRT`:
  1. $P(n)$ holds for all integers $n$ (using the constant expression)
  2. If $P(x)$ holds, then $P(-x)$ holds (using negation)
  3. If $P(x)$ holds and $x \neq 0$, then $P(1/x)$ holds (using inverse)
  4. If $P(x)$ and $P(y)$ hold, then $P(x+y)$ holds (using addition)
  5. If $P(x)$ and $P(y)$ hold, then $P(x \cdot y)$ holds (using multiplication)

* After verifying all these conditions, `STEP_LEMMA_SQRT` gives us an expression $e'$ such that:
  - $P(\text{value}(e'))$ holds, which means $\text{radicals}(e') \subseteq \text{radicals}(e) \setminus \{r\}$
  - $\text{value}(e')$ satisfies the same cubic equation as $\text{value}(e)$

* Since $r \in \text{radicals}(e)$ but $r \notin \text{radicals}(e')$, we have $\text{radicals}(e') \subset \text{radicals}(e)$, which completes the proof.

### Mathematical insight
This theorem is a crucial step in proving that solutions to cubic equations can always be expressed using only arithmetic operations and square roots, following the classical approach of Cardano's formula. The key insight is that we can systematically eliminate radicals one by one while maintaining the solution property.

The theorem provides an inductive step in a constructive proof: given any solution to a cubic equation that involves nested square roots, we can find a simpler solution with fewer radicals. By repeatedly applying this step, we can eventually reach a solution with minimal complexity.

This result is part of a broader investigation into constructible numbers and which algebraic numbers can be expressed using only square roots, which has connections to classical geometric problems like angle trisection and doubling the cube.

### Dependencies
- **Theorems**:
  - `RATIONAL_NUM`: Proves that for any natural number n, &n (the real representation of n) is rational.
  - `STEP_LEMMA_SQRT`: A key lemma that allows extending field properties to expressions involving square roots.
  - `RADICAL_CANONICAL`: Shows that any well-formed expression with radicals can be put in a canonical form u + v⋅√r.

- **Definitions**:
  - `value`: Defines the semantic value of expressions.
  - `wellformed`: Defines when expressions are well-formed.
  - `radicals`: Defines the set of radicals (square roots) used in an expression.

### Porting notes
When porting this theorem:
1. You'll need to first implement the representation of algebraic expressions as inductive data types.
2. The notion of "wellformed" expressions should include type safety as well as domain constraints (e.g., no division by zero).
3. The strict subset relation (PSUBSET) is crucial for the termination argument in the full proof.
4. Most proof assistants will require explicit termination arguments when using this as part of a recursive algorithm.

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
For all real numbers $a$, $b$, and $c$ where $a$, $b$, and $c$ are rational:

For any natural number $n$ and expression $e$ such that:
- $e$ is well-formed
- The cardinality of the set of radicals in $e$ is $n$
- $(\text{value}(e))^3 + a \cdot (\text{value}(e))^2 + b \cdot \text{value}(e) + c = 0$

Then there exists a rational number $x$ such that:
- $x^3 + a \cdot x^2 + b \cdot x + c = 0$

### Informal proof
We prove this theorem using well-founded induction on the cardinality of the set of radicals in the expression $e$.

For a cubic equation with rational coefficients $a$, $b$, and $c$, and a well-formed expression $e$ whose value is a root of this equation:

* First, we apply well-founded induction on the number of radicals in $e$.
* Given an expression $e$ with $n$ radicals that satisfies the cubic equation, we consider two cases:
  * **Base case**: If the set of radicals in $e$ is empty (i.e., $\text{radicals}(e) = \{\}$), then by the theorem `RADICALS_EMPTY_RATIONAL`, the value of $e$ is rational. So we already have a rational root of the cubic equation.
  * **Inductive step**: If the set of radicals is non-empty, we apply the theorem `CUBIC_ROOT_STEP` to $e$. This theorem states that given an expression $e$ whose value is a root of a cubic equation with rational coefficients, we can find another expression $e'$ with strictly fewer radicals whose value is also a root of the same cubic equation.
  
* Since $e'$ has a strictly smaller set of radicals (i.e., $\text{radicals}(e') \subset \text{radicals}(e)$), we apply the theorem `CARD_PSUBSET` to show that $\text{CARD}(\text{radicals}(e')) < \text{CARD}(\text{radicals}(e))$.
* By the induction hypothesis, there exists a rational value $x$ satisfying the cubic equation.

### Mathematical insight
This theorem is fundamental in the theory of constructible numbers and proves that a cubic equation with rational coefficients always has a rational root if it has a root that can be expressed using field operations and square roots (i.e., a constructible root).

This is part of a larger narrative in field theory that examines which algebraic numbers can be expressed using certain operations. While quadratics can be solved using square roots, cubics generally require cube roots. This theorem identifies the special case where a cubic actually has a rational solution.

The proof technique uses a clever induction on the complexity of radical expressions, systematically reducing the number of radical terms needed to express a root until reaching a purely rational expression.

### Dependencies
- **Theorems**:
  - `FINITE_RADICALS`: Shows that for any expression $e$, the set of radicals in $e$ is finite.
  - `RADICALS_EMPTY_RATIONAL`: If an expression $e$ is well-formed and has no radicals, then its value is rational.
  - `CUBIC_ROOT_STEP`: Provides the inductive step by showing that for a cubic equation with rational coefficients, given a root expressed as an expression $e$ with radicals, we can find another expression $e'$ with fewer radicals that is also a root.

- **Definitions**:
  - `value`: Defines the value of expressions (constants, negations, inverses, additions, multiplications, square roots).
  - `wellformed`: Defines when an expression is well-formed (i.e., semantically valid).
  - `radicals`: Defines the set of radicals in an expression.

### Porting notes
When porting this theorem:
1. Ensure the underlying theory of expressions with radicals is properly defined, including the notions of well-formedness and value evaluation.
2. The dependency on well-founded induction over natural numbers (`num_WF`) will need to be supported in the target system.
3. The proof relies heavily on theorems about set cardinality, particularly for finite sets - ensure these are available.
4. The induction strategy may need adjustment depending on how well-founded induction is formalized in the target system.

---

## CUBIC_ROOT_RATIONAL

### CUBIC_ROOT_RATIONAL
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For all real numbers $a$, $b$, and $c$ that are rational, if there exists a radical number $x$ such that $x^3 + ax^2 + bx + c = 0$, then there also exists a rational number $x$ that satisfies the same cubic equation $x^3 + ax^2 + bx + c = 0$.

Here, a "radical number" refers to a number that can be expressed using a well-formed radical expression.

### Informal proof
The proof proceeds as follows:

1. We first rewrite the statement using the theorem `RADICAL_EXPRESSION`, which states that a number $x$ is radical if and only if there exists a well-formed expression $e$ such that $x = \text{value}(e)$.

2. After stripping the assumptions, we apply the theorem `CUBIC_ROOT_RADICAL_INDUCT` to $a$, $b$, and $c$.

3. The induction theorem states that for rational $a$, $b$, and $c$, if there is a well-formed expression $e$ with a finite set of radicals such that $\text{value}(e)$ satisfies the cubic equation, then there exists a rational number $x$ satisfying the same cubic equation.

4. We provide the cardinality of the set of radicals in $e$ and the expression $e$ itself as the induction parameters.

5. The conclusion follows by applying modus ponens with our assumptions.

This proof essentially shows that any cubic equation with rational coefficients that has a radical solution must also have a rational solution.

### Mathematical insight
This theorem is significant in the theory of constructible numbers and field extensions. It demonstrates that cubic equations with rational coefficients have a special property: if they have any solution that can be expressed using radicals, then they must also have a rational solution.

This result is related to classical Galois theory and the work of Cardano on solving cubic equations. It shows that for cubic polynomials with rational coefficients, the existence of a solution expressible using radicals implies the existence of a rational root.

The result is somewhat surprising because, in general, the roots of cubic polynomials with rational coefficients can be irrational (and often are). This theorem identifies a special case where a rational root must exist.

### Dependencies
- Theorems:
  - `RADICAL_EXPRESSION`: Characterizes radical numbers as those expressible by well-formed expressions
  - `CUBIC_ROOT_RADICAL_INDUCT`: The induction principle for cubic roots of radical expressions

- Definitions:
  - `radicals`: A function that collects all radical subexpressions in an expression

### Porting notes
When porting this theorem:
1. Ensure your target system has a well-developed theory of radical expressions and rational numbers
2. The induction principle `CUBIC_ROOT_RADICAL_INDUCT` is crucial and may require significant effort to port
3. The notion of "well-formed expression" and "value" of an expression should be properly defined in your target system
4. The representation of the set of radicals and its cardinality may differ between systems

---

## CUBIC_ROOT_INTEGER

### CUBIC_ROOT_INTEGER
- `CUBIC_ROOT_INTEGER`

### Type of the formal statement
- theorem

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
For all real numbers $a$, $b$, and $c$, if $a$, $b$, and $c$ are integers and there exists a radical number $x$ such that $x^3 + ax^2 + bx + c = 0$, then there exists an integer $x$ such that $x^3 + ax^2 + bx + c = 0$.

Here:
- "integer" means a real number that is an integer
- "radical" refers to numbers constructible within the field of radical expressions

### Informal proof
The proof proceeds as follows:

1. First, we apply the theorem `CUBIC_ROOT_RATIONAL` which states that if a cubic polynomial with rational coefficients has a radical root, then it also has a rational root.

2. We use `RATIONAL_INTEGER` to convert the premise that $a$, $b$, and $c$ are integers to the fact that they are also rational numbers.

3. Finally, we use `RATIONAL_ROOT_INTEGER` which states that if a monic cubic polynomial with integer coefficients has a rational root, then that root must actually be an integer.

4. The result follows by combining these facts using modus ponens.

### Mathematical insight
This theorem is a special case of the rational root theorem from algebra, applied to cubic polynomials. It shows that if a monic cubic polynomial with integer coefficients has any radical root (which includes roots expressible using radicals), then it must also have an integer root.

This result is significant because it establishes that for cubic polynomials with integer coefficients, the existence of a solution in the larger field of radical expressions implies the existence of a much simpler solution in the integers. This connection between different number systems is a fundamental principle in algebraic number theory.

### Dependencies
- **Theorems**:
  - `RATIONAL_INTEGER`: If a real number is an integer, then it is rational.
  - `CUBIC_ROOT_RATIONAL`: If a cubic polynomial with rational coefficients has a radical root, it also has a rational root.
  - `RATIONAL_ROOT_INTEGER`: If a monic cubic polynomial with integer coefficients has a rational root, then that root must be an integer.

### Porting notes
When porting this theorem to other systems, ensure that:
1. The notions of "integer", "rational", and "radical" are properly defined
2. The dependency theorems are available or proven first
3. The monic nature of the polynomial is properly handled in the system's type constraints

---

## length

### length

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let length = new_definition
  `length(a:real^2,b:real^2) = norm(b - a)`;;
```

### Informal statement
The function `length` is defined as:

For two points $a$ and $b$ in $\mathbb{R}^2$, the length between them is:

$$\text{length}(a, b) = \|b - a\|$$

where $\|\cdot\|$ denotes the norm (Euclidean distance) in $\mathbb{R}^2$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition formalizes the standard Euclidean distance between two points in a 2D plane. It represents the straight-line distance from point $a$ to point $b$ using the norm of the difference vector $b-a$.

The length function serves as a foundational concept in computational geometry, allowing for the calculation of distances between points, which is essential for many geometric constructions and proofs. This definition is used in various geometric theorems involving distances, triangles, circles, and other plane figures.

Note that this definition uses the norm function, which for vectors in $\mathbb{R}^2$ computes $\|v\| = \sqrt{v_1^2 + v_2^2}$, the Euclidean norm.

### Dependencies
#### Definitions
- `norm`: The Euclidean norm of a vector

### Porting notes
When porting to other systems, ensure that:
1. The vector type `real^2` is properly represented
2. The norm function is available with the same behavior as in HOL Light
3. The subtraction operation on vectors is properly defined

Depending on the target system, you may need to use different notation for the vector type or explicitly import vector space libraries.

---

## parallel

### parallel
- `parallel`

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let parallel = new_definition
 `parallel (a:real^2,b:real^2) (c:real^2,d:real^2) <=>
        (a$1 - b$1) * (c$2 - d$2) = (a$2 - b$2) * (c$1 - d$1)`;;
```

### Informal statement

The definition states that two line segments are parallel if and only if their direction vectors are proportional.

Specifically, for line segments from point $a$ to point $b$ and from point $c$ to point $d$ in $\mathbb{R}^2$, the segments are parallel if and only if:
$$(a_1 - b_1)(c_2 - d_2) = (a_2 - b_2)(c_1 - d_1)$$

where $a_i$ denotes the $i$-th component of point $a$.

### Informal proof
This is a definition, so there is no proof.

### Mathematical insight
This definition captures the mathematical notion of parallel line segments in a coordinate-based approach. Two line segments in $\mathbb{R}^2$ are parallel if their direction vectors are scalar multiples of each other. 

The definition uses a cross-product-like relation to check this: if we have direction vectors $(a_1 - b_1, a_2 - b_2)$ and $(c_1 - d_1, c_2 - d_2)$, then they are parallel if and only if:
$$(a_1 - b_1)(c_2 - d_2) = (a_2 - b_2)(c_1 - d_1)$$

This is equivalent to saying that their cross product is zero, which means one is a scalar multiple of the other.

The definition avoids explicit checks for zero vectors, so care should be taken when using this definition with degenerate line segments (where the endpoints are the same point).

### Dependencies
None explicitly mentioned in the provided information.

### Porting notes
When porting this definition to other proof assistants:
- Ensure that the type of points is correctly defined as 2D vectors
- The definition uses 1-indexed components (e.g., `a$1` for the first component), which may need adjustment in systems with 0-indexed vectors
- Consider whether the target system needs additional constraints for degenerate cases where line segments reduce to points

---

## collinear3

### collinear3
- collinear3

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let collinear3 = new_definition
  `collinear3 (a:real^2) b c <=> parallel (a,b) (a,c)`;;
```

### Informal statement
Three points $a$, $b$, and $c$ in $\mathbb{R}^2$ are collinear (i.e., lie on a straight line) if and only if the vectors from $a$ to $b$ and from $a$ to $c$ are parallel.

Formally, for any three points $a, b, c \in \mathbb{R}^2$:
$\text{collinear3}(a, b, c) \iff \text{parallel}((a, b), (a, c))$

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition characterizes collinearity of three points in terms of vector parallelism. When three points lie on the same line, the vectors from any one of these points to each of the other two must be parallel (differing only by a scalar factor).

The definition chooses point $a$ as the reference point and checks if the vectors $(a,b)$ and $(a,c)$ are parallel. This is mathematically equivalent to checking if the vectors $b-a$ and $c-a$ are linearly dependent, which is a standard way to define collinearity in vector geometry.

This definition provides a direct computational method for determining collinearity, as parallelism of vectors can be checked using cross products or by verifying if one vector is a scalar multiple of the other.

### Dependencies
- Definitions:
  - `parallel` (implicit dependency, likely defines when two vector pairs are parallel)

### Porting notes
When porting to other proof assistants:
- Ensure the target system has a suitable definition of vector parallelism
- Note that this definition uses pairs of points $(a,b)$ to represent vectors, rather than explicit vector differences $b-a$
- Some systems might prefer defining collinearity using determinants or cross products

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
The point $p$ is said to be an intersection of the lines determined by points $(a,b)$ and $(c,d)$ if and only if:
1. $p$ is collinear with points $a$ and $b$, and
2. $p$ is collinear with points $c$ and $d$.

Formally, $\text{is\_intersection}(p, (a,b), (c,d)) \Leftrightarrow \text{collinear3}(a,p,b) \wedge \text{collinear3}(c,p,d)$, where $p, a, b, c, d$ are points in $\mathbb{R}^2$.

### Informal proof
This is a definition, so no proof is provided.

### Mathematical insight
This definition formalizes the concept of an intersection point between two lines in a plane. Rather than defining a line as an algebraic equation, this definition uses a more geometric approach by specifying two points that determine each line.

The definition uses the `collinear3` predicate which is defined in terms of parallelism. Specifically, `collinear3 a p b` means that the vectors from `a` to `p` and from `a` to `b` are parallel, indicating that the three points lie on the same line.

This approach to defining intersections is useful in constructive geometry, where we're interested in determining whether a point can be constructed as the intersection of two lines, each given by two constructible points.

### Dependencies
#### Definitions
- `collinear3` - Defines when three points are collinear: `collinear3 (a:real^2) b c <=> parallel (a,b) (a,c)`

### Porting notes
When porting this definition to another system:
1. Ensure that the underlying concept of `collinear3` is properly established
2. Consider that this definition doesn't handle edge cases like when the two lines are parallel and don't intersect
3. Note that in some systems, it might be more natural to define lines directly and then define their intersections, rather than this approach using collinearity

---

## on_circle

### Name of formal statement
on_circle

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let on_circle = new_definition
 `on_circle x (centre,pt) <=> length(centre,x) = length(centre,pt)`;;
```

### Informal statement
A point $x$ lies on a circle with center $\text{centre}$ and passing through point $\text{pt}$ if and only if the distance from $x$ to $\text{centre}$ equals the distance from $\text{pt}$ to $\text{centre}$.

Formally:
$$\text{on\_circle}(x, (\text{centre}, \text{pt})) \iff \text{length}(\text{centre}, x) = \text{length}(\text{centre}, \text{pt})$$

where $\text{length}(p, q)$ represents the Euclidean distance between points $p$ and $q$.

### Informal proof
This is a definition, so no proof is required.

### Mathematical insight
This definition captures the fundamental property of a circle: all points on a circle are equidistant from the center. The definition represents a circle by specifying its center point and one point that lies on the circle, rather than using a center and radius formulation. This representation is useful in constructive geometry, allowing a circle to be defined by two points (center and a point on the circumference).

The definition is particularly useful in the context of constructible geometry, where it helps formalize which points can be constructed using compass and straightedge operations. The equidistance property encoded in this definition corresponds directly to the compass operation in geometric constructions.

### Dependencies
- **Definitions**:
  - `length`: Likely represents the Euclidean distance between two points

### Porting notes
When porting this definition to other proof assistants:
1. Ensure that the target system has a suitable definition of Euclidean distance (`length`).
2. Consider whether the target system represents circles differently (e.g., using center and radius instead of center and a point on the circle).
3. In some systems, it might be more natural to define a circle as a set of points rather than as a predicate, depending on the overall formalization approach to geometry.

---

## SQRT_CASES_LEMMA

### SQRT_CASES_LEMMA
- SQRT_CASES_LEMMA

### Type of the formal statement
- theorem

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
For any real numbers $x$ and $y$, if $y^2 = x$, then $0 \leq x$ and either $\sqrt{x} = y$ or $\sqrt{x} = -y$.

### Informal proof
The proof proceeds as follows:

- Start with the assumption that $y^2 = x$.
- Substitute this equality into the goal to obtain $0 \leq y^2$ and $(\sqrt{y^2} = y \lor \sqrt{y^2} = -y)$.
- For the first part, $0 \leq y^2$ follows immediately from the fact that any real square is non-negative.
- For the second part, we need to determine the possible values of $\sqrt{y^2}$.
- Consider the theorem `POW_2_SQRT` which states that $z^2 = (\sqrt{z^2})^2$ for any real $z$.
- Apply this theorem with $z = y$ to get $y^2 = (\sqrt{y^2})^2$.
- Apply the theorem again with $z = -y$ to get $(-y)^2 = (\sqrt{(-y)^2})^2$.
- Since $(-y)^2 = y^2$ (as squaring negates sign), we have $y^2 = (\sqrt{y^2})^2$ and $y^2 = (\sqrt{y^2})^2$.
- This means either $\sqrt{y^2} = y$ or $\sqrt{y^2} = -y$.
- Since $y^2 = x$, we conclude $\sqrt{x} = y$ or $\sqrt{x} = -y$.

### Mathematical insight
This lemma characterizes the relationship between square roots and squares. It formalizes the basic fact that if a number is a perfect square (i.e., $x = y^2$), then its square root is either the original number $y$ or its negative $-y$. This reflects the fundamental property of square roots having two possible values in the real number system, although by convention the principal (non-negative) square root is denoted by $\sqrt{x}$.

The lemma is particularly useful when reasoning about equations involving squares and square roots, providing a way to handle cases where you know a number is a perfect square but need to determine which value the square root takes.

### Dependencies
- `REAL_POW_2`: Defines the squaring operation for real numbers
- `REAL_LE_SQUARE`: States that the square of any real number is non-negative
- `POW_2_SQRT`: States that $x^2 = (\sqrt{x^2})^2$ for any real $x$
- `REAL_POW_NEG`: Handles powers of negative numbers
- Various arithmetic simplification tactics

### Porting notes
When implementing this in another system, be aware of the definition of square root being used. Most systems define $\sqrt{x}$ as the non-negative square root of $x$ when $x \geq 0$, and this lemma relies on that convention. Also, some systems might have built-in automation that can directly handle this kind of reasoning about square roots and squares.

---

## RADICAL_LINEAR_EQUATION

### RADICAL_LINEAR_EQUATION
- `RADICAL_LINEAR_EQUATION`

### Type of the formal statement
- theorem

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
For all real numbers $a$, $b$, and $x$, if $a$ and $b$ are radical numbers, at least one of them is non-zero (i.e., not both $a = 0$ and $b = 0$), and they satisfy the linear equation $ax + b = 0$, then $x$ is also a radical number.

### Informal proof
The proof shows that the solution to the linear equation $ax + b = 0$ is radical when $a$ and $b$ are radical numbers and at least one of them is non-zero.

1. First, we establish that $a \neq 0$ and $x = -b/a$.
   - This follows directly from the constraints, as we need $a \neq 0$ to solve for $x$.
   - When $a \neq 0$, we can solve the equation $ax + b = 0$ to get $x = -b/a$.

2. Once we know that $x = -b/a$, we can apply the `RADICAL_RULES` theorem, which states that:
   - The negative of a radical number is radical.
   - The quotient of two radical numbers is radical (when the denominator is non-zero).

3. Since $a$ and $b$ are radical, and $a \neq 0$, we know that $-b/a$ is radical from these rules.
   - $-b$ is radical because $b$ is radical.
   - The quotient $-b/a$ is radical because both $-b$ and $a$ are radical, and $a \neq 0$.

4. Therefore, $x$ is a radical number.

### Mathematical insight
This theorem establishes that the solution to a linear equation with radical coefficients is itself radical, which is an important result in the theory of constructible numbers. Radical numbers are those that can be constructed using the four basic arithmetic operations and taking square roots (possibly nested). This theorem shows that solutions to linear equations preserve the "radical" property.

The result is part of a broader investigation into which numbers are constructible with straightedge and compass in Euclidean geometry. Linear equations arise naturally in many geometric construction problems, and this theorem ensures that solving such equations stays within the field of radical numbers when the coefficients are radical.

### Dependencies
- Theorems:
  - `RADICAL_RULES`: Establishes the closure properties of radical numbers under various operations such as addition, negation, multiplication, division, powers, and square roots.

### Porting notes
When porting this theorem, ensure that:
1. The definition of "radical numbers" in the target system matches HOL Light's definition.
2. The field-solving automation in the target system is capable of handling the algebraic reasoning needed to demonstrate that $a \neq 0$ and $x = -b/a$ follow from the given conditions.
3. The appropriate rules about algebraic operations on radical numbers are available in the target system.

---

## RADICAL_SIMULTANEOUS_LINEAR_EQUATION

### RADICAL_SIMULTANEOUS_LINEAR_EQUATION
- `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`

### Type of the formal statement
- theorem

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
For all real numbers $a$, $b$, $c$, $d$, $e$, $f$, $x$, and $y$, if:
- $a$, $b$, $c$, $d$, $e$, and $f$ are radical numbers,
- the system is non-degenerate (i.e., $a \cdot e \neq b \cdot d$ or $a \cdot f \neq c \cdot d$ or $e \cdot c \neq b \cdot f$), and
- $a \cdot x + b \cdot y = c$ and $d \cdot x + e \cdot y = f$ (forming a system of two linear equations in two unknowns),

then both $x$ and $y$ are radical numbers.

### Informal proof
We prove that if $(x,y)$ is the solution to the given system of linear equations, then $x$ and $y$ are both radical numbers.

First, we establish that the determinant of the system is non-zero and find the explicit solution using Cramer's rule:

- The determinant is $a \cdot e - b \cdot d \neq 0$, which follows from the non-degeneracy condition.
- The solution is:
  - $x = \frac{e \cdot c - b \cdot f}{a \cdot e - b \cdot d}$
  - $y = \frac{a \cdot f - d \cdot c}{a \cdot e - b \cdot d}$

This is proved by applying the `REAL_FIELD` conversion, which handles the algebraic manipulation automatically.

Once we have the explicit expressions for $x$ and $y$, we use `RADICAL_RULES` to conclude that $x$ and $y$ are radical numbers. This follows because:
- The numerators and denominators are algebraic combinations of radical numbers
- The set of radical numbers is closed under addition, subtraction, multiplication, and division (when the denominator is non-zero)

### Mathematical insight
This theorem establishes an important closure property of radical numbers: the solution to a system of linear equations with radical coefficients is itself a radical number, provided the system is non-degenerate.

The result is a natural extension of the fact that radical numbers form a field. It shows that linear algebra operations preserve the property of being a radical number, which is important for constructible number theory.

The proof uses Cramer's rule to express the solutions explicitly, then applies the algebraic closure properties of radical numbers to show that these expressions are radical numbers.

### Dependencies
- `RADICAL_RULES`: Establishes closure properties of radical numbers under various operations, including addition, subtraction, multiplication, division, powers, and square roots of non-negative numbers.

### Porting notes
When porting this theorem:
1. Ensure your target system has a well-defined notion of radical numbers (constructible by compass and straightedge).
2. The proof relies heavily on algebraic manipulations that might require different tactics in other systems.
3. You may need to explicitly prove Cramer's rule for 2×2 systems if your target system doesn't have automation comparable to `REAL_FIELD`.

---

## RADICAL_QUADRATIC_EQUATION

### RADICAL_QUADRATIC_EQUATION
- This is the name of the theorem `RADICAL_QUADRATIC_EQUATION` in HOL Light.

### Type of the formal statement
- theorem

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
Let $a$, $b$, $c$, and $x$ be real numbers such that:
1. $a$, $b$, and $c$ are radical numbers
2. $ax^2 + bx + c = 0$
3. It is not the case that $a = 0$ and $b = 0$ and $c = 0$ (i.e., at least one of them is non-zero)

Then $x$ is a radical number.

Here, a "radical number" is a real number that can be constructed from the rationals using the field operations and taking square roots.

### Informal proof
The proof proceeds by analyzing two cases: when $a = 0$ and when $a \neq 0$.

**Case 1**: When $a = 0$
- The quadratic equation simplifies to $bx + c = 0$
- This is a linear equation, and we can apply `RADICAL_LINEAR_EQUATION` directly to conclude that $x$ is a radical number

**Case 2**: When $a \neq 0$
- We prove that $x$ satisfies a linear equation with radical coefficients
- Specifically, we apply `RADICAL_LINEAR_EQUATION` with coefficients $2a$ and either $(b - \sqrt{b^2 - 4ac})$ or $(b + \sqrt{b^2 - 4ac})$
- We show that $x$ satisfies either:
  * $(2a)x + (b - \sqrt{b^2 - 4ac}) = 0$, or
  * $(2a)x + (b + \sqrt{b^2 - 4ac}) = 0$
- This follows from applying the quadratic formula to $ax^2 + bx + c = 0$
- We verify that $b^2 - 4ac \geq 0$ and that the discriminant $\sqrt{b^2 - 4ac}$ is a radical number
- Since $2a$ and $(b \pm \sqrt{b^2 - 4ac})$ are radical numbers, we can apply `RADICAL_LINEAR_EQUATION` to conclude that $x$ is a radical number

### Mathematical insight
This theorem demonstrates that the set of radical numbers is closed under taking roots of quadratic equations with radical coefficients. This is a fundamental result in the theory of constructible numbers in classical geometry, showing that if we can construct the coefficients of a quadratic equation with straightedge and compass, then we can also construct its roots.

The theorem corresponds to the geometric intuition that if we can construct $a$, $b$, and $c$, then we can construct the solutions to $ax^2 + bx + c = 0$ using only straightedge and compass. This follows from the fact that the quadratic formula only involves arithmetic operations and square roots.

This result is important for understanding which geometric constructions are possible using straightedge and compass, and which are not (like trisecting an arbitrary angle or doubling a cube).

### Dependencies
- `RADICAL_RULES`: Various closure properties of radical numbers
- `SQRT_CASES_LEMMA`: If $y^2 = x$, then $x \geq 0$ and $\sqrt{x} = y$ or $\sqrt{x} = -y$
- `RADICAL_LINEAR_EQUATION`: Solutions to linear equations with radical coefficients are radical numbers

### Porting notes
When porting this theorem:
1. Ensure the definition of "radical numbers" is properly set up in your target system
2. The proof relies heavily on the quadratic formula, so you may need to verify or develop this result in your target system
3. The case analysis (when $a = 0$ and when $a \neq 0$) is a common structure that should translate well to other systems
4. The `RADICAL_TAC` used in the original proof is a custom tactic - in your target system, you may need to manually prove that the expressions are radical numbers by applying the closure properties

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
For all real numbers $a$, $b$, $c$, $d$, $e$, $f$, and $x$, if:
- $a$, $b$, $c$, $d$, $e$, and $f$ are radical numbers
- It is not the case that $d = 0$ and $e = 0$ and $f = 0$ simultaneously
- The point $(x,y)$ satisfies the system of equations:
  - $(x - a)^2 + (y - b)^2 = c$ (a circle centered at $(a,b)$ with radius $\sqrt{c}$)
  - $d \cdot x + e \cdot y = f$ (a straight line)

Then both $x$ and $y$ are radical numbers.

### Informal proof
We need to show that the coordinates $(x,y)$ of the intersection points between a circle and a line are radical numbers when the parameters defining both curves are radical.

The proof works by substituting the linear equation into the circle equation to obtain a quadratic equation in one variable, and then applying the theorem about quadratic equations having radical solutions when their coefficients are radical.

Let's first recall that the system of equations is:
- $(x - a)^2 + (y - b)^2 = c$ (circle)
- $d \cdot x + e \cdot y = f$ (line)

We solve this system by considering two cases depending on whether $d$ or $e$ is non-zero (at least one must be non-zero by our assumption).

**Case 1:** When we solve for $x$ in terms of $y$:
From the linear equation, if $d \neq 0$, we can express $x = \frac{f - e \cdot y}{d}$. Substituting this into the circle equation:
$((\frac{f - e \cdot y}{d}) - a)^2 + (y - b)^2 = c$

This simplifies to a quadratic equation in $y$ of the form:
$(d^2 + e^2) \cdot y^2 + (2b \cdot d \cdot e - 2a \cdot e^2 - 2d \cdot f) \cdot y + (b^2 \cdot e^2 + a^2 \cdot e^2 + f^2 - c \cdot e^2 - 2b \cdot e \cdot f) = 0$

The coefficients of this quadratic are:
- $A = d^2 + e^2$ (which is non-zero since $(d,e) \neq (0,0)$)
- $B = 2b \cdot d \cdot e - 2a \cdot e^2 - 2d \cdot f$
- $C = b^2 \cdot e^2 + a^2 \cdot e^2 + f^2 - c \cdot e^2 - 2b \cdot e \cdot f$

All these coefficients are radical numbers since they're composed of sums, differences, products, and powers of the original radical parameters. By the theorem `RADICAL_QUADRATIC_EQUATION`, since the quadratic equation has radical coefficients, its solution $y$ must be radical.

**Case 2:** Similarly, we can solve for $y$ in terms of $x$ when $e \neq 0$, leading to another quadratic equation in $x$ with radical coefficients:
$(d^2 + e^2) \cdot x^2 + (2a \cdot d \cdot e - 2b \cdot d^2 - 2f \cdot e) \cdot x + (a^2 \cdot d^2 + b^2 \cdot d^2 + f^2 - c \cdot d^2 - 2a \cdot d \cdot f) = 0$

Again, applying `RADICAL_QUADRATIC_EQUATION`, we conclude that $x$ is radical.

Once we know one coordinate is radical, we can use the linear equation to express the other coordinate in terms of the first, which preserves the radical property.

Therefore, both $x$ and $y$ are radical numbers.

### Mathematical insight
This theorem extends the classical result that quadratic equations with radical coefficients have radical solutions to geometric problems. It shows that the coordinates of intersection points between circles and lines in the Cartesian plane are constructible with straightedge and compass when the parameters defining these geometric objects are constructible.

This result is part of the broader mathematical theory of constructible numbers, which characterizes points in the plane that can be constructed using only straightedge and compass starting from the rational points. Radical numbers precisely capture this notion of constructibility.

The theorem elegantly demonstrates how algebraic properties (being a radical number) translate to geometric constructions. It's a direct application of the fundamental correspondence between analytical geometry and algebra established by Descartes.

### Dependencies
#### Theorems
- `RADICAL_QUADRATIC_EQUATION`: Proves that solutions to quadratic equations with radical coefficients are themselves radical.

#### Implicit
- `RADICAL_TAC`: A tactic that automates reasoning about radical numbers.
- `REAL_RING`: A conversion that proves equalities in real arithmetic.
- `REAL_SOS_EQ_0`: A theorem about sum-of-squares representation for equalities.

### Porting notes
When porting this theorem:
1. Ensure that your target system has a well-defined notion of radical/constructible numbers.
2. The proof relies heavily on algebraic manipulations. Most proof assistants have automation for polynomial arithmetic, but the specific approach may differ.
3. The case analysis in the proof might need to be made more explicit in systems with stricter logical foundations.
4. The algebraic substitutions produce complex expressions - computer algebra capabilities of the target system will determine how cleanly this can be ported.

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
For all real numbers $a$, $b$, $c$, $d$, $e$, $f$, $x$, and $y$:
If:
- $a$, $b$, $c$, $d$, $e$, and $f$ are radical numbers
- The circles are not identical: $(a, b, c) \neq (d, e, f)$
- $(x - a)^2 + (y - b)^2 = c$ (a circle with center $(a,b)$ and radius $\sqrt{c}$)
- $(x - d)^2 + (y - e)^2 = f$ (a circle with center $(d,e)$ and radius $\sqrt{f}$)

Then $x$ and $y$ are radical numbers.

Here, a "radical number" (represented by the predicate `radical`) is a real number that can be constructed from rational numbers using arithmetic operations and taking square roots.

### Informal proof
We prove that the intersection points of two circles with radical parameters have radical coordinates.

The proof reduces the problem of finding the intersection of two circles to solving a system of one circle and one linear equation, which can be handled by the theorem `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`.

We start with the two circle equations:
- $(x - a)^2 + (y - b)^2 = c$
- $(x - d)^2 + (y - e)^2 = f$

Expanding the second equation:
- $(x - d)^2 + (y - e)^2 = (x - a + a - d)^2 + (y - b + b - e)^2$
- $= (x - a)^2 + 2(x - a)(a - d) + (a - d)^2 + (y - b)^2 + 2(y - b)(b - e) + (b - e)^2$

Subtracting the first equation from this expanded form:
- $f = c + 2(x - a)(a - d) + (a - d)^2 + 2(y - b)(b - e) + (b - e)^2$

Rearranging:
- $2(d - a)x + 2(e - b)y = (d^2 - a^2) + (e^2 - b^2) + (c - f)$

This gives us a linear equation $2(d-a)x + 2(e-b)y = (d^2-a^2) + (e^2-b^2) + (c-f)$ along with our original circle equation $(x-a)^2 + (y-b)^2 = c$.

We can now apply `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC` with parameters:
- Circle center: $(a, b)$
- Circle radius squared: $c$
- Linear coefficients: $2(d-a)$, $2(e-b)$
- Linear constant: $(d^2-a^2) + (e^2-b^2) + (c-f)$

Since all these parameters are radical numbers (being combinations of radical numbers using arithmetic operations), and the linear equation is non-trivial (because the circles are not identical), `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC` guarantees that the solutions $x$ and $y$ are radical numbers.

### Mathematical insight
This theorem establishes an important result in the theory of constructible numbers: the coordinates of the intersection points of two circles with constructible parameters are themselves constructible. This is a fundamental result in the classical theory of geometric constructions with straightedge and compass.

The proof illustrates a common technique in computational geometry: reducing the problem of finding the intersection of two curves to solving a system with one of the original curves and a simpler curve (in this case, a line) derived from the second curve.

The theorem is part of the broader characterization of constructible numbers, which are precisely the radical numbers. This allows us to determine which geometric constructions are possible with straightedge and compass.

### Dependencies
#### Theorems
- `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`: Shows that the intersection points of a circle and a non-trivial line with radical parameters have radical coordinates
- `RADICAL_QUADRATIC_EQUATION` (inferred from dependencies but not directly visible in the code)
- `REAL_SOS_EQ_0` (inferred from dependencies but not directly visible in the code)

#### Tactics
- `RADICAL_TAC`: A custom tactic for proving that combinations of radical numbers are radical

### Porting notes
When porting this theorem:

1. Ensure your system has a proper definition of constructible/radical numbers
2. The proof relies on algebraic manipulations (`CONV_TAC REAL_RING`), so automation for ring-like structures would be helpful
3. If the target system has weaker automation for algebraic reasoning, the ring manipulations may need to be expanded
4. The condition that the circles are not identical (`~(a = d /\ b = e /\ c = f)`) is crucial for ensuring the derived linear equation is non-trivial

---

## constructible_RULES,constructible_INDUCT,constructible_CASES

### constructible_RULES, constructible_INDUCT, constructible_CASES

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
                   ==> constructible x)`;;
```

### Informal statement

The inductive definition `constructible` formally defines the class of constructible points in a plane as follows:

1. A point $x \in \mathbb{R}^2$ is constructible if both its coordinates are rational numbers: 
   $\forall x \in \mathbb{R}^2. \text{rational}(x_1) \land \text{rational}(x_2) \Rightarrow \text{constructible}(x)$

2. If $a, b, c, d$ are constructible points forming two non-parallel lines $ab$ and $cd$, and $x$ is their intersection point (such that $x$ is collinear with both $a,b$ and $c,d$), then $x$ is constructible:
   $\forall a,b,c,d,x. \text{constructible}(a) \land \text{constructible}(b) \land \text{constructible}(c) \land \text{constructible}(d) \land \lnot \text{parallel}(a,b)(c,d) \land \text{is\_intersection}(x)(a,b)(c,d) \Rightarrow \text{constructible}(x)$

3. If $a, b, c, d, e$ are constructible points where $a \neq b$, and $x$ lies on line $ab$ and is at distance $|de|$ from point $c$, then $x$ is constructible:
   $\forall a,b,c,d,e,x. \text{constructible}(a) \land \text{constructible}(b) \land \text{constructible}(c) \land \text{constructible}(d) \land \text{constructible}(e) \land a \neq b \land \text{collinear3}(a,x,b) \land \text{length}(c,x) = \text{length}(d,e) \Rightarrow \text{constructible}(x)$

4. If $a,b,c,d,e,f$ are constructible points forming two distinct circles (with centers $a$ and $d$, and radii $|bc|$ and $|ef|$ respectively), and $x$ is at distance $|bc|$ from $a$ and at distance $|ef|$ from $d$, then $x$ is constructible:
   $\forall a,b,c,d,e,f,x. \text{constructible}(a) \land \text{constructible}(b) \land \text{constructible}(c) \land \text{constructible}(d) \land \text{constructible}(e) \land \text{constructible}(f) \land \lnot(a = d \land \text{length}(b,c) = \text{length}(e,f)) \land \text{length}(a,x) = \text{length}(b,c) \land \text{length}(d,x) = \text{length}(e,f) \Rightarrow \text{constructible}(x)$

### Informal proof

This is an inductive definition that generates three theorems:
- `constructible_RULES`: The basic rules for constructing points
- `constructible_INDUCT`: An induction principle for proving properties of constructible points
- `constructible_CASES`: A case analysis principle for constructible points

As this is a definition rather than a theorem with a proof, there are no proof steps to translate.

### Mathematical insight

This definition formalizes the notion of constructible points in the Euclidean plane - points that can be constructed using only a straightedge (unmarked ruler) and compass. The definition captures the four fundamental operations in ruler-and-compass constructions:

1. All points with rational coordinates are constructible (providing a starting set of points)
2. The intersection of two non-parallel lines is constructible (captures straightedge constructions)
3. The intersection of a line and a circle is constructible (captures one type of compass construction)
4. The intersection of two distinct circles is constructible (captures another type of compass construction)

This analytical definition is equivalent to the classical geometric definition of constructibility and provides a foundation for proving important results about which geometric problems can or cannot be solved using only straightedge and compass. The definition aligns with the famous impossibility results (trisecting an angle, doubling a cube, squaring a circle) by providing a precise mathematical characterization of constructible points.

### Dependencies

#### Definitions
- `collinear3`: Three points $a, b, c$ are collinear if the segments $(a,b)$ and $(a,c)$ are parallel.
- `is_intersection`: A point $p$ is the intersection of segments $(a,b)$ and $(c,d)$ if $p$ is collinear with both $a,b$ and $c,d$.

### Porting notes

When porting to another system:
- Ensure that the inductive definition machinery properly handles the complex logical structure with multiple constructors.
- The definition relies on existing notions of parallelism, collinearity, and distance, which must be properly defined first.
- The system needs to handle 2D vectors and their operations, particularly the operations on coordinates denoted by `x$1` and `x$2`.
- In type-theoretic systems, you may need explicit type annotations for the vector space $\mathbb{R}^2$.

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
For points $a, b, c, d, x \in \mathbb{R}^2$, if all coordinates of points $a, b, c, d$ are radical numbers, the lines $(a,b)$ and $(c,d)$ are not parallel, and $x$ is the intersection point of these two lines, then the coordinates of $x$ are also radical numbers.

Formally, if:
- $a_1, a_2, b_1, b_2, c_1, c_2, d_1, d_2$ are radical numbers
- The lines through points $a$ and $b$ and through points $c$ and $d$ are not parallel
- $x$ is the intersection point of these two lines

Then both coordinates $x_1$ and $x_2$ are radical numbers.

### Informal proof
The proof shows that the coordinates of the intersection point can be expressed as solutions to a system of linear equations with radical coefficients.

- We begin by rewriting the definitions of `parallel`, `collinear3`, and `is_intersection`.
- Since $x$ is the intersection point of the lines $(a,b)$ and $(c,d)$, we can express this as a system of linear equations.
- We apply the theorem `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`, which states that solutions to a system of linear equations with radical coefficients are themselves radical numbers.
- We explicitly construct the coefficients for the linear system:
  - For the first line: $(b_2 - a_2)x_1 + (a_1 - b_1)x_2 = a_2(a_1 - b_1) - a_1(a_2 - b_2)$
  - For the second line: $(d_2 - c_2)x_1 + (c_1 - d_1)x_2 = c_2(c_1 - d_1) - c_1(c_2 - d_2)$
- These coefficients are radical numbers (as proven using `RADICAL_TAC`), since they are algebraic combinations of the coordinates of $a, b, c, d$.
- The non-parallel condition ensures that the system has a unique solution.
- The final step uses `CONV_TAC REAL_RING` to verify that the conditions for the application of `RADICAL_SIMULTANEOUS_LINEAR_EQUATION` are satisfied.

### Mathematical insight
This theorem is a fundamental result in coordinate geometry, establishing that the constructible nature of points is preserved under line intersection. It's particularly important in the context of constructible numbers and geometric constructions.

The result fits into the broader framework of constructible geometry, showing that intersections of lines with constructible endpoints yield constructible points. In the context of HOL Light's formalization of geometry, this theorem helps build more complex geometric constructions while maintaining the property that all points have radical (constructible) coordinates.

The theorem is canonical as it demonstrates a closure property: the set of points with radical coordinates is closed under the operation of line intersection.

### Dependencies
- **Theorems**
  - `RADICAL_SIMULTANEOUS_LINEAR_EQUATION`: States that solutions to linear equations with radical coefficients are themselves radical numbers

- **Definitions**
  - `collinear3`: Defines three points as collinear if the associated vectors are parallel
  - `is_intersection`: Defines a point as the intersection of two lines
  - `parallel`: (Implicitly used) Defines when two line segments are parallel

### Porting notes
When porting this theorem:
1. Ensure that the target system has a way to represent radical numbers and geometric points.
2. The theorem relies heavily on algebraic manipulation of real numbers - make sure your target system has good support for real arithmetic.
3. The proof uses `RADICAL_TAC`, which is a custom tactic for radical number manipulation - you may need to create an equivalent tactic or use a different approach.
4. The final part of the proof uses `CONV_TAC REAL_RING` which does automated reasoning about real arithmetic. You may need a similar automation tool in your target system, or you might need to expand some of these steps explicitly.

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
Let $a, b, c, d, e$ be points in $\mathbb{R}^2$ such that:
- The coordinates of $a$, $b$, $c$, $d$, and $e$ are radical numbers
- Points $a$ and $b$ are distinct
- Point $x$ is collinear with points $a$ and $b$
- The distance from $c$ to $x$ equals the distance from $d$ to $e$

Then the coordinates of point $x$ are also radical numbers.

### Informal proof
We start by unpacking the definitions of length and collinearity in terms of algebraic conditions:
- The length equality condition $\text{length}(c,x) = \text{length}(d,e)$ expands to: 
  $\|(c-x)\| = \|(d-e)\|$, which gives us
  $(c_1-x_1)^2 + (c_2-x_2)^2 = (e_1-d_1)^2 + (e_2-d_2)^2$

- The collinearity condition $\text{collinear3}(a,x,b)$ means that vectors $\overrightarrow{ax}$ and $\overrightarrow{ab}$ are parallel.
  This gives us a linear condition: $(b_2-a_2)(x_1-a_1) = (b_1-a_1)(x_2-a_2)$
  
  This can be rearranged to: $(b_2-a_2)x_1 - (b_1-a_1)x_2 = a_2(b_1-a_1) - a_1(b_2-a_2)$

So we have:
- A quadratic equation: $(x_1-c_1)^2 + (x_2-c_2)^2 = (e_1-d_1)^2 + (e_2-d_2)^2$
- A linear equation: $(b_2-a_2)x_1 - (b_1-a_1)x_2 = a_2(b_1-a_1) - a_1(b_2-a_2)$

Now we can apply the theorem `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`, which states that if we have a system with one linear and one quadratic equation where all coefficients are radical numbers, then the solutions are radical numbers.

We set:
- $a' = c_1$
- $b' = c_2$
- $c' = (e_1-d_1)^2 + (e_2-d_2)^2$
- $d' = b_2-a_2$
- $e' = a_1-b_1$
- $f' = a_2(a_1-b_1) - a_1(a_2-b_2)$

These are all radical numbers because the coordinates of $a, b, c, d, e$ are radical.

The linear equation $d'x_1 + e'x_2 = f'$ is non-trivial because $a$ and $b$ are distinct, so $(d',e')$ cannot be $(0,0)$.

By the theorem, we conclude that both $x_1$ and $x_2$ are radical numbers.

### Mathematical insight
This theorem establishes that the intersection points of a line and a circle are constructible by straightedge and compass if both the line and circle are defined by constructible points. The radical numbers correspond precisely to the points that can be constructed with straightedge and compass.

More specifically, this theorem says: if we have a line determined by two constructible points $a$ and $b$, and we want points on that line that are at a specified distance (equal to $|d-e|$) from another constructible point $c$, then such intersection points have constructible coordinates.

This is a fundamental result in constructible geometry, showing that the intersection of basic geometric objects preserves constructibility.

### Dependencies
- Theorems:
  - `RADICAL_SIMULTANEOUS_LINEAR_QUADRATIC`: States that if we have a system of one quadratic and one linear equation with radical coefficients, the solutions are radical numbers

- Definitions:
  - `collinear3`: Defines when three points are collinear, using the condition that vectors formed by the points are parallel

### Porting notes
When porting this theorem:
1. Ensure your system has a good representation of vectors/points in $\mathbb{R}^2$ with coordinate access
2. The proof relies on algebraic manipulations to convert geometric conditions into a system of equations
3. The underlying concept of radical/constructible numbers may be defined differently in other systems
4. The proof strategy involving the reduction to a simultaneous linear-quadratic system should be portable across most systems

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
Let $a, b, c, d, e, f, x$ be points in $\mathbb{R}^2$. If:
- The coordinates of $a, b, c, d, e, f$ are all radical numbers (i.e., for each point $p \in \{a,b,c,d,e,f\}$, both $p_1$ and $p_2$ are radical numbers)
- $\|a - x\| = \|b - c\|$ (i.e., $x$ lies on a circle centered at $a$ with radius equal to the distance between $b$ and $c$)
- $\|d - x\| = \|e - f\|$ (i.e., $x$ lies on a circle centered at $d$ with radius equal to the distance between $e$ and $f$)
- The two equations do not represent the same circle (i.e., it's not the case that $a = d$ and $\|b - c\| = \|e - f\|$)

Then both coordinates of $x$ are radical numbers (i.e., $x_1$ and $x_2$ are radical numbers).

### Informal proof
The theorem states that the intersection point of two circles has radical coordinates if all defining parameters (centers and points determining radii) have radical coordinates.

The proof proceeds as follows:

- We start by rewriting the distance conditions in terms of squared norms:
  $\|a - x\|^2 = \|b - c\|^2$ and $\|d - x\|^2 = \|e - f\|^2$
  
- Expanding the vector squared norms in terms of components, we get:
  $(x_1 - a_1)^2 + (x_2 - a_2)^2 = (c_1 - b_1)^2 + (c_2 - b_2)^2$
  $(x_1 - d_1)^2 + (x_2 - d_2)^2 = (f_1 - e_1)^2 + (f_2 - e_2)^2$

- This gives us a system of two quadratic equations in $x_1$ and $x_2$

- We then apply `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`, which states that the solutions to a system of two distinct quadratic equations with radical coefficients have radical coordinates

- We provide the appropriate values to match our system with the form required by `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`:
  * $a \mapsto a_1$, $b \mapsto a_2$, $c \mapsto \|c - b\|^2$
  * $d \mapsto d_1$, $e \mapsto d_2$, $f \mapsto \|f - e\|^2$

- Each of these values is verified to be a radical number using the assumption that all coordinates of points $a, b, c, d, e, f$ are radical

- The hypothesis that the circl es are distinct ensures we're not solving the same equation twice

The result follows directly from `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`.

### Mathematical insight
This theorem establishes an important result in the theory of constructible numbers: the coordinates of the intersection points of two circles with constructible parameters are themselves constructible. This is a fundamental result for compass and straightedge constructions in Euclidean geometry.

The result is part of a larger theory showing that the set of constructible points is closed under certain geometric operations. In particular, it shows that if we can construct the centers of two circles and points determining their radii, then we can also construct any intersection points of those circles.

This theorem connects to the classical problem of determining which geometric constructions are possible with compass and straightedge, as points with radical coordinates are precisely those that can be constructed from the rationals using these tools.

### Dependencies
- **Theorems**:
  - `RADICAL_SIMULTANEOUS_QUADRATIC_QUADRATIC`: Shows that solutions to systems of two distinct quadratic equations with radical coefficients have radical coordinates

- **Definitions**:
  - `collinear3`: Defines when three points are collinear
  - `length`: Euclidean distance between two points
  - `radical`: Defines radical numbers (constructible real numbers)

### Porting notes
When implementing this in other proof assistants:
- The key insight is converting the geometric problem of circle intersections into an algebraic problem of solving simultaneously quadratic equations
- Careful handling of the vector components and squared norms will be needed
- The implementation should rely on a corresponding result about solving systems of quadratic equations with radical coefficients

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
For any point $x$ in the Euclidean plane, if $x$ is constructible, then both coordinates of $x$ are radical numbers. That is:

$$\forall x. \text{constructible}(x) \Rightarrow \text{radical}(x_1) \land \text{radical}(x_2)$$

where $x_1$ and $x_2$ denote the first and second coordinates of the point $x$.

### Informal proof
We prove this by induction on the structure of constructible points using the induction principle `constructible_INDUCT`. The proof considers all possible ways to construct a point:

1. **Base case**: For points with rational coordinates, their coordinates are radical numbers by definition.

2. **Induction cases**:
   
   * **Line-line intersection**: If $x$ is constructed as the intersection of two lines defined by points with radical coordinates, then $x$ also has radical coordinates. This follows from `RADICAL_LINE_LINE_INTERSECTION`.
   
   * **Line-circle intersection**: If $x$ is constructed as an intersection point of a line and a circle, where all defining points have radical coordinates, then $x$ also has radical coordinates. This follows from `RADICAL_LINE_CIRCLE_INTERSECTION`.
   
   * **Circle-circle intersection**: If $x$ is constructed as an intersection point of two circles, where all defining points have radical coordinates, then $x$ also has radical coordinates. This follows from `RADICAL_CIRCLE_CIRCLE_INTERSECTION`.

In each inductive case, we apply the corresponding theorem and use the induction hypothesis that the coordinates of all previously constructed points are radical numbers.

### Mathematical insight
This theorem establishes a fundamental property of constructible points in Euclidean geometry: their coordinates must be radical numbers. This is a key step in formalizing the classical compass and straightedge construction problems from ancient Greek mathematics.

A radical number is a real number that can be expressed using rational numbers, the four basic arithmetic operations, and taking the square root of non-negative numbers. This theorem connects the geometric notion of constructibility with the algebraic property of being a radical number.

This connection between geometry and algebra is important for proving impossibility results like the trisection of an angle or doubling a cube, as it reduces geometric questions to algebraic ones.

### Dependencies
- `constructible_INDUCT`: The induction principle for constructible points
- `RADICAL_RULES`: Basic properties of radical numbers
- `RADICAL_LINE_LINE_INTERSECTION`: Theorem stating that the intersection of lines with radical coordinates yields a point with radical coordinates
- `RADICAL_LINE_CIRCLE_INTERSECTION`: Theorem stating that the intersection of a line and circle with radical coordinates yields a point with radical coordinates
- `RADICAL_CIRCLE_CIRCLE_INTERSECTION`: Theorem stating that the intersection of two circles with radical coordinates yields a point with radical coordinates

### Porting notes
When porting this theorem to other systems, ensure that:
1. The definition of "radical" numbers is consistent with the standard mathematical definition
2. The inductive structure of constructible points is properly defined
3. The necessary theorems about preserving "radical" coordinates under the various geometric constructions are available

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
There does not exist a constructible number $x$ (i.e., a radical number) such that $x^3 = 2$.

### Informal proof
To prove that no radical number $x$ can satisfy $x^3 = 2$, we proceed by contradiction:

* Suppose there exists a radical number $x$ such that $x^3 = 2$.
* We apply the theorem `CUBIC_ROOT_INTEGER` with $a = 0$, $b = 0$, and $c = -2$.
* This theorem states that if a cubic equation $x^3 + ax^2 + bx + c = 0$ has a radical root and has integer coefficients, then it also has an integer root.
* In our case, the cubic equation becomes $x^3 - 2 = 0$, which is equivalent to $x^3 = 2$.
* By our assumption, this equation has a radical root, and its coefficients (0, 0, and -2) are integers.
* Therefore, by `CUBIC_ROOT_INTEGER`, there must exist an integer $n$ such that $n^3 = 2$.
* Taking the absolute value of both sides: $|n|^3 = 2$.
* Since $n$ is an integer, $|n|$ is a natural number.
* But no natural number cubed equals 2: if $n ≤ 1$, then $n^3 ≤ 1 < 2$; if $n ≥ 2$, then $n^3 ≥ 8 > 2$.
* This is a contradiction, which completes the proof.

### Mathematical insight
This result is a special case of the classical "doubling the cube" problem from ancient Greek mathematics, which asks whether it's possible to construct a cube with twice the volume of a given cube using only a straightedge and compass. 

The result shows that this is impossible because the length of the side of such a cube would be $\sqrt[3]{2}$, which is not constructible. This is a significant example of a compass-and-straightedge construction problem that cannot be solved, along with trisecting an arbitrary angle and squaring the circle.

In algebraic terms, this theorem demonstrates that $\sqrt[3]{2}$ is not a radical number, meaning it cannot be expressed using any combination of the four basic operations and taking square roots. This result can be generalized: numbers constructible with straightedge and compass correspond exactly to radical numbers.

### Dependencies
#### Theorems:
- `INTEGER_CLOSED`: States closure properties of integers under various operations (addition, multiplication, subtraction, etc.)
- `CUBIC_ROOT_INTEGER`: If a cubic equation with integer coefficients has a radical root, then it also has an integer root.

### Porting notes
When porting this theorem:
1. Ensure the target system has a proper definition of radical (constructible) numbers
2. The proof relies on the basic number theory fact that no integer cubed equals 2
3. The theorem `CUBIC_ROOT_INTEGER` is a key dependency - make sure to port it first, as it's doing the heavy lifting in this proof

---

## DOUBLE_THE_CUBE

### DOUBLE_THE_CUBE
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
For any real number $x$, if $x^3 = 2$, then the point $(x, 0)$ in the Cartesian plane is not constructible with straightedge and compass.

### Informal proof
The proof is by contradiction. We assume that there exists an $x$ such that $x^3 = 2$ and the point $(x, 0)$ is constructible.

- By the theorem `CONSTRUCTIBLE_RADICAL`, if a point is constructible, then both of its coordinates are radical numbers (numbers that can be built from rational numbers using arithmetic operations and taking square roots of non-negative numbers).
- So, if the point $(x, 0)$ is constructible, then $x$ must be a radical number and $0$ is trivially a radical number.
- However, by the theorem `DOUBLE_THE_CUBE_ALGEBRA`, there cannot exist a radical number $x$ such that $x^3 = 2$.
- This contradiction shows that the point $(x, 0)$ cannot be constructible.

### Mathematical insight
This theorem formalizes the classical result known as the "doubling the cube" problem, one of the three famous ancient Greek construction problems. It proves the impossibility of constructing, using only straightedge and compass, a cube with twice the volume of a given cube.

The key insight is that constructible numbers form a field that is closed under square roots but not cube roots. A number is constructible if and only if it lies in a field extension of degree $2^n$ over the rationals. Since $\sqrt[3]{2}$ requires a field extension of degree 3, it cannot be expressed using only field operations and square roots, making it impossible to construct with straightedge and compass.

This result has significant historical importance as it resolved a problem that puzzled mathematicians for over two millennia.

### Dependencies
- Theorems:
  - `RADICAL_RULES`: Establishes closure properties of radical numbers under various operations.
  - `CONSTRUCTIBLE_RADICAL`: Shows that the coordinates of constructible points are radical numbers.
  - `DOUBLE_THE_CUBE_ALGEBRA`: Proves that there is no radical number $x$ such that $x^3 = 2$.

### Porting notes
When porting this theorem:
- Ensure that the target system has a well-defined notion of constructible points and radical numbers.
- The porting may require developing a theory of field extensions and their relationships to compass and straightedge constructions.
- The proof relies on algebraic results about the impossibility of representing certain cube roots using only square roots and field operations, which might need to be formalized separately.

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
For all real numbers $x$, we have:
$$\cos(3x) = 4\cos^3(x) - 3\cos(x)$$

This is an identity relating the cosine of a triple angle to powers of the cosine of the original angle.

### Informal proof
The proof proceeds as follows:

- We first rewrite the expression $3x$ as $x + x + x$ using real arithmetic.
- We then apply the cosine addition formula (`COS_ADD`) and sine addition formula (`SIN_ADD`) to expand $\cos(3x)$.
- We use the Pythagorean identity $\sin^2(x) + \cos^2(x) = 1$ (`SIN_CIRCLE`) to simplify terms involving sine.
- Finally, we use real ring arithmetic to complete the algebraic simplification, which yields the desired identity $\cos(3x) = 4\cos^3(x) - 3\cos(x)$.

### Mathematical insight
This identity is a special case of the Chebyshev polynomials of the first kind, specifically $T_3(x) = 4x^3 - 3x$. The identity $\cos(3x) = 4\cos^3(x) - 3\cos(x)$ is fundamental in trigonometry and has important applications in various fields:

1. It is crucial in the classic proof of the impossibility of angle trisection using ruler and compass (as hinted in the comment).
2. It is used in Fourier analysis when dealing with trigonometric series.
3. It demonstrates how multiple angle formulas can be expressed in terms of powers of trigonometric functions.

The identity provides a direct relationship between $\cos(3x)$ and $\cos(x)$, which means that if we know $\cos(x)$, we can calculate $\cos(3x)$ without needing to evaluate the cosine function again.

### Dependencies
- **Theorems:**
  - `SIN_CIRCLE`: $\forall x. \sin^2(x) + \cos^2(x) = 1$
  - `SIN_ADD`: $\forall x\, y. \sin(x + y) = \sin(x)\cos(y) + \cos(x)\sin(y)$
  - `COS_ADD`: $\forall x\, y. \cos(x + y) = \cos(x)\cos(y) - \sin(x)\sin(y)$
- **Definitions:**
  - `cos`: $\cos(x) = \text{Re}(\text{ccos}(\text{Cx}(x)))$

### Porting notes
When porting this theorem:
1. Ensure the target system has the necessary trigonometric addition formulas and the Pythagorean identity.
2. The proof relies on HOL Light's real arithmetic decision procedures (`REAL_ARITH` and `REAL_RING`). In other systems, you might need to provide more explicit algebraic steps for the substitutions and simplifications.
3. The final simplification might require careful algebraic manipulation in systems with less powerful arithmetic automation.

---

## COS_PI3

### COS_PI3
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
This theorem states that:
$$\cos\left(\frac{\pi}{3}\right) = \frac{1}{2}$$

### Informal proof
To prove that $\cos(\frac{\pi}{3}) = \frac{1}{2}$, we proceed as follows:

1. Apply the triple angle formula for cosine from `COS_TRIPLE`. For any real $x$:
   $$\cos(3x) = 4\cos^3(x) - 3\cos(x)$$

2. Substitute $x = \frac{\pi}{3}$ to get:
   $$\cos\left(3 \cdot \frac{\pi}{3}\right) = 4\cos^3\left(\frac{\pi}{3}\right) - 3\cos\left(\frac{\pi}{3}\right)$$
   
   Which simplifies to:
   $$\cos(\pi) = 4\cos^3\left(\frac{\pi}{3}\right) - 3\cos\left(\frac{\pi}{3}\right)$$

3. We know from `COS_PI` that $\cos(\pi) = -1$, so:
   $$-1 = 4\cos^3\left(\frac{\pi}{3}\right) - 3\cos\left(\frac{\pi}{3}\right)$$

4. This equation can be rewritten as:
   $$-1 = 4c^3 - 3c$$
   where $c = \cos\left(\frac{\pi}{3}\right)$.

5. Solving this equation using algebra:
   $$4c^3 - 3c = -1$$
   $$4c^3 - 3c + 1 = 0$$
   
   This can be factored to show that either $c = \frac{1}{2}$ or $c = -1$.

6. We can eliminate the solution $c = -1$ by using `COS_POS_PI`, which states that if $-\frac{\pi}{2} < x < \frac{\pi}{2}$, then $\cos(x) > 0$.
   
   Since $\frac{\pi}{3}$ is within the interval $(-\frac{\pi}{2}, \frac{\pi}{2})$ (which we can verify using `PI_POS`), we know that $\cos\left(\frac{\pi}{3}\right) > 0$.

7. Therefore, $\cos\left(\frac{\pi}{3}\right) = \frac{1}{2}$ is the only valid solution.

### Mathematical insight
This result gives the exact value of the cosine function at $\frac{\pi}{3}$ (or 60 degrees). It is a fundamental value in trigonometry, appearing in many geometric constructions and applications.

The proof uses the triple angle formula for cosine and exploits the known value of $\cos(\pi)$, demonstrating how special values of trigonometric functions can be derived from one another using appropriate formulas and constraints.

This specific value is part of the collection of "special angles" in trigonometry whose values can be expressed exactly in terms of radicals, making it an important reference point in both pure and applied mathematics.

### Dependencies
- **Definitions**:
  - `cos`: Definition of the cosine function
  - `pi`: Definition of π

- **Theorems**:
  - `COS_TRIPLE`: The triple angle formula for cosine, stating $\cos(3x) = 4\cos^3(x) - 3\cos(x)$
  - `COS_PI`: The value of cosine at π, stating $\cos(\pi) = -1$
  - `COS_POS_PI`: Positivity of cosine in the interval $(-\frac{\pi}{2}, \frac{\pi}{2})$
  - `PI_POS`: States that $\pi > 0$

### Porting notes
When porting this theorem:
1. Ensure that the cosine triple angle formula is available in your target system.
2. Verify that the basic properties of π and the positivity of cosine in the first quadrant are established.
3. The proof relies on algebraic manipulation after applying the triple angle formula - most proof assistants should handle this well, though the exact tactics will differ.
4. The elimination of the invalid solution (-1) may require different strategies in other systems, depending on how interval reasoning is formalized.

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
There does not exist a radical number $x$ such that $x^3 - 3x - 1 = 0$.

Here, a radical number refers to a number constructible using the basic arithmetic operations and taking $n$-th roots.

### Informal proof
The proof proceeds by contradiction.

- Assume there exists a radical number $x$ such that $x^3 - 3x - 1 = 0$.
- By the theorem `CUBIC_ROOT_INTEGER`, if a cubic equation with integer coefficients has a radical root, then it must also have an integer root.
- Apply this theorem with $a = 0$, $b = -3$, and $c = -1$, so we're considering the equation $x^3 + 0 \cdot x^2 - 3x - 1 = 0$, which is the same as our original equation.
- We verify that the coefficients are indeed integers.
- This means there must be an integer $x$ such that $x^3 - 3x - 1 = 0$.
- Rewrite the equation as $x(x^2 - 3) = 1$.
- Taking the absolute value of both sides: $|x| \cdot |x^2 - 3| = 1$.
- For an integer to divide 1, it must be $\pm 1$. So we need to check if any integer $x$ satisfies the equation.
- Case $x = 0$: This gives $0 \cdot (-3) = 1$, which is false.
- Case $x = 1$: This gives $1 \cdot (1 - 3) = 1$, so $1 \cdot (-2) = 1$, which is false.
- Case $x = -1$: This gives $|-1| \cdot |1 - 3| = 1 \cdot 2 = 2 \neq 1$, which is false.
- Case $|x| \geq 2$: For any integer $x$ with $|x| \geq 2$, we have $|x^2 - 3| \geq 1$, which means $|x| \cdot |x^2 - 3| \geq 2 \cdot 1 = 2 > 1$.
- Since no integer solution exists, we have a contradiction, proving that there is no radical solution to the equation.

### Mathematical insight
This theorem establishes the impossibility of trisecting a 60-degree angle using only a straightedge and compass. The equation $x^3 - 3x - 1 = 0$ arises when trying to find $\cos(20°)$ in terms of $\cos(60°) = 1/2$. Since trisecting an angle using straightedge and compass is equivalent to finding radical solutions to this cubic equation, the theorem proves that this is impossible.

This result is part of the broader theory of constructible numbers and is related to the classical Greek problems of straightedge and compass constructions. Specifically, it proves one instance of the general impossibility of angle trisection.

### Dependencies
- Theorems:
  - `INTEGER_CLOSED`: Various closure properties of integers under arithmetic operations
  - `CUBIC_ROOT_INTEGER`: If a cubic equation with integer coefficients has a radical solution, then it has an integer solution

### Porting notes
When porting to other proof assistants:
1. Ensure that the concept of radical numbers is appropriately defined
2. Check that the cubic root theorems have been properly established
3. The proof relies on case analysis of possible integer solutions, which should be straightforward to implement in most proof assistants

---

## TRISECT_60_DEGREES

### TRISECT_60_DEGREES
- State the exact name of the formal item as it appears in the HOL Light source.

### Type of the formal statement
- theorem

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
The theorem states that for any real value $y$, the point $(cos(\pi/9), y)$ is not constructible with straightedge and compass.

Formally:
$$\forall y. \neg \text{constructible}(\text{vector}[cos(\pi/9), y])$$

This means that it is impossible to construct an angle of 20 degrees (i.e., $\pi/9$ radians) using only straightedge and compass, as the x-coordinate of the point on the unit circle corresponding to this angle cannot be constructed.

### Informal proof
The proof shows that trisecting a 60-degree angle (which would give a 20-degree angle) is impossible in straightedge and compass construction:

1. We begin with a proof by contradiction. Assume that for some $y$, the point $(cos(\pi/9), y)$ is constructible.

2. By theorem `CONSTRUCTIBLE_RADICAL`, if a point is constructible, then both its coordinates are radical numbers (numbers expressible using integers, addition, subtraction, multiplication, division, and extraction of square roots).

3. Therefore, $cos(\pi/9)$ would be a radical number.

4. We use the identity $cos(3\theta) = 4cos^3(\theta) - 3cos(\theta)$ from `COS_TRIPLE`.

5. Setting $\theta = \pi/9$, we get $cos(3\pi/9) = cos(\pi/3) = 4cos^3(\pi/9) - 3cos(\pi/9)$.

6. We know from `COS_PI3` that $cos(\pi/3) = 1/2$.

7. This gives us the equation: $1/2 = 4cos^3(\pi/9) - 3cos(\pi/9)$, which can be rewritten as:
   $(2cos(\pi/9))^3 - 3(2cos(\pi/9)) - 1 = 0$

8. Let $x = 2cos(\pi/9)$. Then $x$ is also a radical number (by `RADICAL_RULES`), and it satisfies
   $x^3 - 3x - 1 = 0$

9. But theorem `TRISECT_60_DEGREES_ALGEBRA` states that there is no radical number $x$ such that $x^3 - 3x - 1 = 0$.

10. This contradiction proves that our initial assumption was false, and therefore $cos(\pi/9)$ cannot be a radical number and the point $(cos(\pi/9), y)$ is not constructible.

### Mathematical insight
This theorem is a specific case of the general result that angle trisection is impossible with straightedge and compass in general. Specifically, it proves that a 60-degree angle (or $\pi/3$ radians) cannot be trisected to construct a 20-degree angle (or $\pi/9$ radians).

The key insight comes from the connection between:
1. Constructible numbers and radical numbers
2. The algebraic equation satisfied by $cos(\pi/9)$, which is a cubic equation
3. The fact that this specific cubic equation $x^3 - 3x - 1 = 0$ has no radical solutions

This is closely related to the classical result in Galois theory that certain cubic equations cannot be solved using only arithmetic operations and square roots, making the corresponding geometric constructions impossible with straightedge and compass.

### Dependencies
- **Theorems:**
  - `COS_PI3`: Proves that $cos(\pi/3) = 1/2$
  - `COS_TRIPLE`: States the formula $cos(3x) = 4cos^3(x) - 3cos(x)$
  - `CONSTRUCTIBLE_RADICAL`: Proves that if a point is constructible, then its coordinates are radical numbers
  - `RADICAL_RULES`: Properties of radical numbers including closure under various operations
  - `TRISECT_60_DEGREES_ALGEBRA`: Proves that the equation $x^3 - 3x - 1 = 0$ has no radical solutions

- **Definitions:**
  - `cos`: The cosine function defined as $cos(x) = Re(ccos(Cx x))$
  - `pi`: The constant $\pi$ defined using properties of the sine function

### Porting notes
When porting this theorem:
1. Ensure the target system has a good theory of constructible numbers and radical numbers
2. The proof relies on algebraic properties of cubic equations, so the target system should have appropriate algebraic tools
3. Consider that the proof uses a contradiction approach combined with several mathematical identities
4. The target system will need appropriate trigonometric identities, particularly for the triple angle formula for cosine

---

