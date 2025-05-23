# two_squares.ml

## Overview

Number of statements: 24

The `two_squares.ml` file formalizes the representation of prime numbers congruent to 1 modulo 4 as the sum of two squares. It builds upon the `prime.ml` library, leveraging its definitions and theorems to establish this specific property of primes. The file's content is centered around proving this representation, which is a fundamental concept in number theory. Its purpose is to provide a formal proof of this mathematical fact within the HOL Light system.

## involution

### Name of formal statement
involution

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let involution = new_definition
  `involution f s = !x. x IN s ==> f(x) IN s /\ (f(f(x)) = x)`
```

### Informal statement
The `involution` property holds for a function `f` and a set `s` if for all `x` in `s`, `f(x)` is also in `s` and applying `f` twice to `x` yields `x` back.

### Informal sketch
* The definition asserts the existence of a function `f` that maps elements within a set `s` to elements within the same set `s`.
* The key property is that applying `f` twice to any element `x` in `s` results in the original element `x`, which is a characteristic of an involution.
* This involves two main logical stages: 
  - First, establishing that `f(x)` is in `s` for all `x` in `s`, which ensures `f` is a self-map on `s`.
  - Second, proving that `f(f(x)) = x`, which demonstrates the involution property.

### Mathematical insight
The `involution` definition captures the concept of a function that is its own inverse when applied twice, a fundamental idea in mathematics with applications in group theory, geometry, and other areas. This definition is crucial for studying symmetries and structures that exhibit such reflective properties.

### Dependencies
- **Definitions**: 
  - `IN` (set membership)
- **Theorems**: None explicitly mentioned, but potentially relies on basic properties of set theory and function composition.

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system represents set membership (`IN`) and function equality. The `!x` quantifier, which denotes "for all" in HOL Light, should be translated to the corresponding universal quantification in the target system. Additionally, ensure that the target system's type system and function definition mechanisms can accurately capture the involution property.

---

## INVOLUTION_IMAGE

### Name of formal statement
INVOLUTION_IMAGE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_IMAGE = prove
 (`!f s. involution f s ==> (IMAGE f s = s)`,
  REWRITE_TAC[involution; EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is an involution on `s`, then the image of `s` under `f` is equal to `s`.

### Informal sketch
* The proof starts by assuming that `f` is an involution on `s`, which means that `f` is its own inverse.
* Using the definition of `involution`, we can rewrite this assumption in terms of the `involution` property.
* The `REWRITE_TAC` tactic is used to rewrite the `involution` and `EXTENSION` properties, and `IN_IMAGE` is applied to simplify the expression.
* The `MESON_TAC` tactic is then used to derive the conclusion that the image of `s` under `f` is equal to `s`.
* The key idea is to leverage the `involution` property to show that `f` maps `s` onto itself.

### Mathematical insight
This theorem provides a fundamental property of involutions, which are functions that are their own inverses. The result shows that an involution on a set `s` leaves the set invariant, meaning that it maps `s` onto itself. This is a crucial insight in various areas of mathematics, such as group theory, geometry, and analysis.

### Dependencies
* `involution`
* `EXTENSION`
* `IN_IMAGE`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of quantifiers and the `involution` property. In particular, ensure that the definition of `involution` is correctly ported, as it is crucial for the proof. Additionally, the `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics in the target proof assistant.

---

## INVOLUTION_DELETE

### Name of formal statement
INVOLUTION_DELETE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_DELETE = prove
 (`involution f s /\ a IN s /\ (f a = a) ==> involution f (s DELETE a)`,
  REWRITE_TAC[involution; IN_DELETE] THEN MESON_TAC[]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is an involution on `s`, and `a` is an element of `s` such that `f(a) = a`, then `f` is an involution on the set `s` with `a` deleted.

### Informal sketch
* Start with the assumption that `f` is an involution on `s`, which means `f` satisfies certain properties on `s`.
* Given `a` is in `s` and `f(a) = a`, we aim to show `f` is an involution on `s DELETE a`.
* The proof involves rewriting the definition of `involution` and applying `IN_DELETE` to handle the set difference.
* Key steps include:
  + Unfolding the definition of `involution` to apply its properties to `f` and `s DELETE a`.
  + Using `IN_DELETE` to reason about the membership of elements in `s DELETE a`.
  + Applying `MESON_TAC` to deduce the conclusion from the given premises and rewrites.

### Mathematical insight
This theorem is important because it allows us to simplify the domain of an involution by removing fixed points, which can be crucial in various algebraic and geometric constructions. It essentially says that if a function is an involution on a set and there's an element that the function maps to itself, then removing that element from the set still results in the function being an involution on the reduced set.

### Dependencies
- `involution`
- `IN_DELETE`

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles set operations (like `DELETE`) and function properties (like `involution`). The `REWRITE_TAC` and `MESON_TAC` tactics may have direct analogs or require manual application of rewrite rules and propositional logic tactics. Ensure that the target system's libraries include or can easily define `involution` and set operations like `DELETE`.

---

## INVOLUTION_STEPDOWN

### Name of formal statement
INVOLUTION_STEPDOWN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_STEPDOWN = prove
 (`involution f s /\ a IN s ==> involution f (s DIFF {a, (f a)})`,
  REWRITE_TAC[involution; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is an involution on `s` and `a` is an element of `s`, then `f` is an involution on the set `s` with `a` and `f(a)` removed.

### Informal sketch
* Start with the assumption that `f` is an involution on `s`, meaning `f` is a function from `s` to `s` such that `f (f x) = x` for all `x` in `s`.
* Assume `a` is an element of `s`.
* To show `f` is an involution on `s DIFF {a, (f a)}`, we need to prove that for all `x` in `s DIFF {a, (f a)}`, `f (f x) = x`.
* The proof involves using the `involution` definition and properties of set difference, specifically leveraging the `IN_DIFF`, `IN_INSERT`, and `NOT_IN_EMPTY` theorems to simplify and establish the involution property on the reduced set.

### Mathematical insight
This theorem is important because it allows us to reduce the domain of an involution function `f` by removing a point and its image under `f`, and still maintain the involution property. This can be useful in various algebraic and geometric constructions where involutions play a crucial role.

### Dependencies
- `involution`
- `IN_DIFF`
- `IN_INSERT`
- `NOT_IN_EMPTY`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how the system handles set operations (like `DIFF`) and function properties (like `involution`). The `REWRITE_TAC` and `MESON_TAC` tactics in HOL Light are used for rewriting and automated reasoning, respectively. In other systems, similar tactics or mechanisms (e.g., `rewrite` in Coq, `simp` in Isabelle) may be used to achieve the same goal. Ensure that the ported version correctly applies the involution definition and set properties to establish the theorem.

---

## INVOLUTION_NOFIXES

### Name of formal statement
INVOLUTION_NOFIXES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_NOFIXES = prove
 (`involution f s ==> involution f {x | x IN s /\ ~(f x = x)}`,
  REWRITE_TAC[involution; IN_ELIM_THM] THEN MESON_TAC[]);
```

### Informal statement
For all functions `f` and sets `s`, if `f` is an involution on `s`, then `f` is also an involution on the set of elements `x` in `s` such that `f(x)` is not equal to `x`.

### Informal sketch
* The proof starts with the assumption that `f` is an involution on `s`, which means that `f` is a function from `s` to `s` that is its own inverse.
* The goal is to show that `f` is an involution on the subset of `s` where `f(x)` is not equal to `x`.
* The `REWRITE_TAC` tactic is used to rewrite the `involution` property using its definition, and `IN_ELIM_THM` is used to eliminate the set comprehension.
* The `MESON_TAC` tactic is then used to prove the resulting goal using basic logical rules.

### Mathematical insight
This theorem shows that if a function is an involution on a set, it remains an involution when restricted to the subset of elements that are not fixed points. This is a useful property in various areas of mathematics, such as group theory and combinatorics.

### Dependencies
* `involution`
* `IN_ELIM_THM`

### Porting notes
When porting this theorem to another proof assistant, note that the `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target system. Additionally, the `involution` definition and `IN_ELIM_THM` theorem may need to be defined or imported separately.

---

## INVOLUTION_SUBSET

### Name of formal statement
INVOLUTION_SUBSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_SUBSET = prove
 (`!f s t. involution f s /\ (!x. x IN t ==> f(x) IN t) /\ t SUBSET s
           ==> involution f t`,
  REWRITE_TAC[involution; SUBSET] THEN MESON_TAC[]);
```

### Informal statement
For all functions `f`, sets `s` and `t`, if `f` is an involution on `s`, and for all `x` in `t`, `f(x)` is in `t`, and `t` is a subset of `s`, then `f` is an involution on `t`.

### Informal sketch
* Start with the assumption that `f` is an involution on `s`, which means `f` is a function from `s` to `s` that is its own inverse.
* Assume that for every `x` in `t`, `f(x)` is also in `t`, establishing that `f` maps `t` into itself.
* Given that `t` is a subset of `s`, use the properties of `f` being an involution on `s` and the fact that `f` maps `t` into itself to show that `f` is an involution on `t`.
* The proof involves rewriting the definition of `involution` and using `SUBSET` properties, followed by applying `MESON_TAC` to deduce the conclusion logically.

### Mathematical insight
This theorem is important because it allows us to restrict the domain of an involution `f` from a larger set `s` to any subset `t` of `s`, as long as `f` maps `t` into itself. This is useful in various mathematical contexts where one needs to analyze the behavior of a function on smaller domains while preserving certain properties.

### Dependencies
- `involution`
- `SUBSET`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles quantifiers, subset relations, and function definitions. Specifically, the `involution` definition and the `SUBSET` relation may need to be defined or imported from appropriate libraries. Additionally, the automation provided by `MESON_TAC` in HOL Light might need to be replicated using different tactics or automation mechanisms available in the target proof assistant.

---

## INVOLUTION_EVEN

### Name of formal statement
INVOLUTION_EVEN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_EVEN = prove
 (`!s. FINITE(s) /\ involution f s /\ (!x:A. x IN s ==> ~(f x = x))
       ==> EVEN(CARD s)`,
  REWRITE_TAC[involution] THEN MESON_TAC[INVOLUTION_EVEN_NOFIXPOINTS])
```

### Informal statement
For all sets `s`, if `s` is finite and `f` is an involution on `s` such that for all `x` in `s`, `f(x)` is not equal to `x`, then the cardinality of `s` is even.

### Informal sketch
* The proof starts by assuming a finite set `s` and a function `f` that is an `involution` on `s`.
* It then uses the fact that `f` is an involution to derive properties about `f` and its behavior on `s`.
* The `REWRITE_TAC[involution]` step suggests rewriting the `involution` definition to better apply it to the given assumptions.
* The `MESON_TAC[INVOLUTION_EVEN_NOFIXPOINTS]` step implies using a meson tactic with a theorem `INVOLUTION_EVEN_NOFIXPOINTS` to conclude that the cardinality of `s` is even, leveraging the fact that there are no fixed points for `f` in `s`.
* The overall strategy is to leverage the properties of involutions and the absence of fixed points to constrain the size of `s`.

### Mathematical insight
This theorem is important because it establishes a relationship between the existence of an involution without fixed points on a set and the parity of the set's cardinality. Involutions without fixed points pair elements in the set, implying that the set must have an even number of elements to ensure every element is paired.

### Dependencies
#### Theorems
* `INVOLUTION_EVEN_NOFIXPOINTS`
#### Definitions
* `involution`
* `FINITE`
* `CARD`
* `EVEN`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how involutions are defined and how the absence of fixed points is represented. The use of `REWRITE_TAC` and `MESON_TAC` suggests that the proof relies on rewriting and basic logical deductions, which should be straightforward to replicate in other systems. However, the specific tactic script may need adjustments based on the target system's automation and tactic language.

---

## INVOLUTION_FIX_ODD

### Name of formal statement
INVOLUTION_FIX_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_FIX_ODD = prove
 (`FINITE(s) /\ involution f s /\ (?!a:A. a IN s /\ (f a = a))
   ==> ODD(CARD s)`,
  REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `s = (a:A) INSERT (s DELETE a)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; IN_DELETE; ODD; NOT_ODD] THEN
  MATCH_MP_TAC INVOLUTION_EVEN THEN
  ASM_SIMP_TAC[INVOLUTION_DELETE; FINITE_DELETE; IN_DELETE] THEN
  ASM_MESON_TAC[])
```

### Informal statement
If a set `s` is finite, `f` is an involution on `s`, and there exists exactly one element `a` in `s` such that `f(a) = a`, then the cardinality of `s` is odd.

### Informal sketch
* The proof starts by assuming the premises: `s` is finite, `f` is an involution on `s`, and there exists a unique `a` in `s` such that `f(a) = a`.
* It then proceeds to manipulate the set `s` by considering it as the insertion of `a` into `s` with `a` deleted (`s DELETE a`), utilizing `SUBGOAL_THEN` and `SUBST1_TAC` to manage the proof state.
* Key steps involve simplifying expressions using `REWRITE_TAC` with various definitions (`EXISTS_UNIQUE_DEF`, `EXTENSION`, `IN_INSERT`, `IN_DELETE`) and applying `ASM_MESON_TAC` to derive conclusions from the assumptions.
* The proof leverages `INVOLUTION_EVEN` and simplifies further using `ASM_SIMP_TAC` with definitions like `CARD_CLAUSES`, `FINITE_DELETE`, `INVOLUTION_DELETE`, to eventually conclude that the cardinality of `s` is odd (`ODD(CARD s)`).

### Mathematical insight
This theorem provides insight into the structure of sets under involutions, specifically when there is exactly one fixed point. It shows that in such cases, the cardinality of the set must be odd, which has implications for understanding the behavior of functions with specific symmetry properties. The theorem is built on the concept of an involution, which is a function that is its own inverse, and the notion of a fixed point, where the function does not change the input.

### Dependencies
#### Theorems
- `INVOLUTION_EVEN`
#### Definitions
- `involution`
- `EXISTS_UNIQUE_DEF`
- `EXTENSION`
- `IN_INSERT`
- `IN_DELETE`
- `CARD_CLAUSES`
- `FINITE_DELETE`
- `INVOLUTION_DELETE`
- `ODD`
- `NOT_ODD`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how the system handles finite sets, involutions, and the notion of fixed points. The use of `SUBGOAL_THEN` and `SUBST1_TAC` may need to be adapted, as different systems have different tactics for managing proof goals and substitutions. Additionally, the automation level and support for `REWRITE_TAC` and `ASM_MESON_TAC` might vary, potentially requiring more manual intervention or different automation tactics.

---

## INVOLUTION_ODD

### Name of formal statement
INVOLUTION_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_ODD = prove
 (`!n s. FINITE(s) /\ involution f s /\ ODD(CARD s)
         ==> ?a. a IN s /\ (f a = a)`,
  REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[INVOLUTION_EVEN])
```

### Informal statement
For all natural numbers `n` and sets `s`, if `s` is finite, `f` is an involution on `s`, and the cardinality of `s` is odd, then there exists an element `a` in `s` such that `f(a)` equals `a`.

### Informal sketch
* The proof starts by assuming that `s` is a finite set, `f` is an involution on `s`, and the cardinality of `s` is odd.
* It uses the fact that if the cardinality of `s` is odd, then it is not even, utilizing the `GSYM NOT_EVEN` rewrite rule to possibly simplify or rearrange the statement for better handling by the proof system.
* The `MESON_TAC[INVOLUTION_EVEN]` tactic suggests that the proof involves applying a set of meson (clause-style) rules, specifically leveraging the properties of involutions on even sets (`INVOLUTION_EVEN`), to deduce the existence of a fixed point `a` in `s` where `f(a) = a`.
* The high-level strategy involves recognizing that an involution on a set with an odd number of elements must have at least one fixed point, as there cannot be a one-to-one pairing of all elements with their distinct images under `f`.

### Mathematical insight
This theorem is important because it establishes a fundamental property of involutions on finite sets. An involution is a function that is its own inverse; when applied twice, it returns to the original input. On a set with an odd number of elements, an involution cannot pair every element with a distinct partner (since there's an odd number of elements), implying there must be at least one element that maps to itself, a fixed point. This theorem provides insight into the structure of symmetric functions on finite sets and has implications for various areas of mathematics, including group theory and combinatorics.

### Dependencies
* `INVOLUTION_EVEN`
* `FINITE`
* `involution`
* `ODD`
* `CARD`

### Porting notes
When translating this theorem into another proof assistant, pay attention to how that system handles finite sets, involutions, and odd/even properties. Specifically, ensure that the target system's `involution` definition matches the one used here and that there's an equivalent to the `GSYM NOT_EVEN` rewrite rule for handling odd cardinalities. Additionally, the port should preserve the structure of the proof, leveraging meson-style rules or equivalent mechanisms for applying the properties of involutions on even sets to derive the existence of a fixed point in odd sets.

---

## INVOLUTION_FIX_FIX

### Name of formal statement
INVOLUTION_FIX_FIX

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_FIX_FIX = prove
 (`!f g s. FINITE(s) /\ involution f s /\ involution g s /\
           (?!x. x IN s /\ (f x = x)) ==> ?x. x IN s /\ (g x = x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVOLUTION_ODD THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INVOLUTION_FIX_ODD THEN
  ASM_REWRITE_TAC[]);;
```

### Informal statement
For all functions `f` and `g` and for all sets `s`, if `s` is finite and both `f` and `g` are involutions on `s`, and there exists a unique `x` in `s` such that `f(x) = x`, then there exists an `x` in `s` such that `g(x) = x`.

### Informal sketch
* The proof starts by assuming the premises: `s` is finite, `f` and `g` are involutions on `s`, and there exists a unique `x` in `s` such that `f(x) = x`.
* It then applies the `INVOLUTION_ODD` theorem, which likely relates the properties of involutions and the finiteness of the set.
* The proof proceeds with rewriting using `ASM_REWRITE_TAC`, indicating that some simplification or transformation of the expressions is applied based on the assumptions.
* The `INVOLUTION_FIX_ODD` theorem is then applied, which presumably deals with the existence of fixpoints under certain conditions.
* Further rewriting is applied to conclude the proof, showing that if one involution has a unique fixpoint, the other must also have a fixpoint.

### Mathematical insight
This theorem provides insight into the properties of involutions on finite sets, specifically regarding the existence of fixpoints. It suggests that if one involution on a finite set has a unique fixpoint, then any other involution on the same set must also have a fixpoint, highlighting a deep connection between the structure of the set and the behavior of involutions.

### Dependencies
* `INVOLUTION_ODD`
* `INVOLUTION_FIX_ODD`
* `FINITE`
* `involution`

### Porting notes
When translating this theorem into other proof assistants, special attention should be given to how each system handles quantifiers, especially the unique existential quantifier `?!`. Additionally, the `involution` predicate and the `FINITE` property should be defined or imported correctly. The automation and rewriting tactics (`REPEAT STRIP_TAC`, `MATCH_MP_TAC`, `ASM_REWRITE_TAC`) may have equivalents in other systems, but their application and behavior could differ, requiring adjustments in the proof strategy.

---

## zset

### Name of formal statement
zset

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let zset = new_definition
  `zset(a) = {(x,y,z) | x EXP 2 + 4 * y * z = a}`
```

### Informal statement
The set `zset(a)` is defined as the set of all ordered triples `(x, y, z)` such that `x` squared plus `4` times `y` times `z` equals `a`.

### Informal sketch
* The definition of `zset(a)` involves a set comprehension, which constructs a set of triples `(x, y, z)` that satisfy a specific condition.
* The condition `x EXP 2 + 4 * y * z = a` is the core of the definition, relating the elements of the triple to the parameter `a`.
* To recreate this definition in another proof assistant, one would need to define a set comprehension or an equivalent construct, and then apply it to the given condition.

### Mathematical insight
The `zset(a)` definition appears to be related to a formalization of Zagier's "one-sentence" proof, which suggests a connection to number theory or algebra. The definition itself represents a set of solutions to a specific equation, which could be useful in various mathematical contexts.

### Dependencies
* None explicitly mentioned, but the definition relies on basic arithmetic operations and set comprehension, which are typically available in any proof assistant.

### Porting notes
When translating this definition to another proof assistant, consider the following:
* Set comprehension may be represented differently, e.g., using `∃` or `∀` quantifiers, or through explicit set constructors.
* The `EXP` operator might need to be replaced with the equivalent exponentiation operator in the target system.
* Pay attention to the treatment of arithmetic operations and their precedence in the target system.

---

## zag

### Name of formal statement
zag

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let zag = new_definition
  `zag(x,y,z) =
        if x + z < y then (x + 2 * z,z,y - (x + z))
        else if x < 2 * y then (2 * y - x, y, (x + z) - y)
        else (x - 2 * y,(x + z) - y, y)`;;
```

### Informal statement
The function `zag` takes three arguments `x`, `y`, and `z` and returns a triple based on the following conditions: 
- If `x + z` is less than `y`, then it returns the triple `(x + 2 * z, z, y - (x + z))`.
- Otherwise, if `x` is less than `2 * y`, then it returns the triple `(2 * y - x, y, (x + z) - y)`.
- If neither of the above conditions holds, it returns the triple `(x - 2 * y, (x + z) - y, y)`.

### Informal sketch
* The definition of `zag` involves a conditional statement that checks two inequalities involving the inputs `x`, `y`, and `z`.
* The first condition checks if `x + z` is less than `y`, and if so, it computes the triple based on the formula `(x + 2 * z, z, y - (x + z))`.
* If the first condition is not met, it checks the second condition, which is whether `x` is less than `2 * y`. If true, it calculates the triple as `(2 * y - x, y, (x + z) - y)`.
* If neither condition is satisfied, it defaults to computing the triple as `(x - 2 * y, (x + z) - y, y)`.
* The `zag` function does not explicitly use any specific HOL Light tactics or theorems in its definition, but understanding its behavior might require reasoning about inequalities and basic arithmetic properties.

### Mathematical insight
The `zag` function appears to be a piecewise definition based on the relative sizes of its inputs `x`, `y`, and `z`. It seems to adjust its output based on these comparisons, which could be part of a larger strategy in a proof or construction involving inequalities or divisibility. The exact purpose or application of `zag` depends on the broader context in which it is defined, but it clearly involves manipulating and comparing the input values to produce a specific output.

### Dependencies
- No specific dependencies are explicitly mentioned in the definition of `zag`, but it relies on basic arithmetic operations and comparisons, which are typically available in any formal system.

### Porting notes
When translating `zag` into another proof assistant, ensure that the target system supports similar conditional expressions and arithmetic operations. Pay particular attention to how the system handles piecewise definitions and ensure that the translation accurately captures the conditional logic and arithmetic manipulations involved. Additionally, consider the potential need to prove properties about `zag` in the target system, which might involve establishing the correctness of the piecewise definition under various assumptions about `x`, `y`, and `z`.

---

## tag

### Name of formal statement
tag

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let tag = new_definition
  `tag((x,y,z):num#num#num) = (x,z,y)`;;
```

### Informal statement
The function `tag` is defined as a mapping from a triple of numbers `(x, y, z)` to a new triple `(x, z, y)`, effectively swapping the second and third components of the input triple.

### Informal sketch
* The definition involves a simple permutation of the components of a triple.
* The `tag` function takes a triple `(x, y, z)` as input and returns a new triple where `y` and `z` are swapped.
* No specific tactics or complex logical stages are involved, as this is a straightforward definition.

### Mathematical insight
The `tag` function represents a basic operation on triples of numbers, which might be used in various mathematical constructions or proofs involving permutations or rearrangements of elements. This definition is fundamental and can be used as a building block in more complex arguments or transformations.

### Dependencies
#### Definitions
* `num`

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, ensure that the target system supports similar tuple or record types and that the definition can be expressed in a comparable way. Note that the syntax for defining functions and handling tuples may vary between systems. For example, in Lean, you might define `tag` using a lambda expression or a `def` statement, while in Coq, you could use the `Definition` keyword.

---

## ZAG_INVOLUTION_GENERAL

### Name of formal statement
ZAG_INVOLUTION_GENERAL

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ZAG_INVOLUTION_GENERAL = prove
 (`0 < x /\ 0 < y /\ 0 < z ==> (zag(zag(x,y,z)) = (x,y,z))`,
  REWRITE_TAC[zag] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[zag] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC)
```

### Informal statement
For all positive real numbers $x$, $y$, and $z$, if $x > 0$ and $y > 0$ and $z > 0$, then applying the `zag` function twice to $(x, y, z)$ results in the original tuple $(x, y, z)$.

### Informal sketch
* The proof begins by assuming $x > 0$, $y > 0$, and $z > 0$.
* It then applies the definition of `zag` to $(x, y, z)$, using `REWRITE_TAC[zag]`.
* The proof proceeds by considering cases based on the conditions in the definition of `zag`, utilizing `COND_CASES_TAC` and `ASM_REWRITE_TAC` to simplify and handle each case.
* After applying `zag` twice and simplifying, it uses `REWRITE_TAC[PAIR_EQ]` to establish the equality of the resulting pair with the original input.
* Finally, the proof concludes by using `ARITH_TAC` to verify any remaining arithmetic conditions.

### Mathematical insight
This theorem establishes the involution property of the `zag` function for positive real numbers, meaning that applying `zag` twice returns the original input. This property is crucial in various mathematical contexts where such a function is used, providing a form of symmetry or reversal.

### Dependencies
* `zag`
* `PAIR_EQ`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how the `zag` function is defined and how case analysis (`COND_CASES_TAC`) and arithmetic reasoning (`ARITH_TAC`) are handled. The involution property might be proven using similar tactics, but the exact implementation could vary depending on the target system's support for arithmetic and equality reasoning.

---

## IN_TRIPLE

### Name of formal statement
IN_TRIPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IN_TRIPLE = prove
 (`(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);
```

### Informal statement
For all `a`, `b`, and `c`, the triple `(a, b, c)` is an element of the set of all triples `(x, y, z)` such that `P x y z` holds if and only if `P a b c` holds.

### Informal sketch
* The proof involves rewriting the membership relation using the `IN_ELIM_THM` theorem and the definition of pair equality `PAIR_EQ`.
* The `REWRITE_TAC` tactic is applied with these theorems to transform the goal into a more manageable form.
* The `MESON_TAC` tactic is then used to discharge the resulting goal, which involves straightforward logical deductions.

### Mathematical insight
This theorem provides a fundamental property of set membership for triples, allowing for the simplification of expressions involving sets defined by predicates. It is essential for working with sets of tuples in formal proofs.

### Dependencies
* Theorems:
  + `IN_ELIM_THM`
  + `PAIR_EQ`
* Definitions:
  None
* Inductive rules:
  None

### Porting notes
When translating this theorem into other proof assistants, note that the `REWRITE_TAC` and `MESON_TAC` tactics may have analogs, but their exact behavior and applicability might differ. In particular, the handling of binders and automation levels may require adjustments. For example, in Lean, one might use `rw` for rewriting and `finish` or `by auto` for automated proof steps, while in Coq, `rewrite` and `auto` or `eauto` could be used. In Isabelle, `rewrite` and `auto` or `metis` might be employed.

---

## PRIME_SQUARE

### Name of formal statement
PRIME_SQUARE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PRIME_SQUARE = prove
 (`!n. ~prime(n * n)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[PRIME_0; MULT_CLAUSES] THEN
  REWRITE_TAC[prime; NOT_FORALL_THM; DE_MORGAN_THM] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[ARITH] THEN
  DISJ2_TAC THEN EXISTS_TAC `n:num` THEN
  ASM_SIMP_TAC[DIVIDES_LMUL; DIVIDES_REFL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [ARITH_RULE `n = n * 1`] THEN
  ASM_SIMP_TAC[EQ_MULT_LCANCEL])
```

### Informal statement
For all natural numbers `n`, it is not the case that `n` squared is a prime number.

### Informal sketch
* The proof starts by considering all natural numbers `n`.
* It then proceeds by cases: first considering when `n` equals 0, and applying `PRIME_0` and `MULT_CLAUSES` to simplify.
* For non-zero `n`, it further considers the case when `n` equals 1, applying `ARITH` to handle this instance.
* For `n` greater than 1, it asserts the existence of a divisor of `n` squared (namely `n` itself), leveraging `DIVIDES_LMUL` and `DIVIDES_REFL`.
* The proof involves simplification steps using `GEN_REWRITE_TAC` and `ASM_SIMP_TAC` to establish the final result, utilizing properties like `EQ_MULT_LCANCEL`.

### Mathematical insight
This theorem captures a fundamental property of prime numbers, specifically that the square of any natural number greater than 1 cannot be prime. This is because such a square has at least three distinct positive divisors: 1, the number itself, and its square, thus violating the definition of a prime number.

### Dependencies
* **Theorems and definitions:**
  - `PRIME_0`
  - `MULT_CLAUSES`
  - `prime`
  - `NOT_FORALL_THM`
  - `DE_MORGAN_THM`
  - `ARITH`
  - `DIVIDES_LMUL`
  - `DIVIDES_REFL`
  - `EQ_MULT_LCANCEL`
* **Inductive rules:** None

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how each system handles quantifiers, case splits, and the application of rewrite rules. The use of `GEN_TAC`, `ASM_CASES_TAC`, and `GEN_REWRITE_TAC` may have direct analogs or require rephrasing to fit the target system's syntax and proof construction mechanisms. Additionally, ensure that the prime number definition (`prime`) and arithmetic properties (`ARITH`) are properly aligned with their counterparts in the target system.

---

## PRIME_4X

### Name of formal statement
PRIME_4X

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PRIME_4X = prove
 (`!n. ~prime(4 * n)`,
  GEN_TAC THEN REWRITE_TAC[prime; NOT_FORALL_THM; DE_MORGAN_THM] THEN
  DISJ2_TAC THEN EXISTS_TAC `2` THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 * 2`)) THEN
  ASM_SIMP_TAC[GSYM MULT_ASSOC; DIVIDES_RMUL; DIVIDES_REFL; ARITH_EQ] THEN
  ASM_CASES_TAC `n = 0` THEN POP_ASSUM MP_TAC THEN ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, it is not the case that `4 * n` is prime.

### Informal sketch
* The proof starts by assuming an arbitrary `n` and applying generalization (`GEN_TAC`) to set up the proof for all `n`.
* It then rewrites the `prime` definition using `REWRITE_TAC` with theorems `prime`, `NOT_FORALL_THM`, and `DE_MORGAN_THM` to simplify the statement.
* The proof proceeds by case analysis, first considering the case where `n` is not zero, and using `DISJ2_TAC` to focus on the existence of a divisor.
* It then uses `EXISTS_TAC` to introduce a specific divisor, `2`, and simplifies the expression `2 * 2` using `NUM_REDUCE_CONV`.
* The proof continues with simplification steps (`ASM_SIMP_TAC`) involving properties of multiplication (`MULT_ASSOC`), divisibility (`DIVIDES_RMUL` and `DIVIDES_REFL`), and arithmetic equality (`ARITH_EQ`).
* Finally, it considers the special case where `n = 0` using `ASM_CASES_TAC`, and applies `ARITH_TAC` for arithmetic reasoning to conclude the proof.

### Mathematical insight
This theorem states that any number that is a multiple of 4 cannot be prime, which is a fundamental property in number theory. The proof leverages basic properties of arithmetic and divisibility to demonstrate this fact. Understanding this theorem is crucial for further developments in number theory within the proof assistant.

### Dependencies
* Theorems:
  - `prime`
  - `NOT_FORALL_THM`
  - `DE_MORGAN_THM`
  - `MULT_ASSOC`
  - `DIVIDES_RMUL`
  - `DIVIDES_REFL`
  - `ARITH_EQ`
* Tactics and functions:
  - `GEN_TAC`
  - `REWRITE_TAC`
  - `DISJ2_TAC`
  - `EXISTS_TAC`
  - `SUBST1_TAC`
  - `NUM_REDUCE_CONV`
  - `ASM_SIMP_TAC`
  - `ASM_CASES_TAC`
  - `POP_ASSUM`
  - `MP_TAC`
  - `ARITH_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles quantifiers, arithmetic, and divisibility properties. The tactic script provided is specific to HOL Light, so the porting process will require understanding the equivalent tactics and theorems in the target system. For example, the `GEN_TAC` and `REWRITE_TAC` tactics have direct counterparts in other systems, but the specific theorems used (e.g., `prime`, `NOT_FORALL_THM`) may need to be reformulated or imported from libraries within the target proof assistant.

---

## PRIME_XYZ_NONZERO

### Name of formal statement
PRIME_XYZ_NONZERO

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PRIME_XYZ_NONZERO = prove
 (`prime(x EXP 2 + 4 * y * z) ==> 0 < x /\ 0 < y /\ 0 < z`,
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[DE_MORGAN_THM; ARITH_RULE `~(0 < x) = (x = 0)`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES; PRIME_SQUARE; PRIME_4X])
```

### Informal statement
If `x` to the power of 2 plus 4 times `y` times `z` is prime, then `x` is greater than 0, `y` is greater than 0, and `z` is greater than 0.

### Informal sketch
* The proof starts by assuming the negation of the conclusion, using `CONTRAPOS_CONV`, which transforms the goal into a form that is easier to work with.
* It then applies `DE_MORGAN_THM` and an `ARITH_RULE` to simplify the negated conclusion, allowing for case analysis.
* The `DISCH_THEN` and `REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC` steps are used to discharge assumptions and perform substitutions, breaking down the problem into manageable cases.
* Finally, the proof uses `REWRITE_TAC` with various theorems (`EXP_2`, `MULT_CLAUSES`, `ADD_CLAUSES`, `PRIME_SQUARE`, `PRIME_4X`) to simplify expressions and reach the desired conclusion.

### Mathematical insight
This theorem provides a condition under which a specific expression is guaranteed to be prime, based on the properties of its components `x`, `y`, and `z`. The condition that all variables must be positive is both necessary and sufficient for the expression to be prime, highlighting the interplay between the arithmetic properties of the numbers involved and the concept of primality.

### Dependencies
* Theorems:
  * `DE_MORGAN_THM`
  * `EXP_2`
  * `MULT_CLAUSES`
  * `ADD_CLAUSES`
  * `PRIME_SQUARE`
  * `PRIME_4X`
* Tactics and rules:
  * `CONTRAPOS_CONV`
  * `REWRITE_TAC`
  * `DISCH_THEN`
  * `REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC`
  * `ARITH_RULE` 

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how the system handles contrapositive proofs and case analysis, as these are crucial steps in the original HOL Light proof. Additionally, ensure that the target system has equivalent theorems and rules for arithmetic and primality properties, as these are used extensively in the proof.

---

## ZAG_INVOLUTION

### Name of formal statement
ZAG_INVOLUTION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ZAG_INVOLUTION = prove
 (`!p. prime(p) ==> involution zag (zset(p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[involution; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[zset; IN_TRIPLE] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[zag] THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_TRIPLE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD; EXP_2;
                 GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_SUB; LT_IMP_LE] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC ZAG_INVOLUTION_GENERAL THEN
    ASM_MESON_TAC[PRIME_XYZ_NONZERO]])
```

### Informal statement
For all prime numbers `p`, the `zag` function is an involution on the set `zset(p)`.

### Informal sketch
* The proof starts by assuming a prime number `p` and then applies various tactics to transform the goal into a more manageable form.
* It uses `REPEAT STRIP_TAC` to strip away universal quantifiers, followed by `REWRITE_TAC` to apply the definitions of `involution` and `FORALL_PAIR_THM`.
* The proof then proceeds by case analysis using `COND_CASES_TAC` and simplification using `ASM_REWRITE_TAC` and `ASM_SIMP_TAC`.
* Key steps involve applying the definition of `zag` and using properties of integers, such as `INT_OF_NUM_EQ`, `INT_OF_NUM_ADD`, and `LT_IMP_LE`.
* The second part of the proof uses `MATCH_MP_TAC` to apply a general theorem `ZAG_INVOLUTION_GENERAL` and then `ASM_MESON_TAC` to derive the conclusion from `PRIME_XYZ_NONZERO`.

### Mathematical insight
This theorem establishes that the `zag` function is an involution on a specific set `zset(p)` when `p` is prime. An involution is a function that is its own inverse, meaning that applying it twice returns the original input. This property is important in various mathematical contexts, including algebra and geometry.

### Dependencies
* Theorems:
	+ `involution`
	+ `FORALL_PAIR_THM`
	+ `ZAG_INVOLUTION_GENERAL`
* Definitions:
	+ `zag`
	+ `zset`
* Other:
	+ `PRIME_XYZ_NONZERO`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of universal quantifiers, case analysis, and integer properties. The `REPEAT` and `MAP_EVERY` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the `ASM_` prefix on various tactics indicates that they are applied in a specific context, which may require careful handling in the target system.

---

## TAG_INVOLUTION

### Name of formal statement
TAG_INVOLUTION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TAG_INVOLUTION = prove
 (`!a. involution tag (zset a)`,
  REWRITE_TAC[involution; tag; zset; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_TRIPLE] THEN REWRITE_TAC[MULT_AC])
```

### Informal statement
For all `a`, `tag` is an involution on the set `zset a`.

### Informal sketch
* The proof starts with the assumption that `tag` is applied to `zset a`, and then applies several rewrite rules to simplify the expression.
* The `involution` property is checked using the `REWRITE_TAC` tactic with various theorems, including `involution`, `tag`, `zset`, and `FORALL_PAIR_THM`.
* Further simplification is achieved by applying `REWRITE_TAC` with `IN_TRIPLE` and `MULT_AC`.
* The proof aims to establish that `tag` satisfies the involution property for any `zset a`.

### Mathematical insight
The theorem `TAG_INVOLUTION` establishes that the `tag` function is an involution on the set `zset a` for any `a`. This means that applying `tag` twice to any element in `zset a` returns the original element. This property is important in various mathematical structures, as it ensures that the `tag` function has a certain kind of symmetry.

### Dependencies
* Theorems:
	+ `involution`
	+ `tag`
	+ `zset`
	+ `FORALL_PAIR_THM`
	+ `IN_TRIPLE`
	+ `MULT_AC`

### Porting notes
When porting this theorem to another proof assistant, pay attention to the handling of the `involution` property and the `REWRITE_TAC` tactic. The `REWRITE_TAC` tactic is used to simplify the expression using various theorems, so it's essential to ensure that the equivalent tactic in the target proof assistant is used correctly. Additionally, the `involution` property and the `tag` function should be defined and implemented accordingly in the target system.

---

## ZAG_LEMMA

### Name of formal statement
ZAG_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ZAG_LEMMA = prove
 (`(zag(x,y,z) = (x,y,z)) ==> (y = x)`,
  REWRITE_TAC[zag; INT_POW_2] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[PAIR_EQ]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC)
```

### Informal statement
If `zag(x, y, z)` is equal to `(x, y, z)`, then `y` is equal to `x`.

### Informal sketch
* The proof starts by applying `REWRITE_TAC` with `zag` and `INT_POW_2` to transform the given equation.
* It then repeatedly applies `COND_CASES_TAC` followed by `ASM_SIMP_TAC` with `PAIR_EQ` to simplify the expression and handle any conditional cases.
* After simplification, it uses `POP_ASSUM_LIST` with `MP_TAC` and `CONJ` to manage assumptions and combine them into a conjunction.
* Finally, it applies `ARITH_TAC` to complete the proof, likely using arithmetic properties to establish the equality `y = x`.
* Key HOL Light terms involved include `zag`, `INT_POW_2`, and `PAIR_EQ`, indicating the proof relies on properties of these definitions.

### Mathematical insight
This theorem provides insight into the properties of the `zag` function, specifically under what conditions it preserves or relates its input components. The theorem suggests that if `zag` returns its input unchanged, there is a specific relationship between its second and first arguments, namely that they are equal. This could be crucial in contexts where `zag` is used to transform or analyze data, providing a basis for further deductions about the properties of `zag` and its interactions with other functions or relations.

### Dependencies
* **Definitions:**
  - `zag`
  - `INT_POW_2`
  - `PAIR_EQ`
* **Theorems/Tactics:**
  - `REWRITE_TAC`
  - `COND_CASES_TAC`
  - `ASM_SIMP_TAC`
  - `POP_ASSUM_LIST`
  - `MP_TAC`
  - `ARITH_TAC`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to how the target system handles rewriting, conditional case analysis, and arithmetic reasoning. The `REWRITE_TAC`, `COND_CASES_TAC`, and `ARITH_TAC` tactics have direct analogs in many systems (e.g., `rewrite` in Coq, `cases` and `arith` in Isabelle), but the exact application and combination of these tactics may vary. Additionally, the management of assumptions and conjunctions, as done with `POP_ASSUM_LIST` and `MP_TAC`, should be carefully translated to ensure that the proof assistant correctly applies the relevant rules and properties.

---

## ZSET_BOUND

### Name of formal statement
ZSET_BOUND

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ZSET_BOUND = prove
 (`0 < y /\ 0 < z /\ (x EXP 2 + 4 * y * z = p)
   ==> x <= p /\ y <= p /\ z <= p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
   [MESON_TAC[EXP_2; LE_SQUARE_REFL; ARITH_RULE `(a <= b ==> a <= b + c)`];
    CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE `y <= z ==> y <= x + z`) THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MULT_SYM]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `y <= 4 * a * y <=> 1 * y <= (4 * a) * y`] THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < a ==> 1 <= 4 * a`]])
```

### Informal statement
For all `x`, `y`, `z`, and `p`, if `0` is less than `y` and `0` is less than `z` and the equation `x` squared plus `4` times `y` times `z` equals `p`, then `x` is less than or equal to `p` and `y` is less than or equal to `p` and `z` is less than or equal to `p`.

### Informal sketch
* Start by assuming the given conditions: `0 < y`, `0 < z`, and `x^2 + 4*y*z = p`.
* Use these assumptions to derive `x <= p`, `y <= p`, and `z <= p` through a series of logical deductions.
* The proof involves using properties of arithmetic, such as `EXP_2` and `LE_SQUARE_REFL`, and applying rules like `ARITH_RULE` to manipulate inequalities.
* Key steps include using `CONJ_TAC` to split the goal into separate inequalities and `MATCH_MP_TAC` to apply a relevant arithmetic rule.
* The `GEN_REWRITE_TAC` and `ASM_REWRITE_TAC` tactics are used to simplify expressions and apply specific rules like `MULT_SYM` and `LE_MULT_RCANCEL`.
* The final steps involve simplifying the inequalities using `ASM_SIMP_TAC` and `ARITH_RULE` to reach the desired conclusions.

### Mathematical insight
This theorem provides a bound on the variables `x`, `y`, and `z` in terms of `p`, under certain conditions. It is useful in situations where one needs to establish relationships between these variables, particularly in contexts involving quadratic expressions and inequalities. The theorem's importance lies in its ability to provide a clear and direct relationship between the variables, which can be crucial in more complex proofs or calculations.

### Dependencies
* Theorems:
  - `EXP_2`
  - `LE_SQUARE_REFL`
  - `ARITH_RULE`
* Definitions:
  - None
* Inductive rules:
  - None
* Other dependencies:
  - `MULT_SYM`
  - `LE_MULT_RCANCEL`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to the handling of arithmetic rules and the application of tactics like `GEN_REWRITE_TAC` and `MATCH_MP_TAC`. The `ARITH_RULE` and `ASM_SIMP_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the use of `CONJ_TAC` and `THENL` to manage multiple subgoals may require careful translation to ensure that the proof structure is preserved.

---

## ZSET_FINITE

### Name of formal statement
ZSET_FINITE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ZSET_FINITE = prove
 (`!p. prime(p) ==> FINITE(zset p)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `p + 1` FINITE_NUMSEG_LT) THEN
  DISCH_THEN(fun th ->
    MP_TAC(funpow 2 (MATCH_MP FINITE_PRODUCT o CONJ th) th)) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
    FINITE_SUBSET) THEN
  REWRITE_TAC[zset; SUBSET; FORALL_PAIR_THM; IN_TRIPLE] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `z:num`] THEN
  REWRITE_TAC[IN_ELIM_THM; EXISTS_PAIR_THM; PAIR_EQ] THEN
  REWRITE_TAC[ARITH_RULE `x < p + 1 <=> x <= p`; PAIR_EQ] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:num`; `y:num`; `z:num`] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MAP_EVERY EXISTS_TAC [`y:num`; `z:num`] THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[ZSET_BOUND; PRIME_XYZ_NONZERO])
```

### Informal statement
For all prime numbers p, the set zset p is finite.

### Informal sketch
* The proof starts by assuming a prime number `p` and aims to show that `zset p` is finite.
* It uses the `FINITE_NUMSEG_LT` theorem with `p + 1` to establish a finite set.
* The proof then applies `FINITE_PRODUCT` and `FINITE_SUBSET` theorems to derive the finiteness of `zset p`.
* Key steps involve rewriting with `zset`, `SUBSET`, `FORALL_PAIR_THM`, and `IN_TRIPLE` to manipulate the set expressions.
* The tactic script involves several applications of `REWRITE_TAC`, `MAP_EVERY X_GEN_TAC`, `EXISTS_TAC`, and `ASM_MESON_TAC` to handle the logical and set-theoretic reasoning.
* The `PRIME_XYZ_NONZERO` theorem is crucial in establishing properties of prime numbers.

### Mathematical insight
This theorem is important because it establishes a fundamental property of the set `zset p` for prime `p`, which is crucial in number theory. The finiteness of `zset p` has implications for various results in arithmetic and algebra.

### Dependencies
* Theorems:
  * `FINITE_NUMSEG_LT`
  * `FINITE_PRODUCT`
  * `FINITE_SUBSET`
  * `PRIME_XYZ_NONZERO`
* Definitions:
  * `zset`
  * `SUBSET`
  * `FORALL_PAIR_THM`
  * `IN_TRIPLE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to the handling of prime numbers, set finiteness, and the specific tactics used for rewriting and applying theorems. The `GEN_TAC`, `DISCH_TAC`, and `MATCH_MP_TAC` tactics may have direct counterparts, but the `ASM_MESON_TAC` and `funpow` applications might require more careful translation due to differences in automation and tactic languages.

---

## SUM_OF_TWO_SQUARES

### Name of formal statement
SUM_OF_TWO_SQUARES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUM_OF_TWO_SQUARES = prove
 (`!p k. prime(p) /\ (p = 4 * k + 1) ==> ?x y. p = x EXP 2 + y EXP 2`,
  SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?t. t IN zset(p) /\ (tag(t) = t)` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM; tag; PAIR_EQ] THEN
    REWRITE_TAC[zset; IN_TRIPLE; EXP_2] THEN
    ASM_MESON_TAC[ARITH_RULE `4 * x * y = (2 * x) * (2 * y)`]] THEN
  MATCH_MP_TAC INVOLUTION_FIX_FIX THEN EXISTS_TAC `zag` THEN
  ASM_SIMP_TAC[ZAG_INVOLUTION; TAG_INVOLUTION; ZSET_FINITE] THEN
  REWRITE_TAC[EXISTS_UNIQUE_ALT] THEN EXISTS_TAC `1,1,k:num` THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `z:num`] THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[zset; zag; IN_TRIPLE; ARITH] THEN
    REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `~(1 + k < 1)`; PAIR_EQ] THEN
    ARITH_TAC] THEN
  REWRITE_TAC[zset; IN_TRIPLE] THEN STRIP_TAC THEN
  FIRST_ASSUM(SUBST_ALL_TAC o MATCH_MP ZAG_LEMMA) THEN
  UNDISCH_TAC `x EXP 2 + 4 * x * z = 4 * k + 1` THEN
  REWRITE_TAC[EXP_2; ARITH_RULE `x * x + 4 * x * z = x * (4 * z + x)`] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN UNDISCH_TAC `prime p` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[prime] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:num`)) THEN
  SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
   [UNDISCH_TAC `4 * k + 1 = 1 * (4 * z + 1)` THEN
    REWRITE_TAC[MULT_CLAUSES; PAIR_EQ] THEN ARITH_TAC;
    ONCE_REWRITE_TAC[ARITH_RULE `(a = a * b) = (a * b = a * 1)`] THEN
    ASM_SIMP_TAC[EQ_MULT_LCANCEL] THEN STRIP_TAC THENL
     [UNDISCH_TAC `4 * k + 1 = x * (4 * z + x)` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_EQ_0; ARITH_EQ];
      UNDISCH_TAC `4 * z + x = 1` THEN REWRITE_TAC[PAIR_EQ] THEN
      ASM_CASES_TAC `z = 0` THENL
       [ALL_TAC; UNDISCH_TAC `~(z = 0)` THEN ARITH_TAC] THEN
      UNDISCH_TAC `4 * k + 1 = x * (4 * z + x)` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      ASM_CASES_TAC `x = 1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC]])
```

### Informal statement
For all prime numbers `p` and integers `k` such that `p = 4 * k + 1`, there exist integers `x` and `y` such that `p = x^2 + y^2`.

### Informal sketch
* The proof starts by assuming `p` is a prime number and `p = 4 * k + 1` for some integer `k`.
* It then uses the `SIMP_TAC` and `REPEAT STRIP_TAC` to simplify the goal and apply the `SUBGOAL_THEN` tactic to introduce a new subgoal.
* The `MATCH_MP_TAC` tactic is used with `INVOLUTION_FIX_FIX` to apply a fixpoint theorem, and `EXISTS_TAC` is used to introduce the witness `zag`.
* The proof then proceeds with a series of simplifications and applications of various theorems, including `ZAG_INVOLUTION`, `TAG_INVOLUTION`, and `ZSET_FINITE`.
* The `EXISTS_UNIQUE_ALT` theorem is used to introduce the witnesses `1, 1, k`, and the proof is then split into cases using `EQ_TAC`.
* The `DISCH_THEN` and `SUBST1_TAC` tactics are used to substitute and simplify the equations, and the `ARITH_TAC` tactic is used to perform arithmetic simplifications.
* The `MATCH_MP_TAC` tactic is used again with `ZAG_LEMMA` to apply another theorem, and the proof is then completed with a series of simplifications and applications of various theorems.

### Mathematical insight
This theorem is a classic result in number theory, which states that every prime number of the form `4k + 1` can be expressed as the sum of two squares. The proof uses a combination of algebraic manipulations, fixpoint theorems, and properties of prime numbers to establish this result.

### Dependencies
* `prime`
* `EXP_2`
* `INVOLUTION_FIX_FIX`
* `ZAG_INVOLUTION`
* `TAG_INVOLUTION`
* `ZSET_FINITE`
* `EXISTS_UNIQUE_ALT`
* `ZAG_LEMMA`
* `DIVIDES_RMUL`
* `DIVIDES_REFL`
* `EQ_MULT_LCANCEL`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the algebraic manipulations and fixpoint theorems are handled correctly. The `SIMP_TAC` and `REPEAT STRIP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `MATCH_MP_TAC` tactic may need to be replaced with a similar tactic that applies a theorem to a goal. The `EXISTS_TAC` and `DISCH_THEN` tactics should be handled carefully to ensure that the witnesses are introduced and substituted correctly.

---

