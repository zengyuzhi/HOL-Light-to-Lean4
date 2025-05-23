# four_squares.ml

## Overview

Number of statements: 36

The `four_squares.ml` file in HOL Light contains theorems and definitions related to representations as sums of 2 and 4 squares. It builds upon concepts from prime numbers and analysis, as indicated by its imports from `prime.ml` and `analysis.ml`. The file's purpose is to formalize mathematical results concerning these representations, potentially including proofs of known theorems and constructions of relevant mathematical objects. Its content is focused on number theory, specifically the study of sums of squares.

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
For all x, if x is an element of set s, then the function f applied to x is also an element of set s, and the function f applied to the result of f applied to x equals x.

### Informal sketch
* The definition of `involution` involves a universal quantification over x, implying that the property holds for every x in the set s.
* The definition states two conditions:
  + The function f maps elements of s back into s (i.e., `f(x) IN s`).
  + Applying f twice to any element x in s returns that element (i.e., `f(f(x)) = x`).
* This definition can be used to reason about functions that have an involution property over a specific set.

### Mathematical insight
The `involution` definition captures the concept of a function being its own inverse when restricted to a particular set. This is a fundamental concept in mathematics, appearing in various areas such as group theory, where involutions are used to study symmetry properties.

### Dependencies
* `IN` (set membership)
* `!` (universal quantification)
* `==>` (implication)
* `/\` (conjunction)

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles universal quantification, set membership, and function composition. Specifically, the `!x. x IN s ==> ...` construct might be represented differently, and the `f(f(x))` composition may require explicit function type annotations. Additionally, the definition's reliance on set theory and basic logical connectives should be straightforward to translate, but verifying the ported definition's properties might require re-proving or re-importing relevant theorems about set operations and function properties.

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
* The proof assumes that `f` is an involution on `s`, meaning that `f` is its own inverse, i.e., `f (f x) = x` for all `x` in `s`.
* The goal is to show that the image of `s` under `f` is equal to `s`, i.e., `IMAGE f s = s`.
* The proof uses the `REWRITE_TAC` tactic to rewrite the `involution` property in terms of `EXTENSION` and `IN_IMAGE`, and then applies `MESON_TAC` to derive the conclusion.
* Key steps involve:
  + Using the definition of `involution` to establish that `f` maps `s` into itself
  + Applying the `EXTENSION` principle to show that `IMAGE f s` is a subset of `s`
  + Using the `IN_IMAGE` property to show that every element of `s` is in the image of `f`

### Mathematical insight
This theorem establishes a fundamental property of involutions on sets: they are self-inverse and map the set onto itself. This result is important in various areas of mathematics, such as group theory, geometry, and combinatorics.

### Dependencies
* `involution`
* `EXTENSION`
* `IN_IMAGE`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of set theory and function properties. In particular, ensure that the `involution` property is defined and used correctly, and that the `IMAGE` function is properly defined and computed. Additionally, the `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics in the target proof assistant.

---

## INVOLUTION_DELETE

### Name of formal statement
INVOLUTION_DELETE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INVOLUTION_DELETE = prove
 (`involution f s /\ a IN s /\ (f a = a) ==> involution f (s DELETE a)`,
  REWRITE_TAC[involution; IN_DELETE] THEN MESON_TAC[]);;
```

### Informal statement
For all functions `f` and sets `s`, if `f` is an involution on `s`, and `a` is an element of `s` such that `f(a) = a`, then `f` is an involution on the set `s` with `a` deleted.

### Informal sketch
* Start with the assumption that `f` is an `involution` on `s`, meaning it satisfies the properties of an involution, and `a` is in `s` with `f(a) = a`.
* Use the definition of `involution` to establish its properties on `s`.
* Apply the `IN_DELETE` rule to consider the set `s` with `a` removed.
* Utilize the `REWRITE_TAC` tactic to rewrite the `involution` and `IN_DELETE` properties in a suitable form for proof.
* Employ `MESON_TAC` to automatically prove the resulting goal, showing `f` is an involution on `s DELETE a`.

### Mathematical insight
This theorem is important because it shows that if a function is an involution on a set and fixes a particular element, then it remains an involution when that element is removed from the set. This has implications for understanding the behavior of involutions on restricted domains.

### Dependencies
* `involution`
* `IN_DELETE`

### Porting notes
When translating this into another proof assistant, ensure that the notion of `involution` and set operations like `DELETE` are properly defined and aligned with the target system's libraries. The use of `REWRITE_TAC` and `MESON_TAC` may need to be adapted based on the target system's tactic language and automation capabilities.

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
* Start with the assumption that `f` is an involution on `s`, which means `f` is a function from `s` to `s` such that `f (f x) = x` for all `x` in `s`.
* Given `a` is in `s`, we need to show that `f` is an involution on `s DIFF {a, (f a)}`, which means `f` maps this new set to itself and `f (f x) = x` for all `x` in `s DIFF {a, (f a)}`.
* The proof involves rewriting the definition of `involution` and using properties of set difference and membership to establish the result.

### Mathematical insight
This theorem is important because it allows us to reduce the domain of an involution `f` by removing a point and its image under `f`, and still have `f` act as an involution on the reduced domain. This is useful in various algebraic and geometric constructions where involutions play a key role.

### Dependencies
* `involution`
* `IN_DIFF`
* `IN_INSERT`
* `NOT_IN_EMPTY`

### Porting notes
When translating this theorem into another proof assistant, pay attention to how the system handles set difference and the properties of involutions. The `REWRITE_TAC` and `MESON_TAC` tactics in HOL Light are used for rewriting and automated reasoning, respectively. In other systems, similar tactics or mechanisms may be used, but their application might differ. For example, in Lean, you might use `rw` for rewriting and `finish` or `by` with an automation tactic for the second part. In Coq, `rewrite` and `auto` or `eauto` might be used. Ensure that the ported version correctly handles the quantifiers and the specific properties of set operations and involutions.

---

## INVOLUTION_NOFIXES

### Name of formal statement
INVOLUTION_NOFIXES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_NOFIXES = prove
 (`involution f s ==> involution f {x | x IN s /\ ~(f x = x)}`,
  REWRITE_TAC[involution; IN_ELIM_THM] THEN MESON_TAC[]);
```

### Informal statement
If `f` is an involution on the set `s`, then `f` is also an involution on the set of all `x` in `s` such that `f(x)` is not equal to `x`.

### Informal sketch
* Start with the assumption that `f` is an involution on `s`, which means that `f` is a function from `s` to `s` that satisfies certain properties.
* Consider the subset of `s` consisting of all elements `x` such that `f(x)` is not equal to `x`.
* Apply the definition of involution and the given assumption to show that `f` restricted to this subset still satisfies the properties of an involution.
* Use the `involution` definition and `IN_ELIM_THM` to rewrite and simplify the statement, then apply `MESON_TAC` to derive the conclusion.

### Mathematical insight
This theorem shows that if a function `f` is an involution on a set `s`, then it remains an involution when restricted to the subset of `s` where `f` is not the identity function. This is useful for analyzing the behavior of involutions on subsets of their domain.

### Dependencies
* `involution`
* `IN_ELIM_THM`

### Porting notes
When translating this theorem to another proof assistant, pay attention to how the `involution` property is defined and how the `IN_ELIM_THM` theorem is applied. The `MESON_TAC` tactic may need to be replaced with a similar tactic or a manual proof step, depending on the target system's automation capabilities.

---

## INVOLUTION_SUBSET

### Name of formal statement
INVOLUTION_SUBSET

### Type of the formal statement
Theorem

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
* The proof starts by assuming `f` is an involution on `s`, which means `f` satisfies certain properties on `s`.
* It then assumes that for all `x` in `t`, `f(x)` is in `t`, establishing that `f` maps `t` to itself.
* Given that `t` is a subset of `s`, the goal is to show that `f` is an involution on `t`.
* The proof uses `REWRITE_TAC` to unfold the definition of `involution` and `SUBSET`, and then applies `MESON_TAC` to deduce the conclusion from the given premises, leveraging the properties of involutions and subsets.

### Mathematical insight
This theorem is important because it allows us to restrict the domain of an involution from a larger set `s` to a smaller subset `t`, as long as the function `f` maps `t` into itself. This is useful in various mathematical contexts where one needs to study the properties of functions on subsets of their original domain.

### Dependencies
* `involution`
* `SUBSET`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles subset relations and function properties. Specifically, ensure that the definitions of `involution` and `SUBSET` are correctly translated and that the proof steps, particularly the unfolding of definitions and the application of meson (or equivalent), are appropriately adapted to the target system's tactics and automation capabilities.

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
* The proof starts by assuming a finite set `s` and a function `f` that is an `involution` on `s`, with the additional property that `f(x)` is never equal to `x` for any `x` in `s`.
* The `involution` property of `f` implies that `f` is its own inverse, meaning that for all `x` in `s`, `f(f(x)) = x`.
* The proof then likely leverages the fact that an involution without fixed points (i.e., `f(x) ≠ x` for all `x` in `s`) can only exist if the set `s` can be partitioned into pairs of elements that map to each other under `f`.
* The use of `REWRITE_TAC[involution]` suggests that the proof involves rewriting the `involution` property to better apply it to the condition of no fixed points.
* The application of `MESON_TAC[INVOLUTION_EVEN_NOFIXPOINTS]` indicates that the proof concludes by applying a meson tactic (likely a form of automatic reasoning) that utilizes a theorem or lemma named `INVOLUTION_EVEN_NOFIXPOINTS`, possibly establishing the even cardinality of `s` based on the pairing of elements under `f`.

### Mathematical insight
This theorem is important because it establishes a relationship between the existence of an involution without fixed points on a finite set and the parity of the set's cardinality. The key idea is that such an involution pairs up elements in the set, implying that the set must have an even number of elements for all elements to be paired.

### Dependencies
* `involution`
* `INVOLUTION_EVEN_NOFIXPOINTS`
* `FINITE`
* `CARD`
* `EVEN`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to how involutions and finite sets are defined and handled. The concept of an involution and the property of having no fixed points should be directly translatable, but the specific tactics used (e.g., `REWRITE_TAC`, `MESON_TAC`) may need to be reimplemented using the target system's tactics and automation. Additionally, ensure that the target system has equivalents for `FINITE`, `CARD`, and `EVEN` that are compatible with the formal development.

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
For all sets `s` and functions `f`, if `s` is finite and `f` is an involution on `s` and there exists a unique element `a` in `s` such that `f(a) = a`, then the cardinality of `s` is odd.

### Informal sketch
* Start by assuming `s` is finite, `f` is an involution on `s`, and there exists a unique `a` in `s` such that `f(a) = a`.
* Use the definition of `involution` to establish properties of `f` and its behavior on `s`.
* Apply the `SUBGOAL_THEN` tactic to consider the case where `s` is equal to the insertion of `a` into `s` minus `a`, and then apply `REWRITE_TAC` and `ASM_MESON_TAC` to simplify and derive conclusions.
* Utilize `ASM_SIMP_TAC` to simplify the expression involving `CARD s` and apply `MATCH_MP_TAC` with `INVOLUTION_EVEN` to derive the oddness of `CARD s`.
* Key HOL Light terms involved include `involution`, `FINITE`, `CARD`, `ODD`, and `INVOLUTION_EVEN`.

### Mathematical insight
This theorem provides insight into the structure of sets under involutions, specifically showing that if an involution has exactly one fixed point, then the domain of the involution must have an odd number of elements. This is important in understanding the properties of involutions and their applications in various mathematical structures.

### Dependencies
* Theorems:
  + `INVOLUTION_EVEN`
* Definitions:
  + `involution`
  + `FINITE`
  + `CARD`
  + `ODD`
  + `EXISTS_UNIQUE_DEF`
  + `EXTENSION`
  + `IN_INSERT`
  + `IN_DELETE`
  + `INVOLUTION_DELETE`
  + `FINITE_DELETE`
* Inductive rules: None

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to the handling of `involution`, `FINITE`, and `CARD`, as these may have different representations or requirements in other systems. Additionally, the use of `SUBGOAL_THEN` and `MATCH_MP_TAC` may need to be adapted to the tactical systems of the target proof assistant.

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
For all natural numbers `n` and sets `s`, if `s` is finite, `f` is an involution on `s`, and the cardinality of `s` is odd, then there exists an element `a` in `s` such that `f(a) = a`.

### Informal sketch
* The proof starts with the assumption that `s` is a finite set, `f` is an involution on `s`, and the cardinality of `s` is odd.
* The `REWRITE_TAC` tactic is used with `GSYM NOT_EVEN` to rewrite the oddness condition of the cardinality of `s` in terms of evenness, utilizing the fact that a number is odd if and only if it is not even.
* The `MESON_TAC` tactic is then applied with `INVOLUTION_EVEN` to deduce the existence of a fixed point `a` in `s` for the involution `f`, leveraging the properties of involutions and the parity of the set's cardinality.

### Mathematical insight
This theorem is important because it establishes a fundamental property of involutions on finite sets: if the set has an odd number of elements, then any involution on this set must have at least one fixed point. This result has implications in various areas of mathematics, including combinatorics, group theory, and graph theory, where involutions and their fixed points play significant roles.

### Dependencies
#### Theorems
* `INVOLUTION_EVEN`
#### Definitions
* `involution`
* `FINITE`
* `ODD`
* `CARD`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles finite sets, involutions, and cardinality. Specifically, ensure that the translation correctly captures the notion of involution and the parity of set cardinality. Additionally, the use of `REWRITE_TAC` and `MESON_TAC` tactics may need to be adapted to the target system's rewriting and proof search mechanisms.

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
For all functions `f` and `g` and all sets `s`, if `s` is finite and both `f` and `g` are involutions on `s`, and there exists a unique `x` in `s` such that `f(x) = x`, then there exists an `x` in `s` such that `g(x) = x`.

### Informal sketch
* Start by assuming the premises: `s` is finite, `f` and `g` are involutions on `s`, and there exists a unique `x` in `s` such that `f(x) = x`.
* Use the properties of involutions, specifically that an involution is its own inverse, to establish relationships between `f`, `g`, and the elements of `s`.
* Apply the `INVOLUTION_ODD` theorem to establish a key property about the behavior of involutions on finite sets.
* Further apply the `INVOLUTION_FIX_ODD` theorem to derive the existence of a fixed point for `g` based on the properties of `f` and the structure of `s`.
* Combine these insights to conclude the existence of an `x` in `s` such that `g(x) = x`, given the initial conditions.

### Mathematical insight
This theorem provides insight into the behavior of involutions on finite sets, specifically how the existence of a unique fixed point for one involution implies the existence of a fixed point for another involution on the same set. This is important in understanding the structural properties of functions on finite sets and has implications for various areas of mathematics and computer science where symmetry and inverse relations are crucial.

### Dependencies
#### Theorems
* `INVOLUTION_ODD`
* `INVOLUTION_FIX_ODD`
#### Definitions
* `involution`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles quantifiers, especially the unique existence quantifier `?!`. Additionally, the treatment of finite sets and functions may vary, so careful consideration of how `FINITE(s)` and `involution f s` are defined and used is necessary. The automation and tactic structure may also differ, so understanding the proof steps and how they are encoded in HOL Light tactics like `REPEAT STRIP_TAC`, `MATCH_MP_TAC`, and `ASM_REWRITE_TAC` will be essential for a successful port.

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
The `zset` function is defined as the set of all ordered triples `(x, y, z)` such that `x` squared plus `4` times `y` times `z` equals `a`.

### Informal sketch
* The definition of `zset` involves a set comprehension, which collects all triples `(x, y, z)` that satisfy the equation `x^2 + 4*y*z = a`.
* This equation is the core of the definition, and it is expected to be used in subsequent proofs or constructions involving `zset`.
* The `EXP` operator is used for exponentiation, and the equation is a simple polynomial equation involving the variables `x`, `y`, `z`, and the parameter `a`.

### Mathematical insight
The `zset` definition appears to be related to the formalization of a mathematical concept, possibly related to number theory or algebraic geometry, given the reference to "Zagier's one-sentence proof". The equation `x^2 + 4*y*z = a` suggests a connection to quadratic forms or Diophantine equations.

### Dependencies
* No explicit dependencies are listed in the given formal content, but it is likely that the definition relies on basic arithmetic operations and properties, such as `EXP` and multiplication, which are typically defined elsewhere in the HOL Light development.

### Porting notes
When translating this definition to other proof assistants, care should be taken to ensure that the set comprehension is handled correctly, and that the equation `x^2 + 4*y*z = a` is properly represented. Additionally, the `EXP` operator may need to be replaced with the equivalent operator in the target proof assistant.

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
        else (x - 2 * y,(x + z) - y, y)`
```

### Informal statement
The function `zag` is defined as a ternary relation that takes three arguments `x`, `y`, and `z`. It returns a triple based on the following conditions: 
- If `x + z` is less than `y`, then it returns the triple `(x + 2 * z, z, y - (x + z))`.
- Otherwise, if `x` is less than `2 * y`, then it returns the triple `(2 * y - x, y, (x + z) - y)`.
- If neither condition holds, it returns the triple `(x - 2 * y, (x + z) - y, y)`.

### Informal sketch
* The definition of `zag` involves conditional statements that check inequalities involving the input parameters `x`, `y`, and `z`.
* The function returns different triples based on these conditions, which suggests a piecewise definition.
* The conditions and the returned values imply a dependency on basic arithmetic operations and comparisons.
* To replicate this definition in another proof assistant, one would need to define a similar piecewise function, potentially using pattern matching or if-then-else constructs, depending on the target system's syntax and support for such definitions.

### Mathematical insight
The `zag` function appears to implement a specific transformation or relation between its inputs `x`, `y`, and `z`, with the output depending on the relative sizes of these inputs. The exact mathematical significance or purpose of this function would depend on the context in which it is used, such as in number theory, algebra, or as part of a larger algorithm.

### Dependencies
* No specific dependencies are listed in the given formal item, but the definition relies on basic arithmetic operations and comparisons, which are typically part of the core language or library of any proof assistant.

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, pay attention to how each system handles conditional definitions and arithmetic operations. Some systems may require explicit type annotations for `x`, `y`, and `z`, or may have different syntax for if-then-else statements. Additionally, consider how the target system handles tuples or triples, as the return type of `zag` is a triple.

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
* The definition of `tag` involves a simple reordering of the components of the input tuple.
* This is achieved by pattern matching on the input triple `(x, y, z)` and returning a new triple with `y` and `z` swapped.
* The definition does not involve any complex logical stages or proof steps, as it is a straightforward definition of a function.

### Mathematical insight
The `tag` function represents a basic permutation operation on tuples, which can be useful in various mathematical contexts, such as algebra, geometry, or combinatorics. This definition provides a simple way to swap the middle and last elements of a triple, which can be a necessary operation in certain proofs or constructions.

### Dependencies
* None

### Porting notes
When porting this definition to other proof assistants, note that the syntax for defining functions and pattern matching may differ. For example, in Lean, this definition might be written using the `def` keyword and pattern matching syntax, while in Coq, it might involve the `Definition` keyword and a `match` expression. Additionally, the `num` type may need to be replaced with the equivalent type in the target system (e.g., `Nat` in Lean or `nat` in Coq).

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
For all positive real numbers $x$, $y$, and $z$, if $x > 0$, $y > 0$, and $z > 0$, then applying the `zag` function twice to $(x, y, z)$ results in the original tuple $(x, y, z)$.

### Informal sketch
* The proof starts by assuming $x > 0$, $y > 0$, and $z > 0$.
* It then applies the definition of `zag` to `zag(x, y, z)` and simplifies using `REWRITE_TAC` with the `zag` definition.
* The process involves conditional case analysis using `COND_CASES_TAC` and simplification with `ASM_REWRITE_TAC`.
* After the first application of `zag` and simplification, it applies `zag` again and repeats the process of conditional case analysis and simplification.
* The proof then uses `REWRITE_TAC` with `PAIR_EQ` to establish the equality of the resulting pairs.
* Finally, it employs arithmetic reasoning with `ARITH_TAC` to conclude the proof.

### Mathematical insight
This theorem shows that the `zag` function is an involution when applied to positive real numbers, meaning applying it twice returns the original input. This property can be crucial in various mathematical constructions and proofs, especially where symmetries or inverse operations are involved.

### Dependencies
* `zag`
* `PAIR_EQ`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles conditional case analysis and arithmetic reasoning. Specifically, the equivalents of `COND_CASES_TAC`, `REWRITE_TAC`, and `ARITH_TAC` must be identified and applied appropriately. Additionally, ensure that the `zag` function and `PAIR_EQ` theorem are defined or imported correctly in the target system.

---

## IN_TRIPLE

### Name of formal statement
IN_TRIPLE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IN_TRIPLE = prove
 (`(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);
```

### Informal statement
For all `a`, `b`, and `c`, the triple `(a, b, c)` is an element of the set of all triples `(x, y, z)` such that `P x y z` holds if and only if `P a b c` holds.

### Informal sketch
* The proof involves rewriting the membership condition using the `IN_ELIM_THM` theorem to simplify the set membership expression.
* It then applies the `PAIR_EQ` theorem to handle the equality of pairs.
* The `MESON_TAC` tactic is used to automatically prove the resulting simplified statement, which involves basic logical deductions.
* The key steps mirror the structure of the formal proof, focusing on set membership, equality of pairs, and logical equivalence.

### Mathematical insight
This theorem provides a fundamental property of set membership for triples, allowing for the simplification of expressions involving sets defined by predicates. It is crucial for working with sets of tuples and predicates in a formal setting, as it establishes a direct relationship between set membership and the satisfaction of a predicate for the components of a tuple.

### Dependencies
* Theorems:
  + `IN_ELIM_THM`
  + `PAIR_EQ`
* Definitions:
  None
* Inductive rules:
  None

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to how set membership and predicate application are handled. The equivalent of `IN_ELIM_THM` and `PAIR_EQ` should be identified in the target system, and care should be taken to ensure that the automation provided by `MESON_TAC` is appropriately replaced, potentially requiring manual application of similar tactics or the use of a different automation mechanism.

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
* It first handles the case when `n` equals 0, using `PRIME_0` and `MULT_CLAUSES` to simplify.
* Then, it applies `REWRITE_TAC` with `prime`, `NOT_FORALL_THM`, and `DE_MORGAN_THM` to transform the statement.
* The case when `n` equals 1 is handled separately, using `ARITH` for simplification.
* The proof then proceeds to show that for any `n` greater than 1, `n` squared is not prime by exhibiting a divisor, utilizing `DIVIDES_LMUL` and `DIVIDES_REFL`.
* It simplifies further using `GEN_REWRITE_TAC` and `ARITH_RULE` to establish `n = n * 1`, and concludes with `ASM_SIMP_TAC` using `EQ_MULT_LCANCEL`.

### Mathematical insight
This theorem states that the square of any natural number is not a prime number. The key idea is to show that for any `n` greater than 1, `n` squared has at least one divisor other than 1 and itself, namely `n`. This is a fundamental property in number theory, highlighting the relationship between primality and multiplication.

### Dependencies
* Theorems:
  - `PRIME_0`
  - `prime`
  - `NOT_FORALL_THM`
  - `DE_MORGAN_THM`
  - `DIVIDES_LMUL`
  - `DIVIDES_REFL`
  - `EQ_MULT_LCANCEL`
* Definitions:
  - `prime`
  - `ARITH`
  - `MULT_CLAUSES`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to how each system handles quantifiers, case analysis, and arithmetic properties. Specifically, the use of `GEN_TAC`, `ASM_CASES_TAC`, and `REWRITE_TAC` may need to be adapted to the target system's tactics and rewriting mechanisms. Additionally, ensure that the `prime` definition and arithmetic properties like `MULT_CLAUSES` and `ARITH` are properly defined or imported in the target system.

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
For all natural numbers `n`, it is not the case that `4 * n` is a prime number.

### Informal sketch
* The proof starts by assuming an arbitrary `n` and aiming to show that `4 * n` is not prime.
* It then applies various simplifications and transformations using `REWRITE_TAC` with `prime`, `NOT_FORALL_THM`, and `DE_MORGAN_THM` to set up the proof.
* The `DISJ2_TAC` tactic is used to proceed with a case analysis, followed by `EXISTS_TAC `2`` to introduce a witness (in this case, the number 2) that will help demonstrate the composite nature of `4 * n`.
* Further simplifications are applied using `SUBST1_TAC` and `ASM_SIMP_TAC` with various theorems like `MULT_ASSOC`, `DIVIDES_RMUL`, `DIVIDES_REFL`, and `ARITH_EQ` to establish the relationship between `n`, `4`, and the witness `2`.
* A case analysis on whether `n` equals `0` is performed using `ASM_CASES_TAC `n = 0``, and the proof concludes with arithmetic manipulations facilitated by `POP_ASSUM MP_TAC` and `ARITH_TAC`.

### Mathematical insight
This theorem formalizes the intuitive fact that any number of the form `4 * n` (where `n` is a natural number) cannot be prime, because it can be divided by 2 (and 4, for `n > 0`), thus having more than two distinct positive divisors (1 and itself). This property is foundational in number theory and has implications for various theorems and proofs related to prime numbers and divisibility.

### Dependencies
* Theorems:
  - `prime`
  - `NOT_FORALL_THM`
  - `DE_MORGAN_THM`
  - `MULT_ASSOC`
  - `DIVIDES_RMUL`
  - `DIVIDES_REFL`
  - `ARITH_EQ`
* Definitions:
  - `prime`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles quantifiers, arithmetic, and the `prime` predicate. Specifically, the use of `GEN_TAC`, `REWRITE_TAC`, `DISJ2_TAC`, `EXISTS_TAC`, and arithmetic tactics may have direct or analogous counterparts in the target system. However, the exact formulation of the `prime` definition and the arithmetic properties used (`MULT_ASSOC`, `DIVIDES_RMUL`, etc.) may require adjustments to match the target system's library and syntax.

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
* The proof starts by assuming the negation of the conclusion using `CONTRAPOS_CONV`, which involves assuming that at least one of `x`, `y`, or `z` is not greater than 0.
* It then applies `DE_MORGAN_THM` and an arithmetic rule to simplify the negation of `0 < x` to `x = 0`.
* The proof proceeds by considering cases for each variable being 0 or not, using `DISJ_CASES_THEN` and substitution, aiming to derive a contradiction.
* Key rewrites involve expanding `EXP_2`, `MULT_CLAUSES`, `ADD_CLAUSES`, and properties of prime numbers (`PRIME_SQUARE` and `PRIME_4X`) to simplify the expression and reveal the contradiction.

### Mathematical insight
This theorem provides insight into the conditions under which an expression of the form `x^2 + 4yz` can yield a prime number, specifically requiring all variables `x`, `y`, and `z` to be positive. This has implications for number theory, particularly in the study of prime numbers and their constructions.

### Dependencies
* Theorems:
  - `DE_MORGAN_THM`
  - `PRIME_SQUARE`
  - `PRIME_4X`
* Definitions:
  - `EXP_2`
  - `MULT_CLAUSES`
  - `ADD_CLAUSES`
* Tactics:
  - `CONV_TAC`
  - `REWRITE_TAC`
  - `DISCH_THEN`
  - `REPEAT_TCL`
  - `DISJ_CASES_THEN`
  - `SUBST1_TAC`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles arithmetic, prime numbers, and the specific tactics used. For example, the equivalent of `CONTRAPOS_CONV` and the handling of `DE_MORGAN_THM` might differ. Additionally, the expansion of `EXP_2`, `MULT_CLAUSES`, and `ADD_CLAUSES` might be built-in or require separate proofs. The porting process will require understanding the logical structure and how to mirror it in the target system, potentially leveraging its specific tactics and automation features.

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
* The proof begins by assuming a prime number `p` and applying the definition of `involution` to `zag` and `zset(p)`.
* It then proceeds with a case analysis using `COND_CASES_TAC`, examining different conditions under which `zag` operates on elements of `zset(p)`.
* The proof utilizes `ASM_REWRITE_TAC` to simplify expressions involving `IN_TRIPLE` and applies various arithmetic properties (`INT_OF_NUM_EQ`, `INT_OF_NUM_ADD`, `EXP_2`, `INT_OF_NUM_MUL`, `INT_OF_NUM_SUB`, `LT_IMP_LE`) to manipulate these expressions.
* Additionally, it invokes `ZAG_INVOLUTION_GENERAL` as a lemma, combined with `PRIME_XYZ_NONZERO`, to establish the involution property of `zag` on `zset(p)`.

### Mathematical insight
This theorem establishes that for any prime `p`, the `zag` function exhibits an involution property when applied to the set `zset(p)`. This means that applying `zag` twice to any element in `zset(p)` returns the original element, which is a fundamental property in algebraic structures. The proof leverages the primality of `p` and specific properties of `zset(p)` and `zag` to demonstrate this involution.

### Dependencies
* Theorems:
  + `involution`
  + `ZAG_INVOLUTION_GENERAL`
  + `PRIME_XYZ_NONZERO`
* Definitions:
  + `zag`
  + `zset`
  + `IN_TRIPLE`
  + `FORALL_PAIR_THM`
* Other:
  + `INT_OF_NUM_EQ`
  + `INT_OF_NUM_ADD`
  + `EXP_2`
  + `INT_OF_NUM_MUL`
  + `INT_OF_NUM_SUB`
  + `LT_IMP_LE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles involution properties, prime numbers, and set definitions. Specifically, ensure that the `zag` function and `zset` are defined similarly, and that the proof assistant's arithmetic libraries support the necessary properties (`INT_OF_NUM_EQ`, etc.). Additionally, consider how case analysis and lemma application (`MATCH_MP_TAC`) are handled, as these may differ between systems.

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
For all `a`, the `tag` function is an involution on the set `zset a`.

### Informal sketch
* The proof starts by assuming an arbitrary `a` and aims to show that `tag` is an involution on `zset a`.
* It then applies rewriting using the definitions of `involution`, `tag`, `zset`, and `FORALL_PAIR_THM` to transform the goal.
* Next, it applies further rewriting using the `IN_TRIPLE` and `MULT_AC` theorems to simplify the expression.
* The use of `REWRITE_TAC` indicates that the proof relies on equational reasoning and substitution.
* Key HOL Light terms involved include `involution`, `tag`, `zset`, `FORALL_PAIR_THM`, `IN_TRIPLE`, and `MULT_AC`.

### Mathematical insight
This theorem establishes that the `tag` function has a specific symmetric property when applied to elements of `zset a`, for any `a`. This is important because it provides a guarantee about the behavior of `tag` that can be used in further proofs, particularly those involving set operations or properties of `zset`.

### Dependencies
* Theorems:
  + `involution`
  + `tag`
  + `zset`
  + `FORALL_PAIR_THM`
  + `IN_TRIPLE`
  + `MULT_AC`
* Definitions:
  + `involution`
  + `tag`
  + `zset`

### Porting notes
When porting this theorem to another proof assistant, special attention should be given to how the `involution` property is defined and how rewriting tactics are handled. The use of `REWRITE_TAC` with specific theorems indicates a reliance on equational reasoning, which may need to be replicated using similar tactics in the target system. Additionally, ensuring that the `tag` and `zset` functions are defined and behave similarly in the target system is crucial for a successful port.

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
If `zag(x, y, z)` equals `(x, y, z)`, then `y` equals `x`. This statement involves the `zag` function and asserts an equality condition under a specific functional equation.

### Informal sketch
* The proof starts by applying the `REWRITE_TAC` tactic to rewrite the `zag` function and `INT_POW_2` using their definitions, aiming to simplify the given equation.
* It then repeatedly applies `COND_CASES_TAC` to break down conditional statements and `ASM_SIMP_TAC` with `PAIR_EQ` to simplify equalities involving pairs, which helps in manipulating the equation to derive the conclusion.
* The `POP_ASSUM_LIST` tactic is used in combination with `MP_TAC` and `end_itlist CONJ` to manage assumptions and derive a conjunction, which is then used to apply `ARITH_TAC` for arithmetic reasoning to reach the final conclusion that `y` equals `x`.

### Mathematical insight
This theorem provides insight into the properties of the `zag` function, particularly under conditions where it acts as an identity function for its input. The `zag` function seems to be involved in establishing or utilizing a specific relationship between its inputs `x`, `y`, and `z`, and this lemma clarifies a key aspect of this relationship, namely that under the given condition, `y` must equal `x`. This could be crucial in further deductions involving the `zag` function.

### Dependencies
* `zag`
* `INT_POW_2`
* `PAIR_EQ`

### Porting notes
When translating this into another proof assistant like Lean, Coq, or Isabelle, pay close attention to how each system handles rewriting, conditional case analysis, and arithmetic reasoning. Specifically, the equivalents of `REWRITE_TAC`, `COND_CASES_TAC`, `ASM_SIMP_TAC`, and `ARITH_TAC` need to be identified and applied appropriately. Additionally, the representation of the `zag` function and the `INT_POW_2` and `PAIR_EQ` theorems must be correctly translated to ensure the proof goes through.

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
For all `x`, `y`, `z`, and `p`, if `0` is less than `y` and `0` is less than `z`, and `x` squared plus `4` times `y` times `z` equals `p`, then `x` is less than or equal to `p`, `y` is less than or equal to `p`, and `z` is less than or equal to `p`.

### Informal sketch
* The proof starts by assuming the given conditions: `0 < y`, `0 < z`, and `x^2 + 4*y*z = p`.
* It then uses the `CONJ_TAC` tactic to split the goal into two parts: `x <= p` and `y <= p /\ z <= p`.
* To prove `x <= p`, it applies `MESON_TAC` with relevant arithmetic rules (`EXP_2`, `LE_SQUARE_REFL`, and an arithmetic rule about inequalities).
* For `y <= p /\ z <= p`, it first uses `MATCH_MP_TAC` with an arithmetic rule about transitive inequalities, then applies `GEN_REWRITE_TAC` and `MULT_SYM` to rearrange terms.
* The proof continues with `REWRITE_TAC` and `ASM_REWRITE_TAC` to simplify inequalities, using rules like `LE_MULT_RCANCEL` and `ARITH_RULE` to derive the final conclusions.

### Mathematical insight
This theorem provides a bound on the values of `x`, `y`, and `z` in terms of `p`, under certain conditions. It is likely used in further proofs to limit the range of possible values for these variables, which can be crucial in mathematical derivations involving inequalities and arithmetic operations.

### Dependencies
* Theorems:
 + `EXP_2`
 + `LE_SQUARE_REFL`
 + `ARITH_RULE `(a <= b ==> a <= b + c)`
 + `ARITH_RULE `y <= z ==> y <= x + z`
 + `ARITH_RULE `y <= 4 * a * y <=> 1 * y <= (4 * a) * y`
 + `ARITH_RULE `0 < a ==> 1 <= 4 * a`
* Tactics:
 + `GEN_TAC`
 + `STRIP_TAC`
 + `FIRST_X_ASSUM`
 + `CONJ_TAC`
 + `MESON_TAC`
 + `MATCH_MP_TAC`
 + `GEN_REWRITE_TAC`
 + `REWRITE_TAC`
 + `ASM_REWRITE_TAC`
 + `ASM_SIMP_TAC`

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
For all prime numbers `p`, the set `zset p` is finite.

### Informal sketch
* The proof starts by assuming `p` is a prime number and aims to show that `zset p` is finite.
* It uses the `FINITE_NUMSEG_LT` theorem to establish that the set of numbers less than `p + 1` is finite.
* Then, it applies the `FINITE_PRODUCT` theorem to show that the Cartesian product of this set with itself is also finite.
* The proof then uses the `FINITE_SUBSET` theorem to show that `zset p` is a subset of this product and therefore finite.
* Key steps involve using `REWRITE_TAC` to apply various definitions and theorems, such as `zset`, `SUBSET`, `FORALL_PAIR_THM`, and `IN_TRIPLE`.
* The proof also involves existential quantification over `x`, `y`, and `z` to establish the finiteness of `zset p` under the assumption that `p` is prime.
* The `ASM_MESON_TAC` tactic is used with `ZSET_BOUND` and `PRIME_XYZ_NONZERO` to conclude the proof.

### Mathematical insight
This theorem is important because it establishes a fundamental property of `zset p` for prime `p`, which is crucial in number theory. The finiteness of `zset p` has implications for various results in algebra and number theory, particularly those involving prime numbers and their properties.

### Dependencies
* Theorems:
  * `FINITE_NUMSEG_LT`
  * `FINITE_PRODUCT`
  * `FINITE_SUBSET`
  * `ZSET_BOUND`
  * `PRIME_XYZ_NONZERO`
* Definitions:
  * `zset`
  * `SUBSET`
  * `FORALL_PAIR_THM`
  * `IN_TRIPLE`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how these systems handle prime numbers, finiteness, and subset relations. The `REWRITE_TAC` and `ASM_MESON_TAC` tactics may have direct counterparts or require manual unfolding of definitions. Additionally, the use of `GEN_TAC`, `DISCH_TAC`, and `EXISTS_TAC` may need to be adapted based on the target system's approach to quantifiers and tacticals.

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
For all prime numbers `p` and integers `k`, if `p` is congruent to 1 modulo 4 (i.e., `p = 4 * k + 1`), then there exist integers `x` and `y` such that `p` can be expressed as the sum of two squares (`p = x^2 + y^2`).

### Informal sketch
* The proof starts by assuming `p` is a prime number and `p = 4 * k + 1` for some integer `k`.
* It then invokes the `INVOLUTION_FIX_FIX` theorem with `zag` to establish the existence of `x` and `y`.
* The proof proceeds by case analysis and substitution, using various theorems such as `ZAG_INVOLUTION`, `TAG_INVOLUTION`, and `ZSET_FINITE`.
* It also employs arithmetic properties and the definition of prime numbers to derive the existence of `x` and `y` such that `p = x^2 + y^2`.
* Key steps involve using `MATCH_MP_TAC` with `INVOLUTION_FIX_FIX`, `EXISTS_TAC` with `1, 1, k`, and `EQ_TAC` to establish the equality.

### Mathematical insight
This theorem is a classic result in number theory, stating that any prime number congruent to 1 modulo 4 can be expressed as the sum of two squares. The proof relies on clever use of involution and arithmetic properties to establish the existence of such `x` and `y`.

### Dependencies
* Theorems:
	+ `INVOLUTION_FIX_FIX`
	+ `ZAG_INVOLUTION`
	+ `TAG_INVOLUTION`
	+ `ZSET_FINITE`
	+ `LEFT_IMP_EXISTS_THM`
	+ `FORALL_PAIR_THM`
* Definitions:
	+ `prime`
	+ `zset`
	+ `tag`
	+ `EXP_2`
* Axioms and rules:
	+ `SIMP_TAC`
	+ `REPEAT`
	+ `STRIP_TAC`
	+ `SUBGOAL_THEN`
	+ `MP_TAC`
	+ `EXISTS_TAC`
	+ `ASM_SIMP_TAC`
	+ `ASM_MESON_TAC`
	+ `ARITH_RULE`
	+ `DIVIDES_RMUL`
	+ `DIVIDES_REFL`
	+ `EQ_MULT_LCANCEL`

### Porting notes
When porting this theorem to other proof assistants, pay attention to the handling of arithmetic and involution. The `INVOLUTION_FIX_FIX` theorem and its associated tactics may need to be adapted or reimplemented. Additionally, the use of `SIMP_TAC` and `REPEAT` may require equivalent tactics or strategies in the target system.

---

## PIGEONHOLE_LEMMA

### Name of formal statement
PIGEONHOLE_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PIGEONHOLE_LEMMA = prove
 (`!f:A->B g s t.
        FINITE(s) /\ FINITE(t) /\
        (!x. x IN s ==> f(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) /\
        (!x. x IN s ==> g(x) IN t) /\
        (!x y. x IN s /\ y IN s /\ (g x = g y) ==> (x = y)) /\
        CARD(t) < 2 * CARD(s)
        ==> ?x y. x IN s /\ y IN s /\ (f x = g y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (f:A->B) s`; `IMAGE (g:A->B) s`] CARD_UNION) THEN
  SUBGOAL_THEN `(CARD(IMAGE (f:A->B) s) = CARD s) /\
                (CARD(IMAGE (g:A->B) s) = CARD s)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[CARD_IMAGE_INJ]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  MATCH_MP_TAC(TAUT `(~a ==> c) /\ ~b ==> (a ==> b) ==> c`) THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `!t. t < 2 * s /\ p <= t ==> ~(p = s + s)`) THEN
  EXISTS_TAC `CARD(t:B->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE] THEN
  ASM_MESON_TAC[])
```

### Informal statement
For all functions `f` and `g` from set `s` to set `t`, if `s` and `t` are finite, `f` and `g` map elements of `s` to elements of `t`, `f` and `g` are injective (one-to-one), and the cardinality of `t` is less than twice the cardinality of `s`, then there exist elements `x` and `y` in `s` such that `f(x)` equals `g(y)`.

### Informal sketch
* The proof starts by assuming the premises: `s` and `t` are finite, `f` and `g` map `s` to `t`, and `f` and `g` are injective.
* It then applies the `CARD_UNION` theorem to the images of `f` and `g` over `s`, which leads to a contradiction if the cardinality of `t` is less than twice the cardinality of `s`, given the injectivity of `f` and `g`.
* The proof uses `REPEAT STRIP_TAC` to strip away the universal quantifiers and `MP_TAC` to apply the `CARD_UNION` theorem.
* It then uses `SUBGOAL_THEN` to establish that the cardinalities of the images of `f` and `g` over `s` are equal to the cardinality of `s`, leveraging the `CARD_IMAGE_INJ` theorem for injective functions.
* The `MATCH_MP_TAC` tactic is used with a tautology to derive a contradiction, showing that the assumption that no `x` and `y` satisfy `f(x) = g(y)` leads to a logical contradiction given the conditions on `t`'s cardinality.
* The proof concludes by finding `x` and `y` in `s` such that `f(x) = g(y)` must hold, given the previous steps and the properties of `f` and `g`.

### Mathematical insight
The Pigeonhole Lemma is a fundamental principle in combinatorial mathematics, stating that if `n` items are put into `m` containers, with `n > m`, then at least one container must contain more than one item. This theorem generalizes that idea to functions `f` and `g` from a set `s` to a set `t`, where `s` and `t` are finite, and `f` and `g` are injective. The key insight is that if `t` is too small compared to `s` (specifically, its cardinality is less than twice that of `s`), and given the injective nature of `f` and `g`, there must be overlaps in the images of `f` and `g` over `s`.

### Dependencies
* Theorems:
  + `CARD_UNION`
  + `CARD_IMAGE_INJ`
  + `FINITE_IMAGE`
  + `CARD_SUBSET`
* Definitions:
  + `FINITE`
  + `CARD`
  + `IMAGE`
  + `IN`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles finite sets, injective functions, and cardinalities. The `CARD_UNION` and `CARD_IMAGE_INJ` theorems, as well as the `FINITE_IMAGE` definition, may need to be adapted or proved anew in the target system. Additionally, the use of `REPEAT STRIP_TAC`, `MP_TAC`, `SUBGOAL_THEN`, and `MATCH_MP_TAC` tactics may have equivalents in other proof assistants, but their exact application could vary.

---

## PIGEONHOLE_LEMMA_P12

### Name of formal statement
PIGEONHOLE_LEMMA_P12

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PIGEONHOLE_LEMMA_P12 = prove
 (`!f g p.
        ODD(p) /\
        (!x. 2 * x < p ==> f(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y)) /\
        (!x. 2 * x < p ==> g(x) < p) /\
        (!x y. 2 * x < p /\ 2 * y < p /\ (g x = g y) ==> (x = y))
        ==> ?x y. 2 * x < p /\ 2 * y < p /\ (f x = g y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
  MP_TAC(ISPECL [`f:num->num`; `g:num->num`;
                 `{x:num | 2 * x < 2 * k + 1}`; `{x:num | x < 2 * k + 1}`]
         PIGEONHOLE_LEMMA) THEN
  REWRITE_TAC[ADD1; ARITH_RULE `2 * x < 2 * k + 1 <=> x < k + 1`] THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `2 * k + 1 < 2 * (k + 1)`])
```

### Informal statement
For all functions `f` and `g`, and for all odd numbers `p`, if:
- `f(x)` and `g(x)` are less than `p` whenever `2 * x` is less than `p`,
- `f(x)` and `g(x)` are injective over the domain where `2 * x` is less than `p`,
then there exist `x` and `y` such that `2 * x` is less than `p`, `2 * y` is less than `p`, and `f(x)` equals `g(y)`.

### Informal sketch
* The proof begins by assuming the premises about `f`, `g`, and `p`.
* It then uses the `ODD_EXISTS` property to derive a key insight about `p`.
* The `PIGEONHOLE_LEMMA` is applied to functions `f` and `g` with specific domain and codomain restrictions.
* The proof involves rewriting and simplifying using various arithmetic rules and properties of finite sets.
* Key steps involve:
  + Using `REPEAT GEN_TAC` to generalize the goal
  + Employing `DISCH_THEN` and `CONJUNCTS_THEN2` to manage assumptions
  + Applying `X_CHOOSE_THEN` to select a witness `k`
  + Utilizing `MP_TAC` with `PIGEONHOLE_LEMMA` to derive a crucial intermediate result
  + Simplifying with `REWRITE_TAC` using various theorems and rules

### Mathematical insight
This theorem is a variant of the pigeonhole principle, which states that if `n` items are put into `m` containers, with `n > m`, then at least one container must contain more than one item. Here, it's applied to functions `f` and `g` over a specific domain related to an odd number `p`, showing that under certain conditions, there must exist `x` and `y` such that `f(x)` equals `g(y)`, reflecting the principle's idea in a functional setting.

### Dependencies
* Theorems:
  + `ODD_EXISTS`
  + `PIGEONHOLE_LEMMA`
  + `ADD1`
  + `FINITE_NUMSEG_LT`
  + `CARD_NUMSEG_LT`
  + `IN_ELIM_THM`
* Definitions:
  + `ODD`
  + Arithmetic rules and properties

### Porting notes
When translating this into other proof assistants like Lean, Coq, or Isabelle, pay special attention to:
* The handling of quantifiers and binders, as different systems may have distinct approaches.
* The application of the pigeonhole principle, which might be formulated differently.
* The use of tacticals like `REPEAT`, `GEN_TAC`, `DISCH_THEN`, and `MP_TAC`, which have counterparts in other systems but might require adjustments in strategy.
* Arithmetic and set theory libraries, as the specific rules and theorems used (`ADD1`, `FINITE_NUMSEG_LT`, etc.) may have analogs but need to be identified and applied correctly in the target system.

---

## SQUAREMOD_INJ_LEMMA

### Name of formal statement
SQUAREMOD_INJ_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SQUAREMOD_INJ_LEMMA = prove
 (`!p x d. prime(p) /\ 2 * (x + d) < p /\
           ((x + d) * (x + d) + m * p = x * x + n * p)
           ==> (d = 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides d \/ p divides (2 * x + d)` MP_TAC THENL
   [MATCH_MP_TAC PRIME_DIVPROD THEN ASM_REWRITE_TAC[divides] THEN
    EXISTS_TAC `n - m:num` THEN REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC(ARITH_RULE `!a:num. (a + b + d = a + c) ==> (b = c - d)`) THEN
    EXISTS_TAC `x * x:num` THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN ARITH_TAC;
    DISCH_THEN(DISJ_CASES_THEN(MP_TAC o MATCH_MP DIVIDES_LE)) THEN
    SIMP_TAC[ADD_EQ_0] THEN UNDISCH_TAC `2 * (x + d) < p` THEN ARITH_TAC])
```

### Informal statement
For all prime numbers `p`, all numbers `x`, and all numbers `d`, if `2 * (x + d)` is less than `p` and the equation `(x + d) * (x + d) + m * p = x * x + n * p` holds, then `d` equals `0`.

### Informal sketch
* The proof starts by assuming the given conditions: `p` is prime, `2 * (x + d) < p`, and the equation `(x + d) * (x + d) + m * p = x * x + n * p` holds.
* It then proceeds to show that `d` must be `0` under these conditions, using a case analysis based on whether `p` divides `d` or `p` divides `2 * x + d`.
* In the first case, it uses the `PRIME_DIVPROD` theorem to derive a contradiction, leveraging the fact that `p` is prime and the properties of divisibility.
* In the second case, it applies the `DIVIDES_LE` theorem to further analyze the divisibility conditions and ultimately derive that `d` must be `0` to satisfy the given equation and conditions.
* Key steps involve using `MATCH_MP_TAC` to apply relevant theorems, `EXISTS_TAC` to introduce witnesses, and `ARITH_TAC` to perform arithmetic manipulations.

### Mathematical insight
This theorem provides insight into the properties of quadratic expressions modulo a prime `p`, specifically showing that under certain conditions, the difference `d` must be `0`. This has implications for understanding the behavior of quadratic functions in modular arithmetic and can be useful in various number theoretic and cryptographic applications.

### Dependencies
* Theorems:
  + `PRIME_DIVPROD`
  + `DIVIDES_LE`
  + `ARITH_RULE`
* Definitions:
  + `prime`
  + `divides`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to the handling of prime numbers, divisibility, and arithmetic properties. The `PRIME_DIVPROD` and `DIVIDES_LE` theorems may need to be restated or proved in the target system, and the arithmetic manipulations might require adjustments due to differences in how these systems handle arithmetic and equality. Additionally, the case analysis and introduction of witnesses might be expressed differently, depending on the proof assistant's tactics and term manipulation capabilities.

---

## SQUAREMOD_INJ

### Name of formal statement
SQUAREMOD_INJ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SQUAREMOD_INJ = prove
 (`!p. prime(p)
   ==> (!x. 2 * x < p ==> (x EXP 2 + a) MOD p < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\
              ((x EXP 2 + a) MOD p = (y EXP 2 + a) MOD p)
              ==> (x = y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `x < a ==> ~(a = 0)`)) THEN
  ASM_SIMP_TAC[DIVISION] THEN
  SUBGOAL_THEN
   `(x EXP 2 + a = (x EXP 2 + a) DIV p * p + (x EXP 2 + a) MOD p) /\
    (y EXP 2 + a = (y EXP 2 + a) DIV p * p + (y EXP 2 + a) MOD p)`
  MP_TAC THENL [ASM_SIMP_TAC[DIVISION]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(x2 + a = xp + b:num) /\ (y2 + a = yp + b)
    ==> (x2 + yp = y2 + xp)`)) THEN
  DISJ_CASES_THEN MP_TAC (SPECL [`x:num`; `y:num`] LE_CASES) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS])
  THENL [ONCE_REWRITE_TAC[EQ_SYM_EQ]; ALL_TAC] THEN
  REWRITE_TAC[EXP_2; ARITH_RULE `(x + d = x) = (d = 0)`] THEN
  ASM_MESON_TAC[SQUAREMOD_INJ_LEMMA])
```

### Informal statement
For all prime numbers `p`, if `x` is less than `p/2`, then `(x^2 + a) mod p` is less than `p`. Furthermore, for all `x` and `y` less than `p/2`, if `(x^2 + a) mod p` equals `(y^2 + a) mod p`, then `x` equals `y`.

### Informal sketch
* The proof starts by assuming a prime number `p` and then breaks down into two main parts: 
  * Showing that for any `x` less than `p/2`, `(x^2 + a) mod p` is less than `p`. This involves using the `DIVISION` theorem to express `(x^2 + a)` in terms of its quotient and remainder when divided by `p`.
  * Proving that if `(x^2 + a) mod p` equals `(y^2 + a) mod p` for `x` and `y` less than `p/2`, then `x` equals `y`. This part of the proof uses the `LE_CASES` theorem to consider the relationship between `x` and `y`, and applies the `SQUAREMOD_INJ_LEMMA` to derive the conclusion.

### Mathematical insight
This theorem establishes a property of quadratic residues modulo a prime `p`, specifically that certain quadratic expressions are injective (one-to-one) when `x` and `y` are restricted to be less than `p/2`. This is important in number theory and has implications for various cryptographic and coding theoretic applications.

### Dependencies
* Theorems: 
  * `ARITH_RULE`
  * `LE_CASES`
  * `SQUAREMOD_INJ_LEMMA`
* Definitions: 
  * `EXP_2` 
  * `DIVISION` 

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, special attention should be paid to how each system handles modular arithmetic, prime numbers, and the `EXP_2` function. Additionally, the `SQUAREMOD_INJ_LEMMA` and other dependencies must be either ported or proven within the target system. The use of `REPEAT STRIP_TAC` and other tactics may need to be adapted, as different proof assistants have varying levels of automation and tactic languages.

---

## REFLECT_INJ

### Name of formal statement
REFLECT_INJ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let REFLECT_INJ = prove
 (`(!x. 2 * x < p ==> f(x) < p) /\
   (!x y. 2 * x < p /\ 2 * y < p /\ (f x = f y) ==> (x = y))
   ==> (!x. 2 * x < p ==> p - 1 - f(x) < p) /\
       (!x y. 2 * x < p /\ 2 * y < p /\ (p - 1 - f(x) = p - 1 - f(y))
              ==> (x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * x < p ==> p - 1 - y < p`] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE
   `x < p /\ y < p /\ (p - 1 - x = p - 1 - y) ==> (x = y)`) THEN
  ASM_MESON_TAC[])
```

### Informal statement
For all `x`, if `2 * x` is less than `p` and `f(x)` is less than `p`, and for all `x` and `y`, if `2 * x` and `2 * y` are less than `p` and `f(x)` equals `f(y)`, then `x` equals `y`. Then, for all `x`, if `2 * x` is less than `p`, `p - 1 - f(x)` is less than `p`, and for all `x` and `y`, if `2 * x` and `2 * y` are less than `p` and `p - 1 - f(x)` equals `p - 1 - f(y)`, then `x` equals `y`.

### Informal sketch
* The proof starts by assuming the antecedent of the implication, which includes two conditions: 
  - For all `x`, if `2 * x` is less than `p`, then `f(x)` is less than `p`.
  - For all `x` and `y`, if `2 * x` and `2 * y` are less than `p` and `f(x)` equals `f(y)`, then `x` equals `y`.
* The `REPEAT GEN_TAC` and `STRIP_TAC` steps are used to generalize and strip the implications.
* The `REWRITE_TAC` step applies an arithmetic rule to rewrite the condition `2 * x < p` as `p - 1 - y < p`.
* The `MATCH_MP_TAC` and `ASM_REWRITE_TAC` steps are used to apply the assumption and rewrite the conclusion.
* The `MATCH_MP_TAC` with `ARITH_RULE` is used to prove that if `x` and `y` are less than `p` and `p - 1 - x` equals `p - 1 - y`, then `x` equals `y`.
* The final `ASM_MESON_TAC` step is used to discharge any remaining subgoals.

### Mathematical insight
This theorem shows that a reflection modulo `p` retains a certain property. Specifically, it states that if a function `f` satisfies two conditions, then the reflected function `p - 1 - f(x)` also satisfies these conditions. The conditions are related to the injectivity of the function and the boundedness of its output.

### Dependencies
* `ARITH_RULE`
* Basic properties of arithmetic and equality

### Porting notes
When porting this theorem to another proof assistant, note that the `REPEAT` and `ASM_` tactics may need to be replaced with equivalent constructs. Additionally, the `ARITH_RULE` may need to be replaced with a similar rule or axiom in the target system. The use of `MATCH_MP_TAC` and `ASM_REWRITE_TAC` may also require careful handling, as the exact syntax and behavior of these tactics may vary between systems.

---

## LAGRANGE_LEMMA_ODD

### Name of formal statement
LAGRANGE_LEMMA_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_LEMMA_ODD = prove
 (`!a p. prime(p) /\ ODD(p)
         ==> ?n x y. 2 * x < p /\ 2 * y < p /\
                     (n * p = x EXP 2 + y EXP 2 + a + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL [ASM_MESON_TAC[ODD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. (x EXP 2 + a) MOD p`;
                 `\x. p - 1 - (x EXP 2 + 0) MOD p`; `p:num`]
                PIGEONHOLE_LEMMA_P12) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
     `(a /\ b) /\ (c /\ d) ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [ALL_TAC; MATCH_MP_TAC REFLECT_INJ] THEN
    ASM_MESON_TAC[SQUAREMOD_INJ]; ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `(x = p - 1 - y) ==> y < p ==> (x + y + 1 = p)`)) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `p:num` o AP_TERM `(MOD)`) THEN
  SUBGOAL_THEN
   `((x EXP 2 + a) MOD p + (y EXP 2 + 0) MOD p + 1) MOD p =
    (x EXP 2 + y EXP 2 + a + 1) MOD p`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
    EXISTS_TAC `(x EXP 2 + a) DIV p + (y EXP 2) DIV p` THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE
      `(x2 + a = xd * p + xm) /\ (y2 = yd * p + ym)
       ==> (x2 + y2 + a + 1 = (xm + ym + 1) + (xd + yd) * p)`) THEN
    ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
  SUBGOAL_THEN `p MOD p = 0` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN
    UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC
   [`(x EXP 2 + y EXP 2 + a + 1) DIV p`; `x:num`; `y:num`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPEC `x EXP 2 + y EXP 2 + a + 1` o
    MATCH_MP DIVISION) THEN
 ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN MESON_TAC[])
```

### Informal statement
For all integers `a` and prime numbers `p` where `p` is odd, there exist integers `n`, `x`, and `y` such that `2 * x` is less than `p`, `2 * y` is less than `p`, and `n * p` equals `x` squared plus `y` squared plus `a` plus 1.

### Informal sketch
* The proof starts by assuming `p` is not equal to 0 and `p` is odd.
* It then applies the `PIGEONHOLE_LEMMA_P12` to establish the existence of `x` and `y` satisfying certain conditions modulo `p`.
* The `REFLECT_INJ` and `SQUAREMOD_INJ` theorems are used to derive properties about `x` and `y`.
* The proof proceeds by applying arithmetic rules and modular arithmetic properties to simplify and derive the final equation involving `n`, `x`, `y`, `p`, and `a`.
* Key steps involve using `DIVISION` to establish relationships between the integers and applying `MOD_EQ` to simplify expressions involving modular arithmetic.

### Mathematical insight
This theorem is related to Lagrange's four-square theorem, which states that every natural number can be represented as the sum of four integer squares. This specific lemma focuses on the case where the number is odd and provides a representation involving two squares and an additional term. The proof relies on properties of prime numbers, modular arithmetic, and the pigeonhole principle to establish the existence of suitable `x` and `y`.

### Dependencies
* `prime`
* `ODD`
* `PIGEONHOLE_LEMMA_P12`
* `REFLECT_INJ`
* `SQUAREMOD_INJ`
* `DIVISION`
* `MOD_EQ`

### Porting notes
When porting this theorem to another proof assistant, pay special attention to the handling of modular arithmetic and the application of the pigeonhole principle. The `DIVISION` and `MOD_EQ` theorems may need to be adapted or re-proven in the target system. Additionally, the representation of prime numbers and oddness may differ, requiring adjustments to the assumptions and proof strategy.

---

## LAGRANGE_LEMMA

### Name of formal statement
LAGRANGE_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_LEMMA = prove
 (`!a p. prime(p)
         ==> ?n x y. 2 * x <= p /\ 2 * y <= p /\
                     (n * p = x EXP 2 + y EXP 2 + a)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `EVEN(p)` THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [prime]) THEN
    DISCH_THEN(MP_TAC o SPEC `2` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[EVEN_EXISTS; divides]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_EQ] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_CASES_TAC `EVEN(a)` THENL
     [UNDISCH_TAC `EVEN a` THEN REWRITE_TAC[EVEN_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `0`; `0`] THEN
      REWRITE_TAC[ARITH; ADD_CLAUSES] THEN ARITH_TAC;
      UNDISCH_TAC `~(EVEN(a))` THEN REWRITE_TAC[NOT_EVEN; ODD_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
      MAP_EVERY EXISTS_TAC [`k + 1`; `1`; `0`] THEN
      REWRITE_TAC[ARITH; ADD_CLAUSES] THEN ARITH_TAC];
    ASM_CASES_TAC `a = 0` THENL
     [MAP_EVERY EXISTS_TAC [`0`; `0`; `0`] THEN
      ASM_REWRITE_TAC[LE_0; ADD_CLAUSES; MULT_CLAUSES; EXP_2]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(a = 0) ==> (a = (a - 1) + 1)`)) THEN
    MP_TAC(SPECL [`a - 1`; `p:num`] LAGRANGE_LEMMA_ODD) THEN
    ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[LT_IMP_LE]])
```

### Informal statement
For all integers `a` and prime numbers `p`, there exist integers `n`, `x`, and `y` such that `2 * x` is less than or equal to `p`, `2 * y` is less than or equal to `p`, and `n * p` equals `x` squared plus `y` squared plus `a`.

### Informal sketch
* The proof begins by considering the case when `p` is even, using the `prime` definition to derive a contradiction since `2` is the only even prime number.
* It then proceeds to analyze the parity of `a`, considering both the cases when `a` is even and when `a` is odd, using the `EVEN` and `ODD` properties.
* For each case, it attempts to find suitable `n`, `x`, and `y` that satisfy the given conditions, utilizing `EXISTS_TAC` to introduce these variables and `REWRITE_TAC` to simplify expressions.
* When `a` is not zero, it applies a recursive approach, reducing `a` by `1` and invoking `LAGRANGE_LEMMA_ODD` to find a solution for the reduced case.
* The proof concludes by verifying the conditions for the found `n`, `x`, and `y`, ensuring they meet the required inequalities and equation.

### Mathematical insight
This theorem is a variation of Lagrange's four-square theorem, which states that any natural number can be represented as the sum of four integer squares. Here, it's adapted to involve a prime number `p` and an additional integer `a`, showcasing a deeper connection between number theory and the representation of numbers as sums of squares.

### Dependencies
#### Theorems
* `prime`
* `EVEN_EXISTS`
* `divides`
* `LAGRANGE_LEMMA_ODD`
#### Definitions
* `EXP_2`
* `EVEN`
* `ODD`

---

## AUBREY_THM_4

### AUBREY_THM_4
- Name of the formal statement: AUBREY_THM_4

### Type of the formal statement
- Theorem

### Formal Content
```ocaml
let AUBREY_THM_4 = prove
 (`(?q. ~(q = 0) /\
       ?a b c d.
            (&a / &q) pow 2 + (&b / &q) pow 2 +
            (&c / &q) pow 2 + (&d / &q) pow 2 = &N)
   ==> ?a b c d. &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2 = &N`,
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  ASM_CASES_TAC `m = 1` THENL
   [ASM_REWRITE_TAC[REAL_DIV_1; ARITH_EQ] THEN MESON_TAC[];
    STRIP_TAC THEN MP_TAC(SPEC `m:num` AUBREY_LEMMA_4) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]])
```

### Informal statement
For any non-zero rational number `q` and integers `a`, `b`, `c`, `d` such that `a^2/q^2 + b^2/q^2 + c^2/q^2 + d^2/q^2 = N`, there exist integers `a`, `b`, `c`, `d` such that `a^2 + b^2 + c^2 + d^2 = N`.

### Informal sketch
* The proof starts by assuming the existence of a non-zero rational number `q` and integers `a`, `b`, `c`, `d` satisfying the equation `a^2/q^2 + b^2/q^2 + c^2/q^2 + d^2/q^2 = N`.
* It then considers two cases: `m = 1` and `m ≠ 1`, where `m` is the denominator `q`.
* If `m = 1`, the equation simplifies to `a^2 + b^2 + c^2 + d^2 = N`, which directly satisfies the conclusion.
* If `m ≠ 1`, the proof applies the `AUBREY_LEMMA_4` to find a smaller `m'` and corresponding integers `n'`, `p'`, `q'`, `r'` such that `n'^2/m'^2 + p'^2/m'^2 + q'^2/m'^2 + r'^2/m'^2 = N`.
* The proof then uses this smaller `m'` to construct integers `a`, `b`, `c`, `d` satisfying `a^2 + b^2 + c^2 + d^2 = N`.

### Mathematical insight
The theorem shows that if a number `N` can be represented as the sum of four squares of rational numbers, then it can also be represented as the sum of four squares of integers. This result is a consequence of `AUBREY_LEMMA_4`, which provides a way to reduce the problem to a smaller denominator.

### Dependencies
* `AUBREY_LEMMA_4`
* `REAL_DIV_1`
* `ARITH_EQ`
* `num_WOP`

### Porting notes
When porting this theorem to other proof assistants, care should be taken to preserve the exact logical structure and quantifiers. The `AUBREY_LEMMA_4` lemma, which is used in the proof, may require special attention due to its recursive nature. Additionally, the use of `GEN_REWRITE_TAC` and `DISCH_THEN` tactics may need to be adapted to the target proof assistant's syntax and semantics.

---

## LAGRANGE_IDENTITY

### Name of formal statement
LAGRANGE_IDENTITY

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_IDENTITY = REAL_ARITH
  `(w1 pow 2 + x1 pow 2 + y1 pow 2 + z1 pow 2) *
   (w2 pow 2 + x2 pow 2 + y2 pow 2 + z2 pow 2) =
   (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2) pow 2 +
   (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2) pow 2 +
   (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2) pow 2 +
   (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2) pow 2`;;
```

### Informal statement
For all real numbers $w_1$, $x_1$, $y_1$, $z_1$, $w_2$, $x_2$, $y_2$, and $z_2$, the following equation holds: 
$(w_1^2 + x_1^2 + y_1^2 + z_1^2) \cdot (w_2^2 + x_2^2 + y_2^2 + z_2^2) = (w_1w_2 - x_1x_2 - y_1y_2 - z_1z_2)^2 + (w_1x_2 + x_1w_2 + y_1z_2 - z_1y_2)^2 + (w_1y_2 - x_1z_2 + y_1w_2 + z_1x_2)^2 + (w_1z_2 + x_1y_2 - y_1x_2 + z_1w_2)^2$.

### Informal sketch
* The proof involves expanding and simplifying the left-hand side of the equation using algebraic properties.
* It then involves rearranging and grouping terms to match the structure of the right-hand side.
* Key steps include applying the distributive property, combining like terms, and recognizing the emergence of the squared expressions on the right-hand side.
* The `REAL_ARITH` mechanism in HOL Light is likely used to handle the algebraic manipulations and to ensure the correctness of the equality.

### Mathematical insight
This statement is an instance of Lagrange's identity, which is a fundamental result in number theory and algebra. It relates the sum of squares of certain expressions to the sum of squares of other related expressions, and it has applications in various areas, including geometry, algebra, and analysis. The identity is important because it provides a way to simplify complex expressions and to establish relationships between different mathematical objects.

### Dependencies
* `REAL_ARITH`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of real arithmetic and the expansion of the left-hand side of the equation. The `REAL_ARITH` mechanism in HOL Light is used to handle the algebraic manipulations, so an equivalent mechanism or tactic should be used in the target system to ensure the correctness of the proof. Additionally, the use of automation, such as `REAL_ARITH`, may need to be replaced with manual proofs or different automation tactics in the target system.

---

## LAGRANGE_REAL_NUM

### Name of formal statement
LAGRANGE_REAL_NUM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_REAL_NUM = prove
 (`!n. ?w x y z. &n = &w pow 2 + &x pow 2 + &y pow 2 + &z pow 2`,
  let lemma = prove
   (`(?a. abs(w) = &a) /\ (?b. abs(x) = &b) /\
     (?c. abs(y) = &c) /\ (?d. abs(z) = &d)
     ==> ?a b c d. w pow 2 + x pow 2 + y pow 2 + z pow 2 =
                   &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2`,
    STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ABS_NUM] THEN
    MESON_TAC[]) in
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [REPEAT(EXISTS_TAC `0`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [EXISTS_TAC `1` THEN REPEAT(EXISTS_TAC `0`) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `p divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  ASM_CASES_TAC `m = 1` THENL
   [ALL_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(fun th ->
     MP_TAC(SPEC `p:num` th) THEN MP_TAC(SPEC `m:num` th)) THEN
    ONCE_REWRITE_TAC[ARITH_RULE `m < p * m <=> 1 * m < p * m`] THEN
    REWRITE_TAC[LT_MULT_RCANCEL] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `p < p * m <=> p * 1 < p * m`] THEN
    REWRITE_TAC[LT_MULT_LCANCEL] THEN
    UNDISCH_TAC `~(p * m = 0)` THEN REWRITE_TAC[MULT_EQ_0] THEN
    ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(p = 1)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 < x <=> ~(x = 0) /\ ~(x = 1)`] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`w1:num`; `x1:num`; `y1:num`; `z1:num`] THEN
    DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`w2:num`; `x2:num`; `y2:num`; `z2:num`] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[LAGRANGE_IDENTITY] THEN
    MATCH_MP_TAC lemma THEN REWRITE_TAC[REAL_OF_NUM_MUL] THEN
    MESON_TAC[REAL_INTEGER_CLOSURES]] THEN
  UNDISCH_TAC `m = 1` THEN DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[MULT_CLAUSES] THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LAGRANGE_LEMMA) THEN
  DISCH_THEN(MP_TAC o SPEC `1 EXP 2 + 0 EXP 2`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `x:num`; `y:num`] THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN MATCH_MP_TAC AUBREY_THM_4 THEN
  SUBGOAL_THEN `q * p < p EXP 2` MP_TAC THENL
   [ASM_REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(2 * x) * (2 * x) <= p * p /\ (2 * y) * (2 * y) <= p * p /\
      2 * 2 <= p * p
      ==> x * x + y * y + 1 < p * p`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`~(p = 0)`; `~(p = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXP_2; LT_MULT_RCANCEL] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`; `d:num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `0 * p = x EXP 2 + y EXP 2 + 1 EXP 2 + 0 EXP 2` THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[MULT_CLAUSES; EXP_2] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `&p = &q * &(q * p) / &q pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_ASSOC; real_div] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    SIMP_TAC[REAL_MUL_ASSOC; REAL_POW_EQ_0; REAL_MUL_LINV; REAL_MUL_LID;
             ASSUME `~(q = 0)`; REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; LAGRANGE_IDENTITY] THEN
  SUBST1_TAC(SYM(ASSUME
    `&q = &a pow 2 + &b pow 2 + &c pow 2 + &d pow 2`)) THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div; GSYM REAL_POW_DIV] THEN
  EXISTS_TAC `q:num` THEN REWRITE_TAC[ASSUME `~(q = 0)`] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN
  REWRITE_TAC[REAL_INV_EQ_0; REAL_POW_EQ_0; REAL_OF_NUM_EQ;
              ASSUME `~(q = 0)`] THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN MATCH_MP_TAC lemma THEN
  REWRITE_TAC[REAL_OF_NUM_MUL] THEN MESON_TAC[REAL_INTEGER_CLOSURES])
```

### Informal statement
For all natural numbers `n`, there exist integers `w`, `x`, `y`, and `z` such that `n` is equal to the sum of the squares of `w`, `x`, `y`, and `z`.

### Informal sketch
* The proof starts by considering the cases where `n` is `0` or `1`, in which case the statement is trivially true.
* For `n > 1`, the proof uses the `PRIME_FACTOR` theorem to find a prime `p` that divides `n`.
* It then considers two cases: `m = 1` and `m > 1`, where `m` is the quotient of `n` divided by `p`.
* In the case `m = 1`, the proof uses the `LAGRANGE_LEMMA` theorem to find integers `q`, `x`, `y`, and `z` such that `q^2 + x^2 + y^2 = p^2`.
* In the case `m > 1`, the proof uses the `AUBREY_THM_4` theorem to find integers `q`, `x`, `y`, and `z` such that `q^2 + x^2 + y^2 + 1 = p^2`.
* The proof then uses the `lemma` to rewrite the sum of squares in terms of the absolute values of `w`, `x`, `y`, and `z`.
* Finally, the proof uses the `REAL_INTEGER_CLOSURES` theorem to conclude that the sum of squares is equal to `n`.

### Mathematical insight
The Lagrange's four-square theorem states that every natural number can be represented as the sum of four integer squares. This theorem has important implications in number theory and has been used in various applications, including cryptography and coding theory. The proof of this theorem involves a combination of mathematical techniques, including the use of prime factorization, modular arithmetic, and the properties of integer squares.

### Dependencies
* Theorems:
	+ `PRIME_FACTOR`
	+ `LAGRANGE_LEMMA`
	+ `AUBREY_THM_4`
	+ `REAL_INTEGER_CLOSURES`
* Definitions:
	+ `REAL_OF_NUM`
	+ `REAL_POW`
	+ `REAL_ADD`
	+ `REAL_MUL`
	+ `REAL_DIV`
	+ `REAL_ABS`
	+ `REAL_POW2`
* Axioms:
	+ `REAL_OF_NUM_EQ`
	+ `REAL_POW_EQ`
	+ `REAL_ADD_EQ`
	+ `REAL_MUL_EQ`
	+ `REAL_DIV_EQ`
	+ `REAL_ABS_EQ`

### Porting notes
When porting this theorem to other proof assistants, care should be taken to ensure that the `REAL_OF_NUM` and `REAL_POW` functions are defined correctly, as they are used extensively in the proof. Additionally, the `PRIME_FACTOR` and `LAGRANGE_LEMMA` theorems may need to be proved separately in the target system. The use of `MATCH_MP_TAC` and `MP_TAC` tactics may also need to be adapted to the target system's tactic language.

---

## LAGRANGE_NUM

### Name of formal statement
LAGRANGE_NUM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_NUM = prove
 (`!n. ?w x y z. n = w EXP 2 + x EXP 2 + y EXP 2 + z EXP 2`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` LAGRANGE_REAL_NUM) THEN
  REWRITE_TAC[REAL_POS; REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ])
```

### Informal statement
For all natural numbers `n`, there exist integers `w`, `x`, `y`, and `z` such that `n` is equal to the sum of the squares of `w`, `x`, `y`, and `z`.

### Informal sketch
* The proof starts by considering an arbitrary natural number `n`.
* It then applies the `LAGRANGE_REAL_NUM` theorem, which is specialized to `n` using `SPEC`.
* The `GEN_TAC` and `MP_TAC` tactics are used to manage the quantifiers and apply the theorem.
* The `REWRITE_TAC` tactic is used to simplify the expression using various rewrite rules, including `REAL_POS`, `REAL_OF_NUM_POW`, `REAL_OF_NUM_ADD`, and `REAL_OF_NUM_EQ`.
* The key idea is to leverage the `LAGRANGE_REAL_NUM` theorem, which likely establishes a similar result for real numbers, and then use the rewrite rules to translate this result to the natural numbers.

### Mathematical insight
This theorem is a version of Lagrange's four-square theorem, which states that every natural number can be represented as the sum of four integer squares. This result is important in number theory and has numerous applications. The formal item `LAGRANGE_NUM` provides a precise statement and proof of this theorem within the HOL Light system.

### Dependencies
* Theorems:
	+ `LAGRANGE_REAL_NUM`
* Definitions:
	+ `EXP`
	+ `REAL_POS`
	+ `REAL_OF_NUM_POW`
	+ `REAL_OF_NUM_ADD`
	+ `REAL_OF_NUM_EQ`

### Porting notes
When translating this theorem to another proof assistant, special attention should be paid to the handling of quantifiers, rewrite rules, and the application of the `LAGRANGE_REAL_NUM` theorem. The `GEN_TAC` and `MP_TAC` tactics may need to be replaced with equivalent constructs in the target system. Additionally, the rewrite rules used in `REWRITE_TAC` may need to be redefined or replaced with similar rules in the target system.

---

## LAGRANGE_INT

### Name of formal statement
LAGRANGE_INT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LAGRANGE_INT = prove
 (`!a. &0 <= a <=> ?w x y z. a = w pow 2 + x pow 2 + y pow 2 + z pow 2`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`a:int`,`a:int`) THEN REWRITE_TAC[GSYM INT_FORALL_POS] THEN
    X_GEN_TAC `n:num` THEN MP_TAC(SPEC `n:num` LAGRANGE_REAL_NUM) THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    SIMP_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD] THEN
    MESON_TAC[];
    STRIP_TAC THEN ASM_SIMP_TAC[INT_LE_SQUARE; INT_LE_ADD; INT_POW_2]])
```

### Informal statement
For all integers `a`, `a` is greater than or equal to 0 if and only if there exist integers `w`, `x`, `y`, and `z` such that `a` equals the sum of the squares of `w`, `x`, `y`, and `z`.

### Informal sketch
* The proof proceeds by first assuming `a` is greater than or equal to 0 and then finding `w`, `x`, `y`, and `z` such that `a` equals the sum of their squares.
* It uses a generalization tactic (`GEN_TAC`) and then splits into two cases using `EQ_TAC`.
* In the first case, it specializes the assumption to `a` being a positive integer, rewrites the assumption using `GSYM INT_FORALL_POS`, and then applies `LAGRANGE_REAL_NUM` to find suitable `w`, `x`, `y`, and `z`.
* The second case involves stripping the assumption that `a` is greater than or equal to 0 and then simplifying using `INT_LE_SQUARE`, `INT_LE_ADD`, and `INT_POW_2`.
* Key HOL Light terms used include `SPEC_TAC`, `REWRITE_TAC`, `MP_TAC`, `SIMP_TAC`, and `MESON_TAC`, which facilitate the manipulation of the formal expressions and application of relevant theorems.

### Mathematical insight
This theorem, known as Lagrange's Four-Square Theorem, states that every non-negative integer can be represented as the sum of four perfect squares. The proof involves showing that this representation exists for all non-negative integers, leveraging the `LAGRANGE_REAL_NUM` theorem, which likely provides a similar result for real numbers or a related property.

### Dependencies
* Theorems:
  + `LAGRANGE_REAL_NUM`
* Definitions:
  + `INT_OF_NUM_EQ`
  + `INT_OF_NUM_POW`
  + `INT_OF_NUM_ADD`
  + `REAL_OF_NUM_POW`
  + `REAL_OF_NUM_ADD`
  + `REAL_OF_NUM_EQ`
* Tactics and rules:
  + `GEN_TAC`
  + `EQ_TAC`
  + `SPEC_TAC`
  + `REWRITE_TAC`
  + `MP_TAC`
  + `SIMP_TAC`
  + `MESON_TAC`
  + `STRIP_TAC`
  + `ASM_SIMP_TAC`

### Porting notes
When translating this theorem into another proof assistant, special attention should be paid to the handling of integers, real numbers, and the `LAGRANGE_REAL_NUM` theorem, as the representation and properties of these may differ between systems. Additionally, the use of `MESON_TAC` for automated reasoning may need to be replaced with equivalent tactics or manual proofs, depending on the capabilities of the target system.

---

