# four_squares.ml

## Overview

Number of statements: 36

`four_squares.ml` proves theorems about representing numbers as sums of squares, specifically sums of 2 and 4 squares. It relies on prime number theory and real analysis. The file contributes to number theory within the HOL Light library by formalizing results on sums-of-squares representations.


## involution

### Name of formal statement
- involution

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let involution = new_definition
  `involution f s = !x. x IN s ==> f(x) IN s /\ (f(f(x)) = x)`;;
```

### Informal statement
- Given a function `f` and a set `s`, `involution f s` is defined to be true if and only if for all `x`, if `x` is in `s`, then `f(x)` is in `s`, and `f(f(x))` is equal to `x`.

### Informal sketch
- The definition introduces a predicate `involution` that captures the properties of a function `f` being an involution on a set `s`.
- It states that `f` maps elements of `s` back into `s`, and that applying `f` twice to an element of `s` results in the original element.
- The definition directly expresses these two conditions as a universal quantification over elements `x` and a conditional statement.
- The two conditions are a set membership condition `f(x) IN s` and the involution property `f(f(x)) = x`.

### Mathematical insight
- The `involution` definition formalizes the notion of an involutive function with respect to a particular set. An involution is a function that is its own inverse. This concept is useful in various mathematical areas, such as group theory, linear algebra, and combinatorics.
- This definition provides a way to formally reason about involutions within the HOL Light theorem prover.

### Dependencies
- `IN` (set membership)


---

## INVOLUTION_IMAGE

### Name of formal statement
INVOLUTION_IMAGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_IMAGE = prove
 (`!f s. involution f s ==> (IMAGE f s = s)`,
  REWRITE_TAC[involution; EXTENSION; IN_IMAGE] THEN MESON_TAC[]);;
```
### Informal statement
For all functions `f` and sets `s`, if `f` is an involution on `s`, then the image of `s` under `f` is equal to `s`.

### Informal sketch
The proof proceeds as follows:
- Assume that `f` is an involution on `s`. This means that for all `x` in `s`, `f(f(x)) = x`.
- We need to show that `IMAGE f s = s`. This is proved by showing mutual inclusion: `IMAGE f s` is a subset of `s` and `s` is a subset of `IMAGE f s`.
- To prove `IMAGE f s` is a subset of `s`, we consider an arbitrary element `y` in `IMAGE f s`. By the definition of `IMAGE`, there exists an `x` in `s` such that `f(x) = y`. Since `f` is an involution on `s`, if `x` is in `s`, then `f(x)` is in `s`. Thus, `y` is in `s`.
- To prove `s` is a subset of `IMAGE f s`, we consider an arbitrary element `x` in `s`. Since `f` is an involution, `f(f(x)) = x`. This means that `x` is the image of `f(x)` under `f`. Since `x` is in `s` and `f` is an involution, `f(x)` is also in `s`. Therefore, `x` is in `IMAGE f s`.
- Having shown the mutual inclusions, we conclude that `IMAGE f s = s`.

### Mathematical insight
This theorem states a fundamental property of involutions: applying an involution to a set does not change the set. This is because an involution is its own inverse (when restricted to the set), so the image contains the same elements as the original set.

### Dependencies
- Definitions:
  - `involution`
  - `IMAGE`

- Theorems:
  - `EXTENSION`
  - `IN_IMAGE`


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
If `f` is an involution on the set `s`, and `a` is an element of `s` such that `f a = a`, then `f` is an involution on the set obtained by deleting `a` from `s`.

### Informal sketch
The proof proceeds by rewriting the definition of `involution` and the membership condition `IN_DELETE` after deleting an element, and then uses a Meson tactic to automatically discharge the resulting goal.
- Assume `f` is an involution on `s`, `a` is in `s`, and `f a = a`.
- Show that `f` is an involution on `s DELETE a`.
- This requires showing that for all `x` in `s DELETE a`, it holds that `f (f x) = x` and `f x` is also in `s DELETE a`.
- The proof uses the definition of `involution` (`involution f s` is `forall x. x IN s ==> f x IN s /\ f (f x) = x`) and the definition of `IN_DELETE` (`x IN (s DELETE a)` is equivalent to `x IN s /\ x != a`).
- The MESON tactic then uses the properties of `f` being an involution on `s` and `a` being a fixed point of `f` to establish that `f` is an involution on `s DELETE a`.

### Mathematical insight
The theorem states that if an involution `f` has a fixed point `a` in a set `s`, then removing `a` from `s` preserves the involution property of `f` on the remaining set. This is because the involution property requires that `f(f(x)) = x` and that `f(x)` stays within the set. When `a` is removed, the involution property still holds for the other elements because `f(a)=a` doesn't play a role in the involution of other elements.

### Dependencies
- `involution`
- `IN_DELETE`


---

## INVOLUTION_STEPDOWN

### Name of formal statement
INVOLUTION_STEPDOWN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_STEPDOWN = prove
 (`involution f s /\ a IN s ==> involution f (s DIFF {a, (f a)})`,
  REWRITE_TAC[involution; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;
```
### Informal statement
For any function `f` and set `s`, if `f` is an involution on `s` and `a` is an element of `s`, then `f` is an involution on the set `s` with the elements `a` and `f a` removed.

### Informal sketch
The proof demonstrates that removing an element `a` and its image `f a` from a set `s` preserves the involution property of `f` on the resulting set.

- The proof starts with the assumption that `f` is an involution on `s` and `a` is an element of `s`.
- It aims to show that `f` is an involution on the set `s` with the elements `a` and `f a` removed ( `s DIFF {a, (f a)}` ).
- Expanding the definition of `involution` states that for all `x` in the new set `s DIFF {a, f a}`, `f x` is also in `s DIFF {a, f a}`, and `f (f x) = x`.
- To prove `f x` is in `s DIFF {a, f a}`, we use the facts that `f` is an involution on `s` (so `f x` is in `s`) and `x` is not equal to `a` and `x` is not equal to `f a`. If `f x` were equal to `a`, then `f (f x)` would be `f a`, and since `f (f x) = x`, we would have `x = f a`, which is a contradiction. Similarly, if `f x` were equal to `f a`, then `f (f x)` would be `f (f a)`, which is `a`. Thus `x = a` which is a contradiction, because `x` belongs to `s DIFF {a, f a}`. The proof uses properties of set difference (`IN_DIFF`), set insertion (`IN_INSERT`), elementary set theory (`NOT_IN_EMPTY`), and the definition of `involution`.

### Mathematical insight
This theorem provides a method for reducing the size of the set on which a function is an involution. If we know `f` is an involution on `s`, and `s` is finite, we can iteratively remove pairs of elements `a` and `f a` until we are left with a set where `f` may no longer be an involution (e.g., the empty set, or a singleton set `x` where `f x = x`). This is a useful lemma for proving properties about involutions on finite sets through induction, simplification, or case splitting.

### Dependencies
- `involution`
- `IN_DIFF`
- `IN_INSERT`
- `NOT_IN_EMPTY`


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
  REWRITE_TAC[involution; IN_ELIM_THM] THEN MESON_TAC[]);;
```
### Informal statement
If `f` is an involution on the set `s`, then `f` is also an involution on the set of elements `x` in `s` for which `f x` is not equal to `x`.

### Informal sketch
The proof proceeds as follows:
- Assume `involution f s`.
- Show that `involution f {x | x IN s /\ ~(f x = x)}` holds.
- Unfold the definition of `involution` and use set membership elimination.
- Apply a generic MESON tactic to complete the proof using propositional reasoning and equality.

### Mathematical insight
The theorem states that if a function `f` is an involution on a set `s` (i.e., applying `f` twice returns the original element), then `f` is also an involution when restricted to the subset of `s` that contains only elements which are not fixed points of `f`. This is because if `f` is an involution, applying `f` twice to any element in the subset will return the original element.

### Dependencies
- Definitions: `involution`
- Theorems: `IN_ELIM_THM`


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
  REWRITE_TAC[involution; SUBSET] THEN MESON_TAC[]);;
```
### Informal statement
For all functions `f`, and sets `s` and `t`, if `f` is an involution on `s` and for all `x`, if `x` is in `t` then `f(x)` is in `t`, and `t` is a subset of `s`, then `f` is an involution on `t`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is an involution on `s`. This means that for all `x` in `s`, `f(f(x)) = x`. Also assume that if `x` is in `t` then `f(x)` is in `t`, and that `t` is a subset of `s`.
- We need to show that `f` is an involution on `t`, i.e., for all `x` in `t`, `f(f(x)) = x`.
- Since `t` is a subset of `s`, if `x` is in `t`, then `x` is also in `s`.
- Because `f` is an involution on `s` and `x` is in `s`, we have `f(f(x)) = x`.
- Therefore, `f` is indeed an involution on `t`.
- The rewrite tactic uses the definitions of `involution` and `SUBSET` to rewrite the goal. `MESON_TAC` then uses first-order logic to complete the proof.

### Mathematical insight
The theorem states that if a function `f` is an involution on a set `s`, and a set `t` is a subset of `s` that is closed under `f` (i.e., `f(x)` is in `t` whenever `x` is in `t`), then `f` is also an involution on `t`. This is a natural and useful property when dealing with involutions, as it allows us to restrict the domain of the involution to a smaller, invariant subset without losing the involution property.

### Dependencies
Definitions:
- `involution`
- `SUBSET`


---

## INVOLUTION_EVEN

### Name of formal statement
INVOLUTION_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_EVEN = prove
 (`!s. FINITE(s) /\ involution f s /\ (!x:A. x IN s ==> ~(f x = x))
       ==> EVEN(CARD s)`,
  REWRITE_TAC[involution] THEN MESON_TAC[INVOLUTION_EVEN_NOFIXPOINTS]);;
```
### Informal statement
For all sets `s`, if `s` is finite, `f` is an involution on `s`, and for all `x` in `s`, `f(x)` is not equal to `x`, then the cardinality of `s` is even.

### Informal sketch
The proof proceeds by rewriting with the definition of `involution` and then using `INVOLUTION_EVEN_NOFIXPOINTS`. The core idea is that an involution without fixed points pairs up elements of the set, implying that the set's cardinality must be even.
- The `involution f s` property means that for all `x` in `s`, `f(x)` is in `s` and `f(f(x)) = x`.
- The condition `!x:A. x IN s ==> ~(f x = x)` states that `f` has no fixed points in `s`. This means that for every element `x` in `s`, `f(x)` is a distinct element in `s`. Therefore elements in S are paired up.
- Given that there are no fixed points and elements are paired under `f`, the cardinality of `s` must be even.

### Mathematical insight
This theorem formalizes the intuitive notion that an involution on a set, without any fixed points, implies that the cardinality of the set is even, because the involution pairs elements up. This result is fundamental in combinatorics and group theory when considering actions of groups and involutions.

### Dependencies
- Definitions:
  - `involution`
  - `FINITE`
  - `EVEN`
  - `CARD`
  - `IN`

- Theorems:
  - `INVOLUTION_EVEN_NOFIXPOINTS`


---

## INVOLUTION_FIX_ODD

### Name of formal statement
INVOLUTION_FIX_ODD

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[]);;
```
### Informal statement
If `s` is a finite set, `f` is an involution on `s`, and there exists a unique element `a` in `s` such that `f a = a`, then the cardinality of `s` is odd.

### Informal sketch
The proof proceeds as follows:
- Start with the assumption that `s` is finite, `f` is an involution on `s`, and there exists a unique fixed point `a` in `s`.
- Show that `s` is equal to the insertion of `a` into the set obtained by deleting `a` from `s`; that is, `s = INSERT a (DELETE a s)`.
- Use properties of `CARD`, `FINITE_DELETE`, `IN_DELETE`, `ODD`, and `NOT_ODD` for simplification.
- Apply the theorem `INVOLUTION_EVEN`, which states that an involution on a finite set with no fixed points has an even cardinality.
- Simplify using properties of `INVOLUTION_DELETE`, `FINITE_DELETE`, and `IN_DELETE`.
- Complete the proof by discharging the assumptions using a decision procedure (`ASM_MESON_TAC`).

### Mathematical insight
The theorem states a fundamental property relating involutions, fixed points, and cardinality. An involution is a function that, when applied twice, returns the original value. The existence of a unique fixed point in the domain of an involution constrains the cardinality of the domain to be odd. This connection arises because elements other than the fixed point must be paired by the involution, contributing even numbers to the cardinality, while the sole fixed point adds one, making it odd.
### Dependencies
- Definitions:
  - `FINITE`
  - `involution`
  - `EXISTS_UNIQUE_DEF` (exists unique)
  - `IN`
  - `CARD`
  - `ODD`
- Theorems:
  - `EXTENSION`
  - `IN_INSERT`
  - `IN_DELETE`
  - `CARD_CLAUSES`
  - `FINITE_DELETE`
  - `NOT_ODD`
  - `INVOLUTION_EVEN`
  - `INVOLUTION_DELETE`
### Porting notes (optional)
- The proof relies on rewriting with standard set-theoretic identities and properties of cardinality. These should be available in most proof assistants. The key step is likely the application of `INVOLUTION_EVEN`, which may need to be ported separately.
- The automation via `ASM_MESON_TAC` handles the final reasoning step based on the simplifications. You may need to use a similar automated tactic or perform the reasoning manually depending on the capabilities of your target proof assistant.


---

## INVOLUTION_ODD

### Name of formal statement
INVOLUTION_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INVOLUTION_ODD = prove
 (`!n s. FINITE(s) /\ involution f s /\ ODD(CARD s)
         ==> ?a. a IN s /\ (f a = a)`,
  REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[INVOLUTION_EVEN]);;
```
### Informal statement
For all sets `s` and functions `f`, if `s` is finite, `f` is an involution on `s`, and the cardinality of `s` is odd, then there exists an element `a` in `s` such that `f(a) = a`.

### Informal sketch
*   The theorem states that an involution on a finite set with an odd number of elements must have a fixed point.
*   The proof uses the theorem `INVOLUTION_EVEN`, implicitly stating that any involution that has no fixed points must have an even number of elements.
*   The given hypothesis `ODD(CARD s)` means that `NOT_EVEN(CARD s)`. The goal is to show that `?a. a IN s /\ (f a = a)`.
*   The tactic `REWRITE_TAC[GSYM NOT_EVEN]` rewrites the hypothesis to `NOT (EVEN(CARD s))`.
*   The tactic `MESON_TAC[INVOLUTION_EVEN]` then uses the `INVOLUTION_EVEN` theorem to prove the required existential goal.

### Mathematical insight

The key idea behind this theorem is that an involution pairs elements of a set, except for fixed points. If the set has an odd number of elements and the involution has no fixed points, then it's impossible to pair all the elements. Therefore, at least one fixed point must exist. This theorem is a standard result in combinatorics.

### Dependencies
- Theorems: `INVOLUTION_EVEN`
- Definitions: `FINITE`, `involution`, `ODD`, `CARD`, `IN`
- Tactics: `REWRITE_TAC`, `GSYM`, `MESON_TAC`, `NOT_EVEN`


---

## INVOLUTION_FIX_FIX

### Name of formal statement
INVOLUTION_FIX_FIX

### Type of the formal statement
theorem

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
For all functions `f` and `g`, and for all sets `s`, if `s` is finite, `f` is an involution on `s`, `g` is an involution on `s`, and there exists an `x` such that `x` is in `s` and `f x = x`, then there exists an `x` such that `x` is in `s` and `g x = x`.

### Informal sketch
The proof proceeds by:
- Assuming the hypotheses: `FINITE(s)`, `involution f s`, `involution g s`, and `?!x. x IN s /\ (f x = x)`.  The goal is to prove `?x. x IN s /\ (g x = x)`.
- Applying the theorem `INVOLUTION_ODD`, instantiating it with `f` and `s`, and then using `MATCH_MP_TAC` to apply the result to the assumption `involution f s` to deduce that if `s` is finite and `f` is an involution on `s`, then `s` has odd cardinality: `#s MOD 2 = 1`.
- Rewriting using the assumptions.
- Applying the theorem `INVOLUTION_FIX_ODD`, instantiating it with `g` and `s`, and then using `MATCH_MP_TAC` to apply the result to the assumption `involution g s` to deduce that if `s` is finite with odd cardinality and `g` is an involution on `s`, then there exists an `x` in `s` such that `g x = x`.
- Rewriting using the assumptions.

### Mathematical insight
The theorem `INVOLUTION_FIX_FIX` states that if a finite set admits two involutions, and one of them has a fixed point, then the other one must also have a fixed point. The proof relies on the fact that an involution on a finite set has a fixed point if and only if the cardinality of the set is odd.

### Dependencies
- `FINITE`
- `involution`
- `IN`
- `INVOLUTION_ODD`
- `INVOLUTION_FIX_ODD`


---

## zset

### Name of formal statement
zset

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let zset = new_definition
  `zset(a) = {(x,y,z) | x EXP 2 + 4 * y * z = a}`;;
```
### Informal statement
The set `zset(a)` is defined to be the set of all triples `(x, y, z)` such that `x` squared plus `4` times `y` times `z` equals `a`.

### Informal sketch
The item `zset` is defined as a set. The definition uses set comprehension to build a set that contains all triples of natural numbers `(x,y,z)` satisfying the equation `x^2 + 4 * y * z = a`, for a given natural number `a`.

### Mathematical insight
This definition introduces a set that is central to Zagier's one-sentence proof. This set is used to count the number of solutions to a specific Diophantine equation. Understanding the properties of this set, especially its cardinality, is key to the proof.

### Dependencies
None


---

## zag

### Name of formal statement
- zag

### Type of the formal statement
- new_definition

### Formal Content
- The full HOL Light statement will be inserted here **after generation**.
```ocaml
let zag = new_definition
  `zag(x,y,z) =
        if x + z < y then (x + 2 * z,z,y - (x + z))
        else if x < 2 * y then (2 * y - x, y, (x + z) - y)
        else (x - 2 * y,(x + z) - y, y)`;;
```
### Informal statement
- Define a function `zag` that takes three arguments, `x`, `y`, and `z`, and returns a triple.
- If `x + z < y`, then `zag(x, y, z) = (x + 2 * z, z, y - (x + z))`.
- Otherwise, if `x < 2 * y`, then `zag(x, y, z) = (2 * y - x, y, (x + z) - y)`.
- Otherwise, `zag(x, y, z) = (x - 2 * y, (x + z) - y, y)`.

### Informal sketch
- The definition of `zag(x, y, z)` is given by a conditional expression.
- The first condition checks if `x + z < y`. If true, a specific triple is returned.
- If the first condition is false, the second condition checks if `x < 2 * y`. If true, another specific triple is returned.
- If both conditions are false, a third specific triple is returned.

### Mathematical insight
- The purpose of `zag` appears to be to conditionally transform a triple of values based on arithmetic comparisons. Without further context, the exact mathematical significance isn't clear; this might be a step in a larger algorithm or construction. Its importance lies in its precise definition which makes its behavior unambiguous.

### Dependencies
None

### Porting notes (optional)
- Pay attention to the order of the conditional checks, as the definition relies on it. Different proof assistants may handle conditional definitions in slightly different ways, potentially affecting the proof obligations during verification. Be sure to preserve the correct precedence.


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
The function `tag` which takes a triple `(x,y,z)` of natural numbers as input, returns the triple `(x,z,y)` where the second and third components of the input triple are swapped.

### Informal sketch
- The definition introduces a function `tag` that performs a specific permutation on the components of an ordered triple of natural numbers.
- It directly specifies the transformation: `tag (x, y, z) = (x, z, y)`.
- This does not require a proof, as it is a direct definition.

### Mathematical insight
The `tag` function is a simple but useful operation for manipulating triples. It effectively swaps the second and third elements, which can be useful in various contexts where the order of these elements needs to be changed. This definition provides a named function for this specific permutation.

### Dependencies
None

### Porting notes (optional)
This definition is straightforward to port to other proof assistants. Most systems will have a way to define functions that operate on tuples or product types. The key is to ensure that the tuple indexing or pattern matching is correctly translated. No special automation should be needed.


---

## ZAG_INVOLUTION_GENERAL

### Name of formal statement
ZAG_INVOLUTION_GENERAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZAG_INVOLUTION_GENERAL = prove
 (`0 < x /\ 0 < y /\ 0 < z ==> (zag(zag(x,y,z)) = (x,y,z))`,
  REWRITE_TAC[zag] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[zag] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```

### Informal statement
If `x`, `y`, and `z` are all strictly greater than 0, then `zag(zag(x, y, z))` is equal to `(x, y, z)`.

### Informal sketch
The proof proceeds by:
- Rewriting with the definition of `zag`.
- Applying case splits based on the conditional definitions within `zag`. These case splits concern the ordering of x, y, and z. The cases are handled one by one via automated rewriting using assumptions from the context.
- Rewriting again with the definition of `zag`.
- Applying case splits similarly to before, and rewriting to handle the subgoals.
- Rewriting using the definition of `PAIR_EQ`.
- Discharging assumptions from the assumption list as needed, via conjunction.
- Finally, completing the proof using `ARITH_TAC`.

### Mathematical insight
The theorem states that the `zag` function is an involution when applied to triples of positive numbers. In other words, applying the `zag` function twice returns the original triple. This property is important because it shows that `zag` defines a kind of symmetry or reflection in the positive octant.

### Dependencies
- Definitions: `zag`, `PAIR_EQ`
- Theorems: `CONJ`
- Tactics: `REWRITE_TAC`, `COND_CASES_TAC`, `ASM_REWRITE_TAC`, `MP_TAC`, `end_itlist`, `POP_ASSUM_LIST`, `ARITH_TAC`

### Porting notes (optional)
The main challenge is likely to be the automated case-splitting and rewriting, which depends on HOL Light's `ASM_REWRITE_TAC` with arithmetic reasoning via `ARITH_TAC`. Other provers might require more manual case splitting or a more tailored approach to arithmetic simplification.


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
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;
```

### Informal statement
For any predicate `P` and any `a`, `b`, and `c`, the triple `(a,b,c)` is an element of the set of triples `(x,y,z)` such that `P x y z` holds if and only if `P a b c` holds.

### Informal sketch
The proof proceeds as follows:

- The goal is `(a,b,c) IN {(x,y,z) | P x y z} <=> P a b c`.
- First, rewrite using `IN_ELIM_THM` to eliminate the set membership, which involves reducing `IN` to an equality condition using `==`.
- Then, rewrite using `PAIR_EQ` which relates equality of n-tuples to equality of their components. Specifically, `PAIR_EQ` is used to decompose the triple comparison occurring within the 'IN' set membership.
- Finally, use `MESON_TAC[]` to complete the proof automatically, using propositional reasoning to conclude the equivalence.

### Mathematical insight
This theorem expresses a fundamental property of set membership for triples defined by a predicate `P`. It formalizes the intuitive notion that a triple belongs to a set defined by a predicate if and only if the predicate holds true when applied to the components of the triple.

### Dependencies
- `IN_ELIM_THM`
- `PAIR_EQ`


---

## PRIME_SQUARE

### Name of formal statement
PRIME_SQUARE

### Type of the formal statement
theorem

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
  ASM_SIMP_TAC[EQ_MULT_LCANCEL]);;
```
### Informal statement
For all natural numbers n, it is not the case that `n * n` is a prime number.

### Informal sketch
The proof proceeds by contradiction, assuming that there exists some `n` such that `prime(n * n)`.

- First, we consider the case where `n = 0`. In this case, `n * n = 0`, and `prime(0)` is false, resolving the contradiction.
  - The relevant theorems used are `PRIME_0` which states that 0 is not prime and `MULT_CLAUSES` which defines multiplication.
- Next, the goal is rewritten using the definition of `prime`; `NOT_FORALL_THM` is used to negate the universal quantifier in the definition of prime, and `DE_MORGAN_THM` is applied.
- Then, we consider the case where `n = 1`. In this case, `n * n = 1`, and `prime(1)` is false using arithmetic simplification.
- If `n` is not equal to 0 or 1, then it is split into two subgoals. The second subgoal assumes `prime (n * n)`
  - We show that there exists a number that divides `n * n`. `n` clearly divides `n*n`, so choose `n` as the witness.
  - The rewriting step uses `DIVIDES_LMUL` (which states that if d divides m, then d divides m*n) and `DIVIDES_REFL` (which states that n divides n).
  - We then rewrite `n` as `n * 1` using arithmetic rewriting and then use `EQ_MULT_LCANCEL` to simplify the divisibility condition.

### Mathematical insight
This theorem states that the square of any natural number is never a prime number. The proof relies on the fact that a prime number must be greater than 1 and only divisible by 1 and itself. If `n` is 0 or 1, then `n*n` is not prime; otherwise `n*n` is divisible by `n`, so it is not prime because it has a divisor other than 1 and itself.

### Dependencies
- `PRIME_0`
- `MULT_CLAUSES`
- `prime`
- `NOT_FORALL_THM`
- `DE_MORGAN_THM`
- `ARITH`
- `DIVIDES_LMUL`
- `DIVIDES_REFL`
- `ARITH_RULE`
- `EQ_MULT_LCANCEL`


---

## PRIME_4X

### Name of formal statement
PRIME_4X

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_4X = prove
 (`!n. ~prime(4 * n)`,
  GEN_TAC THEN REWRITE_TAC[prime; NOT_FORALL_THM; DE_MORGAN_THM] THEN
  DISJ2_TAC THEN EXISTS_TAC `2` THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 * 2`)) THEN
  ASM_SIMP_TAC[GSYM MULT_ASSOC; DIVIDES_RMUL; DIVIDES_REFL; ARITH_EQ] THEN
  ASM_CASES_TAC `n = 0` THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, it is not the case that `4 * n` is prime.

### Informal sketch

*   The proof starts by negating the goal, which introduces the assumption that there exists a natural number `n` such that `4 * n` is prime.

*   We instantiate this with `2` to obtain `prime(4 * 2)`, which simplifies to `prime(8)`.

*   We use the definition of `prime` to obtain `!d. divides d 8 ==> d = 1 \/ d = 8`.

*   The proof proceeds by cases with `n = 0`.
    *   If `n = 0`, then `4 * n = 0`.
    *   Then `~ prime(0)` by `ARITH_TAC`.

*   The proof proceeds assuming `n <> 0`, and uses automatic arithmetic reasoning (`ARITH_TAC`) to derive a contradiction.

### Mathematical insight

The theorem states that no multiple of 4 is prime. This is because any number of the form `4 * n`, where `n` is a natural number, is divisible by 2 (unless `n=0`), and therefore not prime (except when equal to 2, but here, `4*n=2` implies `n=1/2` which is not a natural number, or when equal to 1, namely `4*n = 1` implies `n = 1/4` which is not a natural number. `4*0 = 0` is not prime).

### Dependencies

*   Definitions: `prime`
*   Theorems: `NOT_FORALL_THM`, `DE_MORGAN_THM`, `MULT_ASSOC`, `DIVIDES_RMUL`, `DIVIDES_REFL`, `ARITH_EQ`


---

## PRIME_XYZ_NONZERO

### Name of formal statement
PRIME_XYZ_NONZERO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_XYZ_NONZERO = prove
 (`prime(x EXP 2 + 4 * y * z) ==> 0 < x /\ 0 < y /\ 0 < z`,
  CONV_TAC CONTRAPOS_CONV THEN
  REWRITE_TAC[DE_MORGAN_THM; ARITH_RULE `~(0 < x) = (x = 0)`] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES; PRIME_SQUARE; PRIME_4X]);;
```
### Informal statement
For all natural numbers $x$, $y$, and $z$, if $x^2 + 4yz$ is prime, then $x > 0$ and $y > 0$ and $z > 0$.

### Informal sketch
The proof proceeds by contradiction.
- The contrapositive of the statement is taken. That is, it is shown that if not ($x > 0$ and $y > 0$ and $z > 0$), then not ($x^2 + 4yz$ is prime).
- The negation `~(0 < x /\ 0 < y /\ 0 < z)` is rewritten to `(x = 0) \/ (y = 0) \/ (z = 0)`.
- The proof then splits into three cases based on whether $x = 0$, $y = 0$, or $z = 0$.
  - If $x = 0$, then $x^2 + 4yz = 4yz$. Then `PRIME_4X` is used to show that $4yz$ is not prime.
  - If $y = 0$, then $x^2 + 4yz = x^2$. Then `PRIME_SQUARE` is used to show that $x^2$ is not prime.
  - If $z = 0$, then $x^2 + 4yz = x^2$. Then `PRIME_SQUARE` is used to show that $x^2$ is not prime.
- In each case, it is shown that $x^2 + 4yz$ is not prime, completing the proof by contradiction.

### Mathematical insight
The theorem establishes a necessary condition for $x^2 + 4yz$ to be prime. It states that if $x^2 + 4yz$ is prime, then $x$, $y$, and $z$ must all be greater than zero. This is a simple but useful condition.

### Dependencies
- `DE_MORGAN_THM`
- `PRIME_SQUARE`
- `PRIME_4X`
- `EXP_2`
- `MULT_CLAUSES`
- `ADD_CLAUSES`


---

## ZAG_INVOLUTION

### Name of formal statement
ZAG_INVOLUTION

### Type of the formal statement
theorem

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
    ASM_MESON_TAC[PRIME_XYZ_NONZERO]]);;
```
### Informal statement
For all prime numbers `p`, `zag` is an involution on the `zset` of `p`.

### Informal sketch
The proof proceeds as follows:
- The goal is to prove that for any prime number `p`, the function `zag` applied twice to any element in `zset(p)` returns the original element. This is the definition of an involution.
- Start by stripping the quantifier and rewriting using the definition of `involution` and `FORALL_PAIR_THM`.
- Introduce variables `x`, `y`, and `z` for the triple.
- Rewrite with the definition of `zset` and `IN_TRIPLE`.
- Discharge and substitute using the symmetry.
- Split the goal into two subgoals by performing a conjunction.
- Rewrite the first subgoal using the definition of `zag`. Perform conditional cases on the conditions within `zag`. Use assumptions and rewrite with `IN_TRIPLE`. Rule out the `<` case using `NOT_LT`. Use arithmetic simplification.
- For the second subgoal, use `ZAG_INVOLUTION_GENERAL` along with `PRIME_XYZ_NONZERO` to solve the goal.
- Arithmetic simplification is applied to complete certain subgoals.

### Mathematical insight
The theorem states that the `zag` function, when applied twice to an element within a `zset` of a prime `p`, returns the original element. This signifies that `zag` acts as an involution within the constraints of `zset(p)`. The involution property is important in various mathematical contexts, particularly in group theory and cryptography.

### Dependencies
- Definitions: `involution`, `zag`, `zset`, `IN_TRIPLE`
- Theorems: `FORALL_PAIR_THM`, `ZAG_INVOLUTION_GENERAL`, `PRIME_XYZ_NONZERO`, `NOT_LT`, `GSYM INT_OF_NUM_EQ`, `GSYM INT_OF_NUM_ADD`, `EXP_2`, `GSYM INT_OF_NUM_MUL`, `GSYM INT_OF_NUM_SUB`, `LT_IMP_LE`

### Porting notes (optional)
When porting this theorem to other proof assistants, special attention should be paid to the handling of arithmetic simplification (using `INT_ARITH_TAC`) and automation (`ASM_MESON_TAC`). Different proof assistants may require different techniques to achieve similar levels of automation in arithmetic reasoning. The definitions of `zag`, `zset`, and `IN_TRIPLE` should be carefully translated, ensuring that the constraints and conditions are correctly represented. `ZAG_INVOLUTION_GENERAL` and `PRIME_XYZ_NONZERO` are lemmas; ensure precise translation, as they are essential in the proof.


---

## TAG_INVOLUTION

### Name of formal statement
TAG_INVOLUTION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAG_INVOLUTION = prove
 (`!a. involution tag (zset a)`,
  REWRITE_TAC[involution; tag; zset; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_TRIPLE] THEN REWRITE_TAC[MULT_AC]);;
```

### Informal statement
For all `a`, the function `tag` is an involution on the set `zset a`.

### Informal sketch
The proof demonstrates that tagging an element of the set `zset a` and then tagging it again results in the original element.
- The proof starts by rewriting the definition of `involution`, `tag`, and `zset` along with `FORALL_PAIR_THM` to expand the definitions.
- Then the theorem `IN_TRIPLE` is applied to simplify the resulting expression, which involves membership in the `zset`.
- Finally, the tactic `MULT_AC` is used to apply associativity and commutativity of multiplication to complete the proof.

### Mathematical insight
This theorem establishes that the `tag` function, when applied twice to an element within the `zset a`, returns the original element. This property is fundamental for the involutive nature of `tag` within this specific set. The `zset` likely constraints its element to have a particular form enabling the `tag` function to exhibit this involutivity.

### Dependencies

Definitions:
- `involution`
- `tag`
- `zset`

Theorems:
- `FORALL_PAIR_THM`
- `IN_TRIPLE`

Tactics:
- `MULT_AC`


---

## ZAG_LEMMA

### Name of formal statement
ZAG_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ZAG_LEMMA = prove
 (`(zag(x,y,z) = (x,y,z)) ==> (y = x)`,
  REWRITE_TAC[zag; INT_POW_2] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[PAIR_EQ]) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;
```
### Informal statement
If `zag(x, y, z) = (x, y, z)`, then `y = x`.

### Informal sketch
The proof proceeds as follows:
-  Start by rewriting using the definition of `zag` and `INT_POW_2`.
-  Then perform case splits using the conditional cases tactic, followed by simplification using the assumption that pairs are equal if and only if their components are equal (`PAIR_EQ`).
-  Finally, eliminate assumptions using `MP_TAC` and `end_itlist CONJ`, followed by application of `ARITH_TAC`.

### Mathematical insight
This lemma states that if the function `zag` which swaps `x` and `y` in a triple `(x, y, z)` results in the same triple, then `x` and `y` must be equal.

### Dependencies
- Definitions: `zag`
- Theorems: `INT_POW_2`, `PAIR_EQ`


---

## ZSET_BOUND

### Name of formal statement
ZSET_BOUND

### Type of the formal statement
theorem

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
    ASM_SIMP_TAC[ARITH_RULE `0 < a ==> 1 <= 4 * a`]]);;
```

### Informal statement
Given that `0 < y` and `0 < z` and `x^2 + 4 * y * z = p`, then `x <= p` and `y <= p` and `z <= p`.

### Informal sketch
The proof proceeds as follows:
- Assume `0 < y`, `0 < z`, and `x^2 + 4 * y * z = p`.
- Prove `x <= p`: Use the assumption `x^2 + 4 * y * z = p`.  Since `x^2 >= 0` and `4 * y * z > 0`, it follows that `x^2 <= p`. Apply `LE_SQUARE_REFL` and the arithmetic fact that `a <= b ==> a <= b + c`.
- Prove `y <= p` and `z <= p`. First, derive `y <= z`. Then, derive `y <= x + z` using the arithmetic fact that `y <= z ==> y <= x + z`. Transform the equation `x^2 + 4 * y * z = p` into `4 * y * z = p - x^2` by rewriting using the symmetry of multiplication. Then, show `y <= 4 * y * z` which is equivalent to `1 * y <= (4 * z) * y`. Apply the assumption `0 < z` to prove that `1 <= (4 * z)`. Then use the tactic `LE_MULT_RCANCEL` from the assumption to derive that `y <= p`. Finally, derive `z <= p` using the same process.

### Mathematical insight
This theorem establishes bounds on the variables `x`, `y`, and `z` given a specific equation involving them. It's a result useful for bounding solutions to Diophantine equations or for estimation in number-theoretic arguments. Establishing bounds is a very common strategy in number theory.

### Dependencies
**Theorems/Definitions:**
- `EXP_2`
- `LE_SQUARE_REFL`

**Rules:**
- `ARITH_RULE \`(a <= b ==> a <= b + c)\``
- `ARITH_RULE \`y <= z ==> y <= x + z\``
- `ARITH_RULE \`y <= 4 * a * y <=> 1 * y <= (4 * a) * y\` `
- `ARITH_RULE \`0 < a ==> 1 <= 4 * a\` `

**Tactics (These are less critical but can help understand the intent of the proof):**
- `LE_MULT_RCANCEL`
- `MULT_SYM` (Symmetry of multiplication: a * b = b * a)

### Porting notes (optional)
- Depends on the availability of similar arithmetic tactics as found in HOL Light.
- Pay attention to differences in the available arithmetic simplification rules. Ensure the required arithmetic facts are available or can be easily proven.
- The `MESON_TAC` usage suggests a first-order logic automated reasoning step, which may need to be replicated with a different automated tactic depending on the target proof assistant.


---

## ZSET_FINITE

### Name of formal statement
ZSET_FINITE

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[ZSET_BOUND; PRIME_XYZ_NONZERO]);;
```

### Informal statement
For all `p`, if `p` is prime, then the set of triples `(x, y, z)` such that `x * x + y * y = (p + 1) * z * z` is finite.

### Informal sketch
The proof proceeds as follows:
- Assume that a prime number `p` is given.
- Apply `FINITE_NUMSEG_LT` which states that `FINITE(numseg (p + 1))`, which means the set `{0, 1, ..., p}` is finite.
- Instantiate `FINITE_PRODUCT` twice to prove that the set of pairs `(x,y)` with `x < p+1` and `y < p+1` is finite, and further `FINITE((0.. < p + 1) CROSS (0.. < p + 1) CROSS (0.. < p + 1))`, i.e. the set of triples `(x, y, z)` where `x < p + 1`, `y < p + 1`, and `z < p + 1` is finite.
- Use `FINITE_SUBSET` to show the set `zset p` is a subset of triples less than `p + 1`.
- Expand definitions of `zset`, `SUBSET` using `FORALL_PAIR_THM` and `IN_TRIPLE`.
- Introduce three assumptions `x:num`, `y:num`, and `z:num`.
- Rewrite using `IN_ELIM_THM`, `EXISTS_PAIR_THM`, and `PAIR_EQ`.
- After rewriting with `ARITH_RULE x < p + 1 <=> x <= p` and `PAIR_EQ`, discharge the assumption.
- Introduce existential variables `x`, `y`, and `z`.
- Apply assumption rewriting.
- Rewrite using `RIGHT_AND_EXISTS_THM`.
- Introduce existential variables `y` and `z`.
- Rewrite and use `ASM_MESON_TAC`, employing the lemmas `ZSET_BOUND` and `PRIME_XYZ_NONZERO` to complete the proof.

### Mathematical insight
This theorem states that for any prime number `p`, the set of solutions to the equation `x^2 + y^2 = (p + 1) * z^2` forms a finite set. The proof strategy involves establishing a bound on the components of the triples and demonstrating that the solution set is a subset of a finite set.

### Dependencies
- `FINITE_NUMSEG_LT`
- `FINITE_PRODUCT`
- `FINITE_SUBSET`
- `zset`
- `SUBSET`
- `FORALL_PAIR_THM`
- `IN_TRIPLE`
- `IN_ELIM_THM`
- `EXISTS_PAIR_THM`
- `PAIR_EQ`
- `ZSET_BOUND`
- `PRIME_XYZ_NONZERO`

### Porting notes (optional)
- The proof relies heavily on the tactic `ASM_MESON_TAC`, which automatically uses a set of assumptions to prove the goal. When porting to other proof assistants, it might be necessary to manually supply the assumptions or use a similar automated reasoning tactic.
- The definition of `zset` and lemmas `ZSET_BOUND`, `PRIME_XYZ_NONZERO` are important. Ensure that these have been defined and proved appropriately in your target proof assistant.


---

## SUM_OF_TWO_SQUARES

### Name of formal statement
SUM_OF_TWO_SQUARES

### Type of the formal statement
theorem

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
      REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC]]);;
```

### Informal statement
For all prime numbers `p` and natural numbers `k`, if `p` is prime and `p` is equal to `4 * k + 1`, then there exist natural numbers `x` and `y` such that `p` is equal to `x^2 + y^2`.

### Informal sketch
The proof demonstrates that any prime number `p` of the form `4k + 1` can be expressed as the sum of two squares. The proof proceeds as follows:
- Define a set `zset(p)` containing triples `(x, y, z)` where `x * x + y * y + p * z = p`.
- Show that this set includes an involution `zag` (a function such that `zag(zag(t)) = t`) where the tag of t `tag(t)` is equal to t. Show that there is a triple `t` in `zset(p)` such that `tag(t) = t`.
- Find the involution `zag` on `zset(p)` defined by `zag (x,y,z) = (x,4 * z + x,y - x - 4 * z)`.
- Show that `zag` preserves `zset(p)` and is an involution.
- Show that `(1, 1, k)` is a fixed point of `zag` if `x EXP 2 + y EXP 2 + p * z = p`.
- Deduce from examining the definition of `zag` that there is a case where `x=y` so `x^2 + 4xz = 4k+1`.
- Apply `prime p` which expands into `!n. n divides p ==> n = 1 \/ n = p`.
- By assumption, and rewriting with the primality assumption, we know that either `x = 1` or `4*z + x = 1`; examine these two cases.

### Mathematical insight
This theorem is a classical result in number theory. It demonstrates a fundamental property of prime numbers of the form `4k + 1`. The proof employs a clever involution argument on triples of integers, ultimately leading to the desired representation of `p` as a sum of two squares.

### Dependencies
- Definitions: `prime`, `zset`, `tag`, `zag`
- Theorems: `LEFT_IMP_EXISTS_THM`, `FORALL_PAIR_THM`, `PAIR_EQ`, `ZAG_INVOLUTION`, `TAG_INVOLUTION`, `ZSET_FINITE`, `EXISTS_UNIQUE_ALT`, `MULT_CLAUSES`, `ARITH_RULE`, `ADD_EQ_0`, `ARITH_EQ`, `zag`, `IN_TRIPLE`, `MULT_CLAUSES`, `ZAG_LEMMA`, `prime`, `DIVIDES_RMUL`, `DIVIDES_REFL`

### Porting notes (optional)
- The involution argument may need to be constructed explicitly in systems without built-in support for such reasoning.
- The interplay between arithmetic simplification and logical deduction is crucial; ensure the target system can handle such interactions effectively.
- The use of `ASM_MESON_TAC` indicates reliance on a decision procedure for arithmetic and equality; ensure the target system can prove equality of pairs and arithmetic statements (often this is built in)


---

## PIGEONHOLE_LEMMA

### Name of formal statement
PIGEONHOLE_LEMMA

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[]);;
```

### Informal statement
For all functions `f` and `g` from a type `A` to a type `B`, and for all sets `s` and `t`, if `s` and `t` are finite, and the image of `s` under `f` is contained in `t`, and `f` is injective on `s`, and the image of `s` under `g` is contained in `t`, and `g` is injective on `s`, and the cardinality of `t` is less than twice the cardinality of `s`, then there exist `x` and `y` in `s` such that `f(x)` equals `g(y)`.

### Informal sketch
The proof proceeds as follows:

- The goal is to show the existence of `x` and `y` in `s` such that `f x = g y` under the assumption that `CARD t < 2 * CARD s`, `f` and `g` are injective from `s` to `t`, and `s` and `t` are finite.
- Apply the theorem that the cardinality of a union is the sum of the cardinalities minus the cardinality of the intersection to `IMAGE f s` and `IMAGE g s`. `MP_TAC(ISPECL [`IMAGE (f:A->B) s`; `IMAGE (g:A->B) s`] CARD_UNION)`
- Show that `CARD (IMAGE f s) = CARD s` and `CARD (IMAGE g s) = CARD s` since `f` and `g` are injective on `s`, using `CARD_IMAGE_INJ` and `FINITE_IMAGE`.
- Rewrite the goal using these equalities.
- Deduce that since `CARD t < 2 * CARD s = CARD (IMAGE f s) + CARD (IMAGE g s)`, the images of `f` and `g` must intersect in `t`. This is established using arithmetic reasoning `ARITH_RULE` and `CARD_SUBSET`.
- Instantiate the existential quantifier with `CARD t`.
- Show that if the images intersect, we can find the desired `x` and `y`.

### Mathematical insight
This theorem represents a generalized pigeonhole principle. If we have two injective functions `f` and `g` from a set `s` into a set `t`, and `t` is smaller than twice the size of `s`, the images of `f` and `g` must overlap. This overlaps is what is meant by the pigeons (domain of `f` and `g`) sharing holes (range of `f` and `g`).

### Dependencies
- `CARD_UNION` : cardinality of a union of two sets.
- `CARD_IMAGE_INJ` : cardinality of the image of a set under an injection.
- `FINITE_IMAGE` : finiteness of the image of a finite set.
- `EXTENSION`, `IN_INSERT`, `IN_INTER`, `IN_IMAGE`, `NOT_IN_EMPTY` : set theory lemmas.
- `CARD_SUBSET` : cardinality of a subset.
- `SUBSET` : subset definition.
- `IN_UNION`: membership in a union


---

## PIGEONHOLE_LEMMA_P12

### Name of formal statement
PIGEONHOLE_LEMMA_P12

### Type of the formal statement
theorem

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
  REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `2 * k + 1 < 2 * (k + 1)`]);;
```

### Informal statement
For all functions `f` and `g` and number `p`, if `p` is odd, and for all `x`, if `2 * x < p` then `f(x) < p`, and for all `x` and `y`, if `2 * x < p` and `2 * y < p` and `f(x) = f(y)`, then `x = y`, and for all `x`, if `2 * x < p` then `g(x) < p`, and for all `x` and `y`, if `2 * x < p` and `2 * y < p` and `g(x) = g(y)` then `x = y`, then there exist `x` and `y` such that `2 * x < p` and `2 * y < p` and `f(x) = g(y)`.

### Informal sketch
The proof proceeds as follows:
- First, the existence component of the `ODD(p)` assumption (which is equivalent to `?k. p = 2 * k + 1`) is separated out and instantiated, resulting in a new constant `k:num` such that `p = 2 * k + 1`.
- Next, the general pigeonhole principle `PIGEONHOLE_LEMMA` is instantiated with functions `f` and `g`, and with sets `{x:num | 2 * x < 2 * k + 1}` and `{x:num | x < k + 1}`.
- Simplify arithmetical expressions like `2 * x < 2 * k + 1 <=> x < k + 1`.
- Simplify by rewriting with `FINITE_NUMSEG_LT` and `CARD_NUMSEG_LT` to calculate the cardinality of the sets used.
- Rewriting using `IN_ELIM_THM` eliminates set membership.
- Finish using `ARITH_RULE` applied to `2 * k + 1 < 2 * (k + 1)`.

### Mathematical insight
The theorem is a specific instance of the pigeonhole principle. Given an odd number `p = 2k + 1`, and two functions `f` and `g` that map numbers `x` satisfying `2x < p` to numbers less than `p`. If both `f` and `g` are injective when restricted to inputs `x` such that `2x < p`, then there must exist `x` and `y` such that `f(x) = g(y)`. This is because the domain `{ x | 2x < p }` has cardinality `k+1`, and a strict injection into `p = 2k + 1` elements will force a collision.

### Dependencies
- `ODD_EXISTS`
- `PIGEONHOLE_LEMMA`
- `ADD1`
- `FINITE_NUMSEG_LT`
- `CARD_NUMSEG_LT`
- `IN_ELIM_THM`


---

## SQUAREMOD_INJ_LEMMA

### Name of formal statement
SQUAREMOD_INJ_LEMMA

### Type of the formal statement
theorem

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
    SIMP_TAC[ADD_EQ_0] THEN UNDISCH_TAC `2 * (x + d) < p` THEN ARITH_TAC]);;
```

### Informal statement
For all primes `p`, all natural numbers `x` and `d`, if `2 * (x + d)` is less than `p` and `(x + d) * (x + d) + m * p` equals `x * x + n * p`, then `d` must be `0`.

### Informal sketch
The proof demonstrates that under the given conditions, the value of `d` must be zero.

- Assumes `p` is prime, `2 * (x + d) < p`, and `(x + d) * (x + d) + m * p = x * x + n * p`.
- Reduce the assumption `(x + d) * (x + d) + m * p = x * x + n * p` to `p divides d or p divides (2 * x + d)`. The HOL Light tactic `SUBGOAL_THEN` introduces this as a subgoal.
- The first branch proves that `p` divides `d`. This involves simplifying the original assumption using arithmetic and rewriting, and showing that `d * (2 * x + d)` is a multiple of `p`.  Since `p` is prime, either `p` divides `d` or `p` divides `2 * x + d`.
- The second branch considers the case where `p` divides `2 * x + d`. Using the additional condition `2 * (x + d) < p`, it is shown that if `p` divides `2 * x + d`, then `d = 0`. This is proved by cases and simplification using `ADD_EQ_0`.

### Mathematical insight
This lemma establishes an injectivity condition related to the function `x^2 mod p`. Specifically, under the condition `2 * (x + d) < p`, if `(x + d)^2` and `x^2` are congruent modulo `p`, then `x + d` must be equal to `x`, i.e., `d = 0`. This captures a uniqueness property crucial for further modular arithmetic reasoning on quadratic residues.

### Dependencies
- `prime`
- `divides`
- `PRIME_DIVPROD`
- `DIVIDES_LE`
- `ADD_EQ_0`
- `LEFT_SUB_DISTRIB`

### Porting notes (optional)
- The proof relies heavily on arithmetic simplification (`ARITH_TAC`).
- The initial `SUBGOAL_THEN` tactic is essential, and might need to be emulated using appropriate goal manipulation primitives in other proof assistants. Specifically, the ability to add `p divides d \/ p divides (2 * x + d)` as an intermediate goal, then prove that this intermediate goal would complete the proof of the overall goal if it were true.


---

## SQUAREMOD_INJ

### Name of formal statement
SQUAREMOD_INJ

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[SQUAREMOD_INJ_LEMMA]);;
```

### Informal statement
For all primes `p`, if for all `x`, `2 * x < p` implies `(x EXP 2 + a) MOD p < p`, and for all `x` and `y`, if `2 * x < p` and `2 * y < p` and `(x EXP 2 + a) MOD p = (y EXP 2 + a) MOD p`, then `x = y`.

### Informal sketch
The proof proceeds as follows:
- Assume `p` is prime.
- Assume `2 * x < p` implies `(x^2 + a) mod p < p`.
- Assume `2 * x < p` and `2 * y < p` and `(x^2 + a) mod p = (y^2 + a) mod p`.
- Show that `x = y`.
- Apply `ARITH_RULE` stating that `x < a` implies `~(a = 0)`.
- Simplify using `DIVISION`.
- Apply the subgoal tactic to introduce equations stating that `x EXP 2 + a = (x EXP 2 + a) DIV p * p + (x EXP 2 + a) MOD p` and `y EXP 2 + a = (y EXP 2 + a) DIV p * p + (y EXP 2 + a) MOD p`.
- Simplify using `DIVISION`.
- Rewrite with the assumption that `(x EXP 2 + a) MOD p = (y EXP 2 + a) MOD p`, which introduces `x^2 + yp = y^2 + xp`.
- Perform cases on the disjunction `x <= y \/ y < x`. Introduce a variable `d` such that `y = x + d`. Then, consider the two subcases `x <= y` and `y < x`.
- Rewrite using `EXP_2` and `ARITH_RULE` stating `(x + d = x) = (d = 0)`.
- Apply `ASM_MESON_TAC` along with `SQUAREMOD_INJ_LEMMA`.

### Mathematical insight
This theorem states the injectivity of the function `(x^2 + a) mod p` under certain conditions. The injectivity is guaranteed when `x` and `y` are both less than `p/2`. The result is useful in number theory and cryptography, where modular arithmetic is commonly used.

### Dependencies
- `prime`
- `DIVISION`
- `EXP_2`
- `LE_EXISTS`
- `LE_CASES`
- `SQUAREMOD_INJ_LEMMA`


---

## REFLECT_INJ

### Name of formal statement
REFLECT_INJ

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[]);;
```

### Informal statement
For all `p`, and for all `f`, if the following two conditions hold:

1.  For all `x`, if `2 * x < p`, then `f(x) < p`.
2.  For all `x` and `y`, if `2 * x < p` and `2 * y < p` and `f(x) = f(y)`, then `x = y`.

Then the following two conditions also hold:

1.  For all `x`, if `2 * x < p`, then `p - 1 - f(x) < p`.
2.  For all `x` and `y`, if `2 * x < p` and `2 * y < p` and `p - 1 - f(x) = p - 1 - f(y)`, then `x = y`.

### Informal sketch
The proof proceeds by assuming the hypothesis and then proving the conclusion.

-   The proof starts by stripping the top-level implication using `STRIP_TAC`.
-   The goal is unfolded using `REWRITE_TAC` and the arithmetic rule `2 * x < p ==> p - 1 - y < p`.
-   The conclusion is then stripped using `REPEAT STRIP_TAC`.
-   The assumptions are used to rewrite the goal, essentially proving that if `f` satisfies the given properties, so does its reflection `p - 1 - f`.
-   Finally, `p - 1 - f(x) = p - 1 - f(y)` is simplified to `f(x) = f(y)`.

### Mathematical insight
The theorem essentially states that if a function `f` maps elements `x` (where `2 * x < p`) to values less than `p` and is injective on these elements, then the reflection of `f` around `(p-1)/2`, defined as `p - 1 - f(x)`, also possesses these properties. This kind of reflection is relevant in number theory and modular arithmetic.

### Dependencies
* `ARITH_RULE`: Used to apply arithmetic reasoning, specifically `2 * x < p ==> p - 1 - y < p` and `x < p /\ y < p /\ (p - 1 - x = p - 1 - y) ==> (x = y)`.


---

## LAGRANGE_LEMMA_ODD

### Name of formal statement
LAGRANGE_LEMMA_ODD

### Type of the formal statement
theorem

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
 ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN MESON_TAC[]);;
```

### Informal statement
For all `a` and `p`, if `p` is prime and `p` is odd, then there exist natural numbers `n`, `x`, and `y` such that `2 * x < p`, `2 * y < p`, and `n * p = x^2 + y^2 + a + 1`.

### Informal sketch
The proof strategy involves the following key steps:
- Assume `p` is prime and odd.
- Establish that `p` is not zero to avoid division by zero issues.
- Apply the pigeonhole principle (`PIGEONHOLE_LEMMA_P12`) to the sets of residues `(x^2 + a) mod p` and `(p - 1 - (x^2) mod p)`.
- This yields `x` and `y` such that `(x^2 + a) mod p` is equal to `(p - 1 - y^2) mod p`.
- Use arithmetic reasoning to show that `x + y + 1 = p`.
- Use modular arithmetic to relate `(x^2 + a) mod p + (y^2 + 0) mod p + 1` to `(x^2 + y^2 + a + 1) mod p`.
- Deduce the existence of `n` such that `n * p = x^2 + y^2 + a + 1` with additional constraints `2 * x < p` and `2 * y < p`.

### Mathematical insight
This theorem is a lemma towards Lagrange's four-square theorem. It shows that for any odd prime `p` and any number `a`, one can always find `x`, `y` such that `x^2 + y^2 + a + 1` is a multiple of `p`, and `x` and `y` are bounded by `p/2`. This is crucial for showing Lagrange's four-square theorem, by reducing the problem to considering prime numbers.

### Dependencies
- `prime`
- `ODD`
- `PIGEONHOLE_LEMMA_P12`
- `DIVISION`
- `MOD_EQ`
- `MOD_UNIQ`
- Arithmetic rules (e.g., relating division and remainders)
- Tautologies and basic logical rules

### Porting notes (optional)
- The pigeonhole principle (`PIGEONHOLE_LEMMA_P12`) needs to be available or proven in the target system.
- The modular arithmetic and division lemmas (e.g. `MOD_EQ`, `MOD_UNIQ`, `DIVISION`) must also be available, or, if these functionalities are directly provided by target proof assistant, the tactic scripts must be adapted accordingly.
- The proof relies on rewriting and equational reasoning in modular arithmetic, so ensure these are well-supported.
- The use of `MESON_TAC` suggests a need for a strong first-order logic automated prover.


---

## LAGRANGE_LEMMA

### Name of formal statement
LAGRANGE_LEMMA

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN MESON_TAC[LT_IMP_LE]]);;
```

### Informal statement
For any natural number `a` and prime number `p`, there exist natural numbers `n`, `x`, and `y` such that `2 * x` is less than or equal to `p`, `2 * y` is less than or equal to `p`, and `n * p` equals `x` squared plus `y` squared plus `a`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and implication.
- Considering the case where `p` is even.
- Using the fact that the only even prime is 2.
- Using the axiom of existence of even numbers `EVEN_EXISTS` and `divides` to prove existence of `n`, `x`, `y`.
- Simplify using arithmetic.
- Now `p` is odd. Then consider cases where `a` is even and odd.
    - If `a` is even, instantiate existentials `n`, `x`, and `y` with `k`, `0`, and `0` based on the `EVEN_EXISTS`, where `a = 2 * k`.
    - If `a` is odd, instantiate existentials `n`, `x`, and `y` with `k + 1`, `1`, and `0` based on the axiom `ODD_EXISTS`, where `a = 2 * k + 1`.
- Simplify using arithmetic.
- Now consider cases where `a = 0`. Then instantiate existentials `n`, `x`, and `y` with `0`, `0`, and `0`.
- Finally, in the general case where `a != 0`, rewrite `a` to `(a - 1) + 1`, use the instance `LAGRANGE_LEMMA_ODD` to reduce `a - 1`. Rewrite using `NOT_EVEN` and use `MESON` with the theorem `LT_IMP_LE`.

### Mathematical insight
This lemma is a step toward proving Lagrange's four-square theorem. It states that for any prime `p` and number `a`, one can find `x`, `y`, and `n` such that `n*p = x^2 + y^2 + a`, with the constraints that `x` and `y` are small relative to `p`. This lemma sets the stage for further reasoning about sums of squares modulo a prime.

### Dependencies
- Definitions:
  - `prime`

- Theorems/Axioms:
  - `EVEN_EXISTS`
  - `divides`
  - `NOT_EVEN`
  - `ODD_EXISTS`
  - `LAGRANGE_LEMMA_ODD`
   - `LT_IMP_LE`
  - `LE_0`

- Rules:
  - `ARITH_RULE`

### Porting notes
The proof relies heavily on arithmetic simplification tactics (`ARITH_TAC`). Ensure the target proof assistant has comparable capabilities or be prepared to provide more explicit rewriting steps. Cases where HOL Light uses MESON require the most attention when porting. MESON attempts to automatically resolve a proof using specified assumptions, so equivalent functionality or specific lemmas must be available in the target environment. The tactic ASM_CASES_TAC involves case-splitting based on assumptions in the assumption list. If porting to a system where term structure influences case-splitting, be mindful that `EVEN(p)` expands to `?k. p = k + k`.


---

## AUBREY_THM_4

### Name of formal statement
AUBREY_THM_4

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
```

### Informal statement
If for some `q` not equal to 0, there exist `a`, `b`, `c`, and `d` such that `(a / q)^2 + (b / q)^2 + (c / q)^2 + (d / q)^2 = N`, then there exist `a`, `b`, `c`, and `d` such that `a^2 + b^2 + c^2 + d^2 = N`.

### Informal sketch
The proof proceeds by contradiction and induction, leveraging the well-ordering principle on natural numbers (`num_WOP`). It aims to show that if a number `N` can be expressed as the sum of four squares of rational numbers, then it can also be expressed as the sum of four integer squares.
- Initially, the assumption is discharged.
- The proof proceeds by cases based on whether the number `m` (from `AUBREY_LEMMA_4`) is equal to 1.
- If `m = 1`, the result is obtained trivially using rewriting with `REAL_DIV_1` and arithmetic equalities.
- If `m` is not equal to 1 (and not equal to 0 since it must be non-zero), `AUBREY_LEMMA_4` is used with specialization to `m`.

### Mathematical insight
This theorem demonstrates a crucial step in showing that if a number can be represented as the sum of four rational squares, it can also be represented as the sum of four integer squares. This result is related to Lagrange's four-square theorem, which states that every positive integer can be expressed as the sum of four squares of integers. Aubrey's lemma contributes to the overall proof of Lagrange's theorem by showing that rational solutions imply integer solutions.

### Dependencies
- `num_WOP`
- `AUBREY_LEMMA_4`
- `REAL_DIV_1`
- `ARITH_EQ`

### Name of formal statement
REAL_INTEGER_CLOSURES

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
```

### Informal statement
The absolute value of a real number that is the real representation of a natural number remains the real representation of a natural number under addition, subtraction, multiplication, exponentiation, negation, and absolute value. Formally:
- For all `n`, there exists a `p` such that `abs(&n) = &p`.
- For all `x` and `y`, if there exist `m` and `n` such that `abs(x) = &m` and `abs(y) = &n`, then there exists a `p` such that `abs(x + y) = &p`.
- For all `x` and `y`, if there exist `m` and `n` such that `abs(x) = &m` and `abs(y) = &n`, then there exists a `p` such that `abs(x - y) = &p`.
- For all `x` and `y`, if there exist `m` and `n` such that `abs(x) = &m` and `abs(y) = &n`, then there exists a `p` such that `abs(x * y) = &p`.
- For all `x` and `r`, if there exists an `n` such that `abs(x) = &n`, then there exists a `p` such that `abs(x pow r) = &p`.
- For all `x`, if there exists an `n` such that `abs(x) = &n`, then there exists a `p` such that `abs(--x) = &p`.
- For all `x`, if there exists an `n` such that `abs(x) = &n`, then there exists a `p` such that `abs(abs x) = &p`.

### Informal sketch
The proof demonstrates that the set of real numbers which are the real representation of natural numbers is closed under several arithmetic operations and absolute value.
- First, the tautology `x /\ c /\ d /\ e /\ f /\ (a /\ e ==> b) /\ a ==> x /\ a /\ b /\ c /\ d /\ e /\ f` is used to prepare for repeated application of `CONJ_TAC`.
- Each closure property is proven separately.
- The tactic `MESON_TAC` is used to automate the reasoning for most closure properties.
- The closure under addition and subtraction require more detailed arithmetic reasoning to show that there exists a natural number `p` such that `abs(x + y) = &p` given `abs(x) = &m` and `abs(y) = &n`.
- Specifically, rewriting with the definitions `REAL_NEG_ADD`, `REAL_OF_NUM_ADD`, and arithmetic rules is employed.
- `LE_EXISTS`, `ADD_SYM`, and `LE_CASES` are employed in conjunction with `MESON_TAC` to complete the proofs.

### Mathematical insight
This theorem establishes the closure properties of the real representation of natural numbers under basic arithmetic operations and absolute value. This is important for reasoning about the integer solutions of equations involving real numbers. Namely, If we know that some combination of operations results in a real number that is the representation of a natural number, then it is safe to treat it as an integer.

### Dependencies
- `TAUT`
- `REAL_ABS_NUM`
- `REAL_ABS_MUL`
- `REAL_OF_NUM_MUL`
- `REAL_ABS_POW`
- `REAL_OF_NUM_POW`
- `REAL_ABS_NEG`
- `REAL_ABS_ABS`
- `real_sub`
- `REAL_ARITH` (specific instances used are noted in the tactic script)
- `REAL_POS`
- `GSYM`
- `REAL_NEG_ADD`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_EQ`
- `LE_EXISTS`
- `ADD_SYM`
- `LE_CASES`

### Name of formal statement
REAL_NUM_ROUND

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
```

### Informal statement
For any non-negative real number `x`, there exists a natural number `n` such that the absolute value of the difference between `x` and the real representation of `n` is less than or equal to one-half.

### Informal sketch
The proof relies on the Archimedean property and proceeds as follows:
- Given `x >= 0`, first the Archimedean property is employed through `REAL_ARCH_LEAST` and `REAL_LT_01` to find some `n:num` such that `&n <= x < &n + &1`
- Then, the goal is to that there is one of `&n` or `&(n+1)` at most `1/2` away form `x`.
- Then, the proof proceeds by showing that `abs(x - &n) <= &1 / &2 \/ abs(x - (&n + &1)) <= &1 / &2` using `REAL_ARITH` with a specific conditional expression.
- Finally, simplification and automated reasoning via `MESON_TAC` completes the proof.

### Mathematical insight
This theorem asserts that every non-negative real number can be rounded to the nearest integer with an error of at most 1/2. This property is fundamental in approximation theory and numerical analysis.

### Dependencies
- `REAL_ARCH_LEAST`
- `REAL_LT_01`
- `GSYM`
- `REAL_OF_NUM_SUC`
- `REAL_MUL_RID`
- `REAL_ARITH` (specifically, `a <= x /\ x < a + &1 ==> abs(x - a) * &2 <= &1 \/ abs(x - (a + &1)) * &2 <= &1`)
- `REAL_LE_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `ARITH`
- `MESON_TAC`
- `REAL_OF_NUM_ADD`

### Name of formal statement
REAL_POS_ABS_MIDDLE

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
```

### Informal statement
For all `x` and `n`, if `x` is non-negative and the absolute value of `x` minus the real representation of `n` is equal to 1/2, then `x` is either equal to the real representation of `(n - 1) + 1/2` or `x` is equal to the real representation of `n + 1/2`.

### Informal sketch
The proof proceeds by considering the cases when `n = 0` and `1 <= n` using `ARITH_RULE` and `DISJ_CASES_TAC`.
- If `n = 0` the goal is easily discharged using `REAL_RAT_REDUCE_CONV` and `REAL_ARITH_TAC`
- If `1 <= n`, simplification and rewriting with `REAL_ARITH` completes the proof.

### Mathematical insight
This theorem specifies the possible values of `x` when the absolute difference between `x` and an integer `n` is exactly 1/2, given that `x` is non-negative, essentially pinpointing the two real values equidistant from `n`.

### Dependencies
- `SPECL`
- `REAL_OF_NUM_SUB`
- `ARITH_RULE`
- `DISJ_CASES_TAC`
- `ARITH`
- `MP_TAC`
- `REAL_RAT_REDUCE_CONV`
- `REAL_ARITH_TAC`
- `DISCH_THEN`
- `SYM`
- `SUBST1_TAC`
- `REAL_ARITH`

### Name of formal statement
REAL_RAT_ABS_MIDDLE

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
```

### Informal statement
For all `m`, `n`, and `p`, if the absolute value of `m / p - n` is equal to 1/2, then `m / p` is either equal to `(n - 1) + 1/2` or `m / p` is equal to `n + 1/2`.

### Informal sketch
The proof involves using `REAL_POS_ABS_MIDDLE` to reduce this theorem to be equivalent to that one, and then simplifying with `REAL_LE_DIV`, and `REAL_POS`.
- The `REPEAT STRIP_TAC` removes the forall quantifiers and hypothesis implication.
 - `MATCH_MP_TAC REAL_POS_ABS_MIDDLE` applies `REAL_POS_ABS_MIDDLE`
- The `ASM_SIMP_TAC` discharge the side condition.

### Mathematical insight
This theorem is a generalization of `REAL_POS_ABS_MIDDLE` to rational numbers.

### Dependencies
- `REAL_POS_ABS_MIDDLE`
- `REAL_LE_DIV`
- `REAL_POS`

### Name of formal statement
AUBREY_LEMMA_4

### Type of the formal statement
theorem

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
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;
```

### Informal statement
For all natural numbers `m`, `n`, `p`, `q`, and `r`, and a real number `N`, if `m` is not 0 and not 1, and `(n / m)^2 + (p / m)^2 + (q / m)^2 + (r / m)^2 = N`, then there exist natural numbers `m'`, `n'`, `p'`, `q'`, and `r'` such that `m'` is not 0, `m' < m`, and `(n' / m')^2 + (p' / m')^2 + (q' / m')^2 + (r' / m')^2 = N`.

### Informal sketch
The proof attempts to show, by contradiction, that if `N` is a sum of four rational squares with denominator `m`, then we can find another such representation with a smaller denominator `m'`.
- It begins by assuming the negation, namely that for all `m'`, `n'`, `p'`, `q'`, `r'`, if `~(m' = 0) /\ m' < m`, then it doesn't hold that `(&n' / &m') pow 2 + (&p' / &m') pow 2 + (&q' / &m') pow 2 + (&r' / &m') pow 2 = &N`.
- It is shown that either `m = 2 && EVEN(n' + p' + q' + r') = EVEN(N)` or `(&n / &m - &n') pow 2 + (&p / &m - &p') pow 2 + (&q / &m - &q') pow 2 + (&r / &m - &r') pow 2 < &1`. The proof is split into two main cases:

Case 1: There exist `n'`, `p'`, `q'`, and `r'` such that `&n / &m = &n' + &1 / &2`, `&p / &m = &p' + &1 / &2`, `&q / &m = &q' + &1 / &2`, and `&r / &m = &r' + &1 / &2`. This implies that `m = 2` and that `EVEN(n' + p' + q' + r') = EVEN(N)`.

Case 2: We use the `REAL_NUM_ROUND` theorem to find suitable `n'`, `p'`, `q'`, and `r'` such that `abs(&n / &m - &n') <= &1 / &2`, `abs(&p / &m - &p') <= &1 / &2`, `abs(&q / &m - &q') <= &1 / &2`, and `abs(&r / &m - &r') <= &1 / & 2`. This leads to showing `(&n / &m - &n') pow 2 + (&p / &m - &p') pow 2 + (&q / &m - &q') pow 2 + (&r / &m - &r') pow 2 < &1`.
- We derive a contradiction by assuming  `(&n / &m = &n') /\ (&p / &m = &p') /\ (&q / &m = &q') /\ (&r / &m = &r')`. If the above does not hold, we rewrite the original conditions in terms of `s = &n - &m * &n'`, `t = &p - &m * &p'`, `u = &q - &m * &q'`, `v = &r - &m * &r'`, and `N' = n' EXP 2 + p' EXP 2 + q' EXP 2 + r' EXP 2` to define a candidate for `m'`, namely `m' = (N + N') * m - M`, where `M = 2 * (n * n' + p * p' + q * q' + r * r')`. We can express the original condition `(&n / &m) pow 2 + (&p / &m) pow 2 + (&q / &m) pow 2 + (&r / &m) pow 2 = &N` in terms of `m'`, `N`, and `N'`.
- If `m'` is not zero then there exist `w`, `x`, `y`, `z` such that `w pow 2 + x pow 2 + y pow 2 + z pow 2 = &N` where `w = &n' + s * (&N' - &N) / &m'`, `x = &p' + t * (&N' - &N) / &m'`, `y = &q' + u * (&N' - &N) / &m'`, and `z = &r' + v * (&N' - &N) / &m'`.
- Then, suitable natural numbers `a`, `b`, `c`, and `d` can be found based on the parity of `N` and `N'`, so absolute values are equal to it. Specifically, if `EVEN(N' + N)`, then we can set the denominator to 2, and if it is odd, the denominator can be set to 1.

### Mathematical insight
This lemma is a key step in proving that if a number `N` is expressible as the sum of four rational squares, it is expressible as the sum of four integer squares. The lemma provides a way to reduce the denominators of the rational squares, indicating an inductive approach towards finding integer solutions.

### Dependencies
- `NOT_EXISTS_THM`
- `REAL_NUM_ROUND`
- `REAL_RAT_ABS_MIDDLE`
- `TAUT`
- `ARITH_EQ`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_MUL`
- `real_div`
- `REAL_ADD_RDISTRIB`
- `REAL_MUL_ASSOC`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`
- `EVEN_ADD`
- `ARITH_EVEN`
- `EVEN_EXP`
- `SUBST1_TAC`
- `REAL_ARITH`
- `MONO_EXISTS`
- `EVEN_EXISTS`
- `ODD_EXISTS`
- `REAL_EQ_RCANCEL_IMP`
- `REAL_DIV_RMUL`
- `REAL_POW_MUL`
- `REAL_SUB_RDISTRIB`
- `REAL_POW_2`
- `REAL_MUL_AC`
- `EVEN_EXP`
- `GSYM`
- `REAL_INTEGER_CLOSURES`
- `REAL_POW_LE2`
- `REAL_ABS_POS`
- `REAL_LE_DIV`
- `REAL_POS`
- `REAL_POW_EQ_0`
- `REAL_SUB_0`
- `REAL_ENTIRE`
- `REAL_LE_SQUARE`
- `REAL_POW_LT`


---

## LAGRANGE_IDENTITY

### Name of formal statement
LAGRANGE_IDENTITY

### Type of the formal statement
theorem

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
For all real numbers `w1`, `x1`, `y1`, `z1`, `w2`, `x2`, `y2`, and `z2`, the following equation holds:
`(w1^2 + x1^2 + y1^2 + z1^2) * (w2^2 + x2^2 + y2^2 + z2^2) = (w1*w2 - x1*x2 - y1*y2 - z1*z2)^2 + (w1*x2 + x1*w2 + y1*z2 - z1*y2)^2 + (w1*y2 - x1*z2 + y1*w2 + z1*x2)^2 + (w1*z2 + x1*y2 - y1*x2 + z1*w2)^2`.

### Informal sketch
The proof consists of expanding both sides of the equation and simplifying using real arithmetic.
- Expand both sides of the equation. This primarily involves applying distributivity.
- Simplify the expanded expression. This involves rearranging terms and canceling equal terms on both sides. Applying basic arithmetic properties and simplification tactics will lead to the equation `0 = 0`, thus proving the identity.

### Mathematical insight
This theorem expresses Lagrange's four-square identity, which states that the product of two sums of four squares is itself a sum of four squares. This identity has applications in number theory, particularly in relation to the representation of integers as sums of squares. It also relates to the norm of quaternions.

### Dependencies
- `REAL_ARITH` which encapsulates real number arithmetic simplification procedure.


---

## LAGRANGE_REAL_NUM

### Name of formal statement
LAGRANGE_REAL_NUM

### Type of the formal statement
theorem

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
  REWRITE_TAC[REAL_OF_NUM_MUL] THEN MESON_TAC[REAL_INTEGER_CLOSURES]);;
```

### Informal statement
For every natural number `n`, there exist natural numbers `w`, `x`, `y`, and `z` such that the real number representation of `n` is equal to `w` squared plus `x` squared plus `y` squared plus `z` squared.

### Informal sketch
The proof proceeds by induction and prime factorization.
- First, a lemma is proven, stating that if the absolute values of `w`, `x`, `y`, and `z` exist and are equal to some `a`, `b`, `c`, and `d` respectively, then `w^2 + x^2 + y^2 + z^2 = a^2 + b^2 + c^2 + d^2`.
- The main proof then establishes the theorem.
- The base cases `n = 0` and `n = 1` are handled directly by providing explicit values for `w`, `x`, `y`, and `z`.
- Inductive step: It is shown that if `p` is a prime factor of `n` such that `n = p * m`, then if the theorem holds for `m`, it also holds for `n`.
    - First, the case where `m = 1` is considered. If `m = 1`, then we want to show that `p` can be written as the sum of four squares. This is handled via `LAGRANGE_LEMMA` and `AUBREY_THM_4`.
    - If `m` is not equal to `1`, then `m < n`. In this case, suppose `p` is a prime number of `n`, and `n = p * m`. Since the theorem holds true for `m` and for `p` separately (by the assumption and the lemma), Lagrange's four-square identity (`LAGRANGE_IDENTITY`) is used to deduce that the theorem holds also for `n`. This identity states how the product of sums of four squares is itself a sum of four squares.
    - The properties of real numbers and natural numbers (`REAL_INTEGER_CLOSURES`) are used to complete the proof.

### Mathematical insight
Lagrange's four-square theorem states that every natural number can be represented as the sum of four integer squares. The theorem is a fundamental result in number theory. The tactic `REAL_INTEGER_CLOSURES` applies closure properties of integers and real numbers for proving the theorem. `LAGRANGE_IDENTITY` represents key mathematical idea, the theorem leverages to bridge smaller components to the larger desired outcome.

### Dependencies
**Theorems:**
- `PRIME_FACTOR`
- `LAGRANGE_IDENTITY`
- `AUBREY_THM_4`

**Definitions:**
- `divides`

**Lemmas:**
- `LAGRANGE_LEMMA`

**Tactics**
- `num_WF`
- `PRIME_1`
- `REAL_INTEGER_CLOSURES`
- tactic `lemma` defined locally in the script

### Porting notes (optional)
- The proof relies on the existence of prime factors and on being able to represent the product of sums of four squares as another sum of four squares. The corresponding results must be available in the target proof assistant.
- The overall style is that of a computational proof. The porter should not attempt to shorten the proof until an equivalent version in the target system is achieved.


---

## LAGRANGE_NUM

### Name of formal statement
LAGRANGE_NUM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LAGRANGE_NUM = prove
 (`!n. ?w x y z. n = w EXP 2 + x EXP 2 + y EXP 2 + z EXP 2`,
  GEN_TAC THEN MP_TAC(SPEC `n:num` LAGRANGE_REAL_NUM) THEN
  REWRITE_TAC[REAL_POS; REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ]);;
```
### Informal statement
For every natural number `n`, there exist natural numbers `w`, `x`, `y`, and `z` such that `n` is equal to the sum of the squares of `w`, `x`, `y`, and `z`.

### Informal sketch
The proof proceeds as follows:
- Apply `GEN_TAC` which universally quantifies over `n:num`.
- Apply `MP_TAC(SPEC \`n:num\` LAGRANGE_REAL_NUM)` which performs Modus Ponens with the specialization `n:num` of the theorem `LAGRANGE_REAL_NUM`. This likely instantiates a theorem proved for real numbers to the natural numbers.
- Apply `REWRITE_TAC` with the rewrite rules `REAL_POS`, `REAL_OF_NUM_POW`, `REAL_OF_NUM_ADD`, and `REAL_OF_NUM_EQ`. This converts the real terms into natural number terms. `REAL_POS` eliminates the assumption that the variables `w`, `x`, `y`, and `z` are real numbers because squares must be positive (since `n` is a natural number), meaning their square roots must be real and potentially natural. `REAL_OF_NUM_POW` converts real powers of numbers to numeric powers. `REAL_OF_NUM_ADD` converts sums of real numbers to sums of natural numbers. `REAL_OF_NUM_EQ` converts equality between real numbers to equality between natural numbers.

### Mathematical insight
Lagrange's four-square theorem states that every natural number can be represented as the sum of four integer squares. The theorem `LAGRANGE_NUM` represents the formalization of this statement in HOL Light for natural numbers. This theorem is a fundamental result in number theory.

### Dependencies
- `LAGRANGE_REAL_NUM`
- `REAL_POS`
- `REAL_OF_NUM_POW`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_EQ`


---

## LAGRANGE_INT

### Name of formal statement
LAGRANGE_INT

### Type of the formal statement
theorem

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
    STRIP_TAC THEN ASM_SIMP_TAC[INT_LE_SQUARE; INT_LE_ADD; INT_POW_2]]);;
```

### Informal statement
For all integers `a`, `&0 <= a` if and only if there exist integers `w`, `x`, `y`, and `z` such that `a = w pow 2 + x pow 2 + y pow 2 + z pow 2`.

### Informal sketch
The proof proceeds by splitting the equivalence into two directions:

*   **`&0 <= a ==> ?w x y z. a = w pow 2 + x pow 2 + y pow 2 + z pow 2`**:
    Assume `0 <= a`. Instantiate `INT_FORALL_POS`, converting `a` into a natural number `n`. Apply the theorem `LAGRANGE_REAL_NUM`, which states that every natural number can be expressed as the sum of four squares of real numbers. Convert the equation involving real numbers to one with integers by using several rewriting steps involving `REAL_OF_NUM_POW`, `REAL_OF_NUM_ADD`, `REAL_OF_NUM_EQ`, `INT_OF_NUM_EQ`, `INT_OF_NUM_POW` and `INT_OF_NUM_ADD`. Finally, use `MESON_TAC` to dispatch the goal.

*   **`(?w x y z. a = w pow 2 + x pow 2 + y pow 2 + z pow 2) ==> &0 <= a`**:
    Assume there exists integers `w`, `x`, `y` and `z` such that `a = w pow 2 + x pow 2 + y pow 2 + z pow 2`. The goal is to show that `0 <= a`. This is accomplished using simplification tactics with arithmetic lemmas: `INT_LE_SQUARE`, `INT_LE_ADD`, and `INT_POW_2`.

### Mathematical insight
This theorem states Lagrange's four-square theorem for integers. It is a fundamental result in number theory asserting that every non-negative integer can be written as the sum of four squares. The proof relies on the real number version of Lagrange's four-square theorem (`LAGRANGE_REAL_NUM`) and then converts the result back to integers.

### Dependencies

The following HOL Light definitions and theorems are used:

*   `INT_FORALL_POS`
*   `LAGRANGE_REAL_NUM`
*   `REAL_OF_NUM_POW`
*   `REAL_OF_NUM_ADD`
*   `REAL_OF_NUM_EQ`
*   `INT_OF_NUM_EQ`
*   `INT_OF_NUM_POW`
*   `INT_OF_NUM_ADD`
*   `INT_LE_SQUARE`
*   `INT_LE_ADD`
*   `INT_POW_2`
*   `GSYM`

### Porting notes (optional)
*   The most challenging part of porting this theorem is likely to be the Lagrange's four-square theorem over reals. This might require porting the real number theory first.
*   The tactics `MESON_TAC` could be tricky to replicate in other proof assistants, one would need to resort to elementary number theory to prove this half.
*   Some proof assistants treat natural numbers and integers differently. HOL Light's approach of leveraging reals-level theorem and then converting to integers could necessitate intermediate bridging lemmas.


---

