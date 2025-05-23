# two_squares.ml

## Overview

Number of statements: 24

The file `two_squares.ml` formalizes the representation of prime numbers congruent to 1 modulo 4 as the sum of two squares. It relies on the `prime.ml` library and likely contains definitions and theorems related to this specific number-theoretic result. The core purpose is to provide a formally verified proof of this representation theorem.


## involution

### Name of formal statement
- involution

### Type of the formal statement
- new_definition

### Formal Content
- 
```ocaml
let involution = new_definition
  `involution f s = !x. x IN s ==> f(x) IN s /\ (f(f(x)) = x)`;;
```

### Informal statement
- We define `involution f s` to be true if and only if for all `x`, if `x` is in the set `s`, then `f(x)` is in the set `s` and `f(f(x))` is equal to `x`.

### Informal sketch
- The definition introduces the concept of an involution, a function that, when applied twice, returns the original argument. The definition states that for a function `f` to be an involution on a set `s`, it must map elements of `s` to elements of `s`, and applying `f` twice to any element in `s` must yield the original element.
- There is no proof sketch as this is a definition.

### Mathematical insight
- This definition formalizes the notion of an involution within set theory. The condition `x IN s ==> f(x) IN s` indicates that the set `s` is closed under the action of `f`. The condition `f(f(x)) = x` enforces the involutive property, that `f` is its own inverse when restricted to `s`. This definition serves as a foundation for reasoning about functions that exhibit this self-inverse behavior within a specific domain.

### Dependencies
- None


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
For any function `f` and set `s`, if `f` is an involution on `s`, then the image of `s` under `f` is equal to `s`.

### Informal sketch
The proof proceeds as follows:
- Assume `f` is an involution on `s`. This means that for any `x` in `s`, `f(f(x)) = x`.
- To prove `IMAGE f s = s`, we show mutual inclusion: `IMAGE f s SUBSET s` and `s SUBSET IMAGE f s`.
  - To show `IMAGE f s SUBSET s`, assume `y IN IMAGE f s`. Then there exists `x IN s` such that `f x = y`. Since `f` is an involution on `s`, `y IN s`.
  - To show `s SUBSET IMAGE f s`, assume `x IN s`. Since `f` is an involution on `s`, `f (f x) = x` and `f x IN s`. Then `x IN IMAGE f s`, specifically when we apply `f` to `f x`.
- By extensionality, `IMAGE f s = s`.

### Mathematical insight
This theorem states a fundamental property of involutions on sets. An involution, by definition, is its own inverse on a given set. Thus, when an involution is applied to a set, the resulting image is the same set itself. This reflects the symmetrical nature of involutions.

### Dependencies
- Definitions: `involution`, `IMAGE`
- Theorems: `EXTENSION`, `IN_IMAGE`


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
If `f` is an involution on a set `s`, and `a` is an element of `s` such that `f a = a`, then `f` is also an involution on the set obtained by deleting `a` from `s`.

### Informal sketch
The proof proceeds by rewriting with the definitions of `involution` and `IN_DELETE` and then using a MESON call. The core idea is to show that if removing a fixed point from a set preserves the involution property, we need to demonstrate that for any element in the smaller set (i.e., the original set without `a`), applying `f` twice yields the original element, which follows directly from `f` being an involution on the original set.

### Mathematical insight
This theorem demonstrates a property of involutions. Removing a fixed point from a set on which a function is an involution preserves the involution property for the remaining set. This is a useful fact for simplifying involutions or reasoning about them in a more refined setting.

### Dependencies
Definitions:
- `involution`

Theorems:
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
For any function `f` and set `s`, if `f` is an involution on `s` and `a` is an element of `s`, then `f` is an involution on the set `s` excluding `a` and `f a`.

### Informal sketch
The theorem states that if a function `f` is an involution on a set `s`, and an element `a` is in `s`, then `f` is also an involution on the set `s` with `a` and `f a` removed. The proof proceeds by rewriting with the definition of `involution`, and set membership properties such as `IN_DIFF`, `IN_INSERT`, and `NOT_IN_EMPTY`. Then `MESON_TAC` is used to complete the proof.
- Assume `involution f s` and `a IN s`.
- Need to show `involution f (s DIFF {a, f a})`.
- Unfold `involution` using `REWRITE_TAC[involution]`.
- Need to show the two conditions for `involution`, namely `!x. x IN s ==> f x IN s` and `!x. x IN s ==> f (f x) = x`, hold for `s DIFF {a, f a}`.
- Use set membership properties like `IN_DIFF`, `IN_INSERT`, and `NOT_IN_EMPTY` through `REWRITE_TAC` to simplify terms involving set differences.
- Finally, call `MESON_TAC` to discharge the remaining goals using classical reasoning.

### Mathematical insight
The theorem expresses the idea that involutions can be restricted to smaller sets by removing elements and their images without losing the involution property. It incrementally reduces the size of the sets on which the involution is defined.

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
If `f` is an involution on the set `s`, then `f` is also an involution on the set of elements `x` in `s` such that `f(x)` is not equal to `x`.

### Informal sketch
*   The proof starts with the hypothesis that `f` is an involution on the set `s`.
*   The goal is to show that `f` is an involution on the set `{x | x IN s /\ ~(f x = x)}`.
*   This is achieved by rewriting using the definition of `involution` and the theorem `IN_ELIM_THM` to eliminate set membership. Finally, the remaining goal is dispatched using `MESON_TAC[]`.

### Mathematical insight
The theorem states that if a function `f` is an involution on a set `s`, then it remains an involution when restricted to the subset of `s` that excludes the fixed points of `f`. This is because an involution maps elements to their inverses, and if we exclude the fixed points (elements that map to themselves), the involution property is preserved on the remaining elements.

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
For all functions `f`, and sets `s` and `t`, if `f` is an involution on `s`, and for all `x`, if `x` is in `t` then `f(x)` is in `t`, and `t` is a subset of `s`, then `f` is an involution on `t`.

### Informal sketch
The proof proceeds by showing that if `f` is an involution on `s`, and `t` is a subset of `s` such that `f(x)` is in `t` whenever `x` is in `t`, then `f` is an involution on `t`. This involves showing that the domain of `f` when restricted to `t` is `t`, which is immediate from the assumption `!x. x IN t ==> f(x) IN t`, and that for all `x` in `t`, `f(f(x)) = x`, which follows from `f` being an involution on `s` and the fact that `t` is a subset of `s`. The tactics used are `REWRITE_TAC` with `involution` and `SUBSET` to expand the definitions, and `MESON_TAC` to complete the proof using the expanded definitions and assumptions.

### Mathematical insight
This theorem states that if a function `f` is an involution on a set `s`, then it is also an involution on any subset `t` of `s` that is closed under `f`. This is a useful property when dealing with involutions, as it allows us to restrict the domain of the involution to a smaller set without losing the involution property. The restriction is useful for building inductive definitions or proving results by induction.

### Dependencies
* Definitions:
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
For all sets `s`, if `s` is finite, `f` is an involution on `s`, and for all `x`, if `x` is in `s`, then `f(x)` is not equal to `x`, then the cardinality of `s` is even.

### Informal sketch
The proof shows that a finite set `s` acted upon by an involution `f`, which has no fixed points in `s`, must have an even cardinality.
- The theorem `INVOLUTION_EVEN_NOFIXPOINTS` presumably formalizes the fact that if `f` is an involution on `s` with no fixed points, then `s` can be partitioned into pairs `(x, f(x))`.
- The step `REWRITE_TAC[involution]` likely expands the definition of `involution f s`, i.e., `!x. x IN s ==> f x IN s /\ f (f x) = x`.
- The step `MESON_TAC[INVOLUTION_EVEN_NOFIXPOINTS]` calls an external automatic theorem prover to deduce the result.

### Mathematical insight
An involution without fixed points on a finite set pairs elements, implying an even cardinality. This theorem formalizes a fundamental property of involutions and their relation to set cardinality. It is a key component in enumerative combinatorics and often used when counting objects by pairing them.

### Dependencies
- Definitions: `involution`, `FINITE`, `CARD`, `EVEN`, `IN`
- Theorems: `INVOLUTION_EVEN_NOFIXPOINTS`


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
If `s` is a finite set, `f` is an involution on `s`, and there exists exactly one element `a` in `s` such that `f a = a`, then the cardinality of `s` is odd.

### Informal sketch
The proof proceeds as follows:

- Assume `FINITE(s)` and `involution f s` and `?!a. a IN s /\ (f a = a)`.
- Show that there exists a unique `a` such that `s` can be expressed as the insertion of `a` into `s` after deleting `a`, i.e., `s = INSERT a (DELETE a s)`. This step uses `EXISTS_UNIQUE_DEF`, `EXTENSION`, `IN_INSERT` and `IN_DELETE`.
- Apply `CARD_CLAUSES`, `FINITE_DELETE`, `IN_DELETE`, `ODD`, and `NOT_ODD` to simplify the expression.
- Apply the theorem `INVOLUTION_EVEN`, which states that if `f` is an involution on a set `s`, and `s` is finite, then if the cardinality of `s` is even then `f` has no fixed points.
- Simplify with `INVOLUTION_DELETE`, `FINITE_DELETE`, and `IN_DELETE`.
- Conclude using a Meson-based automated proof search.

### Mathematical insight
The core idea is that an involution (a function that is its own inverse) either has elements that map to themselves (fixed points) or pairs of distinct elements that map to each other. If there is exactly one fixed point, the remaining elements must form pairs, implying that the cardinality of the set is odd. This theorem relates the existence and number of fixed points of an involution on a finite set to the parity of its cardinality.

### Dependencies
- `EXISTS_UNIQUE_DEF`
- `EXTENSION`
- `IN_INSERT`
- `IN_DELETE`
- `CARD_CLAUSES`
- `FINITE_DELETE`
- `ODD`
- `NOT_ODD`
- `INVOLUTION_EVEN`
- `INVOLUTION_DELETE`


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
For all sets `s` and functions `f`, if `s` is finite and `f` is an involution on `s`, and the cardinality of `s` is odd, then there exists an element `a` in `s` such that `f(a) = a`.

### Informal sketch
*   The proof proceeds by contradiction. Assuming `FINITE(s)` and `involution f s` and `ODD(CARD s)` and that there does not exist a fixpoint `a` in `s` such that `f a = a.`
*   Then it concludes that `CARD s` must be even using `INVOLUTION_EVEN`.
*   The contradiction with `ODD(CARD s)` is resolved using `NOT_EVEN`.

### Mathematical insight
This theorem states that any involution (a function that is its own inverse, i.e., `f(f(x)) = x`) defined on a finite set with an odd number of elements must have at least one fixed point (an element that `f` maps to itself). This is a fundamental result related to the combinatorial properties of involutions on finite sets.

### Dependencies
- Theorems: `INVOLUTION_EVEN`, `GSYM`, `NOT_EVEN`
- Definitions: `FINITE`, `involution`, `ODD`, `CARD`


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
The proof proceeds as follows:
- Assume `s` is finite, `f` and `g` are involutions on `s`, and `f` has a fixed point in `s`.
- Apply the theorem `INVOLUTION_ODD` to deduce that if an involution has no fixed point, then `FINITE(s)` implies that `CARD(s)` is even. Use the contrapositive.
- Proceed by cases based on whether `g` has a fixed point in `s`. If it does, the goal is proved.
- If `g` has no fixed point in `s`, then use theorem `INVOLUTION_FIX_ODD` to demonstrate the number of element in `s` is even and greater than or equal to 2. By contraposition, it proves that there is at least one element in `s` fixed by `g`.

### Mathematical insight
The theorem states that if two involutions are defined on the same finite set, and one of them has a fixed point, then the other one must also have a fixed point. This relates the existence of fixed points for different involutions on a finite set.

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
The set `zset(a)` is defined as the set of all triples `(x, y, z)` such that `x` squared plus `4` times `y` times `z` equals `a`.

### Informal sketch
- Define `zset(a)` to be the set of all triples `(x, y, z)` satisfying the equation `x^2 + 4yz = a`.

### Mathematical insight
The definition `zset` formalizes the set of integer triples satisfying a specific quadratic Diophantine equation. This set is central to Zagier's one-sentence proof regarding sums of two squares.

### Dependencies
None


---

## zag

### Name of formal statement
- zag

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let zag = new_definition
  `zag(x,y,z) =
        if x + z < y then (x + 2 * z,z,y - (x + z))
        else if x < 2 * y then (2 * y - x, y, (x + z) - y)
        else (x - 2 * y,(x + z) - y, y)`;;
```
### Informal statement
- Define a function `zag` of three variables `x`, `y`, and `z`. The value of `zag(x, y, z)` is a triple determined by the following conditions:
  - if `x + z` is less than `y`, then `zag(x, y, z)` is the triple `(x + 2 * z, z, y - (x + z))`;
  - otherwise, if `x` is less than `2 * y`, then `zag(x, y, z)` is the triple `(2 * y - x, y, (x + z) - y)`;
  - otherwise, `zag(x, y, z)` is the triple `(x - 2 * y, (x + z) - y, y)`.

### Informal sketch
- The definition of `zag` is a straightforward conditional definition, with three cases based on the relative values of `x`, `y`, and `z`.
  - The first condition checks if `x + z < y`.
  - The second condition, checked only if the first is false, checks if `x < 2 * y`.
  - If both of the above are false, a third case is selected by default.
  - Each branch constructs a different triple based on `x`, `y`, and `z`.

### Mathematical insight
- The function `zag` defines a piecewise function that maps three inputs `x`, `y`, and `z` to a triple. The intent and purpose of this function depend on the context in which it is used. Typically, piecewise function definitions provide different behaviors in different areas of the function's domain.

### Dependencies
- None.


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
The function `tag`, when applied to a triple `(x, y, z)` of natural numbers, returns the triple `(x, z, y)`.

### Informal sketch
- The definition introduces a function `tag` that swaps the second and third elements of a triple of natural numbers.
- The definition proceeds by directly specifying the result of applying `tag` to a general triple `(x,y,z)`.

### Mathematical insight
The `tag` function represents a simple permutation or rearrangement of elements within a tuple. It is a basic example of how functions can manipulate data structures. This function could be useful in contexts where the order of elements in a triple needs to be rearranged.

### Dependencies
None

### Porting notes (optional)
This definition should be straightforward to port to other proof assistants. The key is to ensure that the syntax for defining functions and tuple structures is correctly translated. No complex automation or reasoning is required.


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
If `0 < x` and `0 < y` and `0 < z`, then `zag(zag(x,y,z)) = (x,y,z)`.
Here, `zag` is a function that likely swaps two variables based on conditions derived from `x`, `y` and `z`.

### Informal sketch
The proof proceeds by showing that applying the `zag` function twice returns the original triple `(x,y,z)`.

- The proof starts by rewriting with the definition of `zag`.
- Then, it applies conditional case splitting (`COND_CASES_TAC`) repeatedly, coupled with assumption rewriting (`ASM_REWRITE_TAC[]`), to handle the different cases arising from the conditions in the definition of `zag`. This likely involves checking the order of `x`, `y`, and `z`, according to the definition of `zag`.
- The definition of `zag` is rewritten again to undo the first application, this time utilizing information derived from the case splitting.
- Again, conditional case splitting and assumption rewriting are applied to handle different arising from the conditional definition of `zag`.
- Then, rewriting with the definition of `PAIR_EQ` allows us to compare pairs of elements.
- The assumptions are then moved into the goal using `POP_ASSUM_LIST` and combined using conjunction (`CONJ`), and `MP_TAC` is subsequently applied.
- Finally, `ARITH_TAC` concludes the arithmetic reasoning to prove the goal.

### Mathematical insight
The theorem demonstrates that the `zag` function, when applied twice, acts as an involution. An involution is a function that is its own inverse. This is significant because it implies that the `zag` transformation is a reversible operation: applying it twice undoes the initial transformation.

### Dependencies
- Definition: `zag`
- Theorem: `PAIR_EQ`


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
For any predicate `P` of three variables, an ordered triple `(a, b, c)` is a member of the set of ordered triples `(x, y, z)` such that `P x y z` holds if and only if `P a b c` holds.

### Informal sketch
The proof proceeds by rewriting the membership condition using `IN_ELIM_THM`, which states that `x IN {y | P y} <=> P x`, and the definition of equality for pairs (`PAIR_EQ`, which likely expands to `(a,b) = (c,d) <=> a = c /\ b = d`), followed by automatic theorem proving using `MESON_TAC`.  
- The rewriting step replaces `(a,b,c) IN {(x,y,z) | P x y z}` with `{(a,b,c) = (x,y,z) | P x y z}`.
- The equality of triples is reduced to the conjunction of pairwise equality of their components.
- `MESON_TAC` then automatically proves the equivalence `(a = x) /\ (b = y) /\ (c = z) <=> P a b c` from the assumption `P x y z`.

### Mathematical insight
This theorem formalizes the standard set membership condition for triples defined by a predicate. It provides a rule to unpack set membership into the defining predicate.

### Dependencies
- Theorems: `IN_ELIM_THM`, `PAIR_EQ`


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
For all natural numbers `n`, it is not the case that `n * n` is prime.

### Informal sketch
The proof proceeds by contradiction and case analysis.

- We begin by assuming that there exists a number `n` such that `n * n` is prime.
- We then perform case analysis on whether `n = 0`.
  - If `n = 0`, then `n * n = 0`, and `0` is not prime.
  - Otherwise, we proceed to the next case.
- We perform case analysis on whether `n = 1`.
  - If `n = 1`, then `n * n = 1`, and `1` is not prime (by `ARITH`).
  - Otherwise, we proceed to the next case.
- If `n` is neither `0` nor `1`, we show that `n * n` is not prime by exhibiting a divisor of `n * n`, namely `n` itself. This involves:
  - Instantiating the definition of `prime` and using De Morgan's law to rewrite the goal.
  - Showing that `n` divides `n * n`. Since `n * n = n * 1 * n`, then `n` obviously divides `n*n`.
  - We discharge the divisibility goal by rewriting using `DIVIDES_LMUL` and `DIVIDES_REFL`. We use `ARITH_RULE \`n = n * 1\`` to show that `n = 1 * n`
  - Since we have found a divisor `n` of `n*n` that is not 1 or `n*n` (since `n` is not 0, 1, or `n*n`), we conclude that `n * n` is not prime.

### Mathematical insight
The theorem formalizes the basic fact that the square of any natural number is never prime, except trivially for 1 * 1 = 1, which is not prime by definition. The proof explicitly considers the special cases of 0 and 1.

### Dependencies
- `prime` (definition of primality)
- `PRIME_0` (0 is not prime)
- `MULT_CLAUSES` (multiplication properties)
- `NOT_FORALL_THM` (negation of universal quantifier)
- `DE_MORGAN_THM` (De Morgan's law)
- `ARITH` (arithmetic facts)
- `DIVIDES_LMUL` (divisibility and left multiplication)
- `DIVIDES_REFL` (reflexivity of divisibility)
- `EQ_MULT_LCANCEL` (cancellation law for multiplication)

### Porting notes (optional)
- The proof relies on rewriting with primality conditions and divisibility. Ensure the target proof assistant has similar definitions and support for rewriting with related properties.
- The automation through `ASM_SIMP_TAC` might need to be replaced with more explicit rewriting steps in other systems.


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
The theorem states that no multiple of 4 is prime. The proof proceeds as follows:
- Rewrite the goal using the definition of `prime`, `NOT_FORALL_THM`, and `DE_MORGAN_THM` to transform the goal `!n. ~prime(4 * n)` into `!n. exists p. p divides 4 * n /\ p != 1 /\ p != 4 * n`.
- Apply `EXISTS_TAC` with the witness `2` to transform the goal  `!n. exists p. p divides 4 * n /\ p != 1 /\ p != 4 * n` into the goal `!n. 2 divides 4 * n /\ 2 != 1 /\ 2 != 4 * n`.
- Substitute `2 * 2` for `4` in the term `4 * n`.
- Simplify using associativity of multiplication (`MULT_ASSOC`), the rule `DIVIDES_RMUL` which states `!m n p. p divides m ==> p divides m * n`, the reflexivity of divides (`DIVIDES_REFL`), and arithmetic reasoning (`ARITH_EQ`).
- Perform a case split on `n = 0`.
- In the case `n = 0`, use arithmetic to discharge the goal.
- In the case `n != 0`, use arithmetic to discharge the goal.

### Mathematical insight
This theorem formalizes the basic number-theoretic fact that any multiple of 4 cannot be a prime number because it is divisible by 2.

### Dependencies
- `prime`
- `NOT_FORALL_THM`
- `DE_MORGAN_THM`
- `MULT_ASSOC`
- `DIVIDES_RMUL`
- `DIVIDES_REFL`
- `ARITH_EQ`


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
The proof proceeds by contraposition and cases.
- The goal is reduced to proving `~(0 < x /\ 0 < y /\ 0 < z) ==> ~prime(x EXP 2 + 4 * y * z)`.
- The antecedent `~(0 < x /\ 0 < y /\ 0 < z)` is rewritten to `x = 0 \/ y = 0 \/ z = 0`.
- Case 1: `x = 0`. Then `x^2 + 4yz = 4yz`.  The theorem `PRIME_4X` (if `4 * y * z` is prime then `y = 0 \/ z = 0`) is used to show that  `4yz` cannot be prime.
- Case 2: `y = 0`. Then `x^2 + 4yz = x^2`. The theorem `PRIME_SQUARE` (if `x^2` is prime then `x = 1 /\ 1 = -1`) is then used to show that `x^2` cannot be prime.
- Case 3: `z = 0`. Then `x^2 + 4yz = x^2`. The theorem `PRIME_SQUARE` (if `x^2` is prime then `x = 1 /\ 1 = -1`) is then used to show that `x^2` cannot be prime.

### Mathematical insight
Intuitively, if any of $x, y, z$ is zero, then $x^2 + 4yz$ is either a square or a multiple of 4, and thus cannot be prime (except in trivial cases that lead to contradictions).

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
For all primes `p`, the function `zag` is an involution on the set `{ (x, y, z) | x * x + y * y + z * z = p }`.

### Informal sketch
The proof proceeds as follows:
- Start by assuming `p` is prime and proving `involution zag (zset(p))`.
- Expand the definitions of `involution` and `zset`.
- Introduce variables `x`, `y`, and `z` and rewrite the condition `(x, y, z) IN zset p` to `x * x + y * y + z * z = p`.
- Prove that `zag (x, y, z) = (x, y, z)` implies `x = y = z`. This has subgoals:
    - Show that `(x, y, z)` satisfies the `zag` transformation twice corresponds to `(x, y, z)` itself, using conditional case analysis based on which value is the largest and rewriting with the definition `zag` and rules related to arithmetic operations. This shows that `zag` is an involution.
    - Establish that `p` can be represented as a sum of three squares if and only if the prime factorization of `p` does not contain any prime congruent to 3 modulo 4 raised to an odd power, using ZAG_INVOLUTION_GENERAL and PRIME_XYZ_NONZERO.

### Mathematical insight
This theorem proves that the function `zag`, which is a transformation on triples of numbers, is an involution (i.e., applying it twice returns the original input) when restricted to the set of triples whose squared components sum to a prime number `p`. This property is important in the broader mathematical context of representing numbers as sums of squares.

### Dependencies
- `involution`
- `FORALL_PAIR_THM`
- `zset`
- `IN_TRIPLE`
- `zag`
- `NOT_LT`
- `INT_OF_NUM_EQ`
- `INT_OF_NUM_ADD`
- `EXP_2`
- `INT_OF_NUM_MUL`
- `INT_OF_NUM_SUB`
- `LT_IMP_LE`
- `ZAG_INVOLUTION_GENERAL`
- `PRIME_XYZ_NONZERO`


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
The proof demonstrates that `tag` is an involution when applied to the set `zset a`.
- Expand the definitions of `involution`, `tag`, and `zset` using the `REWRITE_TAC` tactic using the theorems or definitions named `involution`, `tag`, `zset`, and `FORALL_PAIR_THM`.
- Rewrite using `IN_TRIPLE` to expand the definition of membership in the triples that arise from the definition of `zset`.
- Use `MULT_AC` to rearrange the multiplication in the resulting statement to show that `tag (zset a)` returns the original input `a`.

### Mathematical insight
The theorem shows that the `tag` function, when applied to the specific set `zset a`, acts as an involution, meaning applying it twice returns the original input. This is significant in the context of whatever system `tag` and `zset` are being used, often in the context of representing primitive recursive functions or set-theoretic encodings. This involution property could be exploited in subsequent reasoning steps or optimizations.

### Dependencies
- Definitions: `involution`, `tag`, `zset`
- Theorems: `FORALL_PAIR_THM`, `IN_TRIPLE`, `MULT_AC`

### Porting notes (optional)
- The main challenge in porting this theorem lies in ensuring that the definitions of `involution`, `tag`, and `zset` are correctly translated into the target proof assistant.
- The `REWRITE_TAC` tactic is used extensively, suggesting that the proof relies on equational reasoning and simplification. Similar tactics or methods for rewriting terms should be available in other systems.
- The tactic `MULT_AC` represents some form of algebraic manipulation related to associativity and commutativity of multiplication, which should also be available similarly in other proof assistants. Carefully verify the assumptions and behaviour of such tactics, as details of automated rewriting are inherently system-dependent.


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
If `zag(x,y,z) = (x,y,z)`, then `y = x`.

### Informal sketch
The proof proceeds as follows:
- Rewrite the hypothesis using the definition of `zag` and `INT_POW_2`. This reveals the structure of the triple `(x + z * 2, y + z * 2, z)`.
- Perform case splits on all assumptions derived from equality on pairs, and simplify using pairing axioms (`PAIR_EQ`).
- Use transitivity of implication to reduce the hypotheses via `POP_ASSUM_LIST(MP_TAC o end_itlist CONJ)`.
- Apply linear arithmetic to conclude `y = x`.

### Mathematical insight
The lemma demonstrates what can be inferred when the `zag` function returns a triple identical to its inputs. Given that `zag` essentially encodes two integers into a larger integer using a base-2 representation, the equality `zag(x, y, z) = (x, y, z)` implies a relationship between `x`, `y`, and `z`, specifically `y=x`.

### Dependencies
- Definitions: `zag`
- Theorems: `INT_POW_2`, `PAIR_EQ`
- Tactics: `REWRITE_TAC`, `COND_CASES_TAC`, `ASM_SIMP_TAC`, `POP_ASSUM_LIST`, `MP_TAC`, `end_itlist`, `CONJ`, `ARITH_TAC`


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
Given that `0 < y`, `0 < z`, and `x^2 + 4 * y * z = p`, then `x <= p`, `y <= p`, and `z <= p`.

### Informal sketch
The proof proceeds as follows:

- Assume `0 < y`, `0 < z`, and `x^2 + 4 * y * z = p`.
- Show that `x <= p` using the assumption `x^2 + 4 * y * z = p`.
  - Use the fact that `x^2 >= 0`, the assumption `x^2 + 4 * y * z = p`, and the theorem `a <= b ==> a <= b + c` to prove `x^2 <= p`. Since `x^2 >=0`, we can infer that adding it to something gives an equal or bigger number. 
  - Use `MESON_TAC` to attempt to solve using the given assumptions and theorems, which should be able to prove `x <= p`.
- Show that `y <= p` and `z <= p`.
  - First, show that `y <= z`. We assume `0 < y` and `0 < z`.
  - Use the fact that `y <= x + z`. `MATCH_MP_TAC` applies the theorem `y <= z ==> y <= x + z`
  - Then, we need to show that `y <= 4 * y * z` which is equivalent to `1 * y <= (4 * z) * y`.
  - Use the lemma `LE_MULT_RCANCEL` and assumption `0 < z ` to simplify the inequality to `1 <= 4 * z`.
  - Because `0 < z`, we know that `1 <= 4 * z` holds.

### Mathematical insight
The theorem provides bounds on the values of `x`, `y`, and `z` given the constraints that `y` and `z` are positive and `x^2 + 4 * y * z = p`. The theorem is useful because it provides upper bounds for `x`, `y`, and `z` in terms of `p`.

### Dependencies
* Theorems: `EXP_2`, `LE_SQUARE_REFL`.
* ARITH_RULE: `(a <= b ==> a <= b + c)`, `y <= z ==> y <= x + z`, `y <= 4 * a * y <=> 1 * y <= (4 * a) * y`, `0 < a ==> 1 <= 4 * a`.
* Definitions: `MULT_SYM`, `LE_MULT_RCANCEL`


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
For all primes `p`, the set of triples `(x, y, z)` such that `x * x + y * y = z * z` and `0 < x < y < z < p + 1` is finite.

### Informal sketch
The proof demonstrates that for any prime `p`, the set `zset p` of triples `(x, y, z)` satisfying `x^2 + y^2 = z^2` and `0 < x < y < z < p + 1` is finite.

- Start by discharging the assumption `prime(p)`.
- Use the theorem `FINITE_NUMSEG_LT` to show that the set of natural numbers less than `p+1` is finite.
- Establish a connection between the finiteness of the set of triples and the finiteness of the set of numbers less than `p + 1`. This involves using `FINITE_PRODUCT` twice on the set of numbers less than `p+1`, showing that the set of triples each element of which is less than `p+1` is finite.
- Use `FINITE_SUBSET` to demonstrate that if one set is finite, then all of its subsets are also finite.
- Rewrite using definitions of `zset`, `SUBSET`, `FORALL_PAIR_THM`, and membership in a triple (`IN_TRIPLE`).
- Introduce existential quantifiers for `x`, `y`, and `z`.
- Simplify the condition `x < p + 1` to `x <= p`.
- Eliminate existential quantifiers using `EXISTS_TAC.`
- Apply assumptions, rewrite, and use the theorem `RIGHT_AND_EXISTS_THM`
- Apply `ASM_MESON_TAC` with `ZSET_BOUND` and `PRIME_XYZ_NONZERO` to automatically resolve the remaining goal.

### Mathematical insight
This theorem shows that for any given prime number `p`, the number of Pythagorean triples `(x, y, z)` that satisfy the condition that all elements are positive and less than `p + 1` is finite. This is a specific case of a more general result concerning the finiteness of sets defined by Diophantine equations within bounded domains.

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
- `RIGHT_AND_EXISTS_THM`
- `ZSET_BOUND`
- `PRIME_XYZ_NONZERO`


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
The proof demonstrates that every prime number of the form `4k + 1` can be expressed as the sum of two squares. The proof proceeds as follows:
- Establish the existence of a fixed point `t` within the set `zset(p)` such that `tag(t) = t`. This involves rewriting the existence and set membership conditions and using an arithmetic rule.
- Apply the involution `INVOLUTION_FIX_FIX` and introduce a term `zag`. Simplify using rules for `ZAG_INVOLUTION`, `TAG_INVOLUTION`, and `ZSET_FINITE`.
- Rewrite using the alternative definition of unique existence and provide witnesses `1`, `1`, and `k` as num.
- Universally quantify `x`, `y`, and `z` and perform equality reasoning by discharging an assumption and rewriting using terms for `zset`, `zag`, `IN_TRIPLE`, and rewriting relational operators
- Rewrite with `zset` and `IN_TRIPLE`, strip the goal, and use ZAG_LEMMA to substitute based on an assumption.
- Eliminate the power and re-write the formula `x EXP 2 + 4 * x * z = x * (4 * z + x)` and assume its symmetric equation. Assume that `prime p`
- Apply the definition of primality to the goal and split assumption disjunctively. Apply divisibility rules to simplify by cases. Split by cases using assumptions.
- These cases directly imply goals by use of arithmetic simplifications.

### Mathematical insight
This theorem, often called Fermat's theorem on sums of two squares, is a classical result in number theory. It asserts that an odd prime number `p` can be expressed as `x^2 + y^2` for integers `x` and `y` if and only if `p` is congruent to 1 modulo 4. The theorem is significant because it connects primality, quadratic forms, and modular arithmetic.

### Dependencies
- Definitions: `prime`, `EXP`, `zset`, `tag`, `zag`
- Theorems/Lemmas: `LEFT_IMP_EXISTS_THM`, `FORALL_PAIR_THM`, `INVOLUTION_FIX_FIX`, `ZAG_INVOLUTION`, `TAG_INVOLUTION`, `ZSET_FINITE`, `EXISTS_UNIQUE_ALT`, `ZAG_LEMMA`, `DIVIDES_RMUL`, `DIVIDES_REFL`
- Rules: `ARITH_RULE`

### Porting notes (optional)
- The proof relies heavily on rewriting and arithmetic simplification, so automation for these tasks will be crucial in other proof assistants.
- The concept of an "involution" and its fixed points plays a key role. Ensure the target proof assistant has similar infrastructure, or be prepared to define it.
- The `zag` relation and `ZAG_LEMMA` seem specific to this proof (and perhaps to HOL Light's number theory library). Porting this may require reimplementing the underlying argument or finding an equivalent result.


---

