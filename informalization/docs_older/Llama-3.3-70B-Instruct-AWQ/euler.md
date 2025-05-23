# euler.ml

## Overview

Number of statements: 22

The `euler.ml` file in HOL Light formalizes Euler's partition theorem and other elementary partition theorems. It provides a foundation for exploring and proving results related to partitions, focusing on the fundamental concepts introduced by Euler. The file's content is self-contained, as indicated by the absence of imports, and is likely used to establish basic results in number theory within the HOL Light library. Its key content includes definitions and proofs related to these theorems, serving as a basis for further development of partition-related theories.

## NSUM_BOUND_LEMMA

### Name of formal statement
NSUM_BOUND_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NSUM_BOUND_LEMMA = prove
 (`!f a b n. nsum(a..b) f = n ==> !i. a <= i /\ i <= b ==> f(i) <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM IN_NUMSEG] THEN
  MATCH_MP_TAC NSUM_POS_BOUND THEN ASM_REWRITE_TAC[LE_REFL; FINITE_NUMSEG])
```

### Informal statement
For all functions `f`, and for all integers `a`, `b`, and `n`, if the sum of `f` from `a` to `b` equals `n`, then for all integers `i` such that `a` is less than or equal to `i` and `i` is less than or equal to `b`, `f(i)` is less than or equal to `n`.

### Informal sketch
* The proof starts by assuming the premise that the sum of `f` from `a` to `b` equals `n`.
* It then applies `GEN_TAC` repeatedly to generalize the variables, followed by `STRIP_TAC` to remove the outermost universal quantifier.
* The `REWRITE_TAC` tactic is used with `GSYM IN_NUMSEG` to rewrite the expression for the sum in terms of the `IN_NUMSEG` predicate.
* The `MATCH_MP_TAC` tactic is applied with `NSUM_POS_BOUND` to match the current goal with the conclusion of the `NSUM_POS_BOUND` theorem.
* Finally, `ASM_REWRITE_TAC` is used with `LE_REFL` and `FINITE_NUMSEG` to perform additional rewrites.

### Mathematical insight
This theorem provides a bound on the values of a function `f` within a given range, based on the sum of `f` over that range. It is useful in establishing properties of functions and their sums, particularly in contexts where bounds on function values are necessary.

### Dependencies
* Theorems:
  * `NSUM_POS_BOUND`
* Definitions:
  * `nsum`
  * `IN_NUMSEG`
* Other:
  * `LE_REFL`
  * `FINITE_NUMSEG`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of binders and the representation of the `nsum` function. The `MATCH_MP_TAC` tactic may need to be replaced with a similar tactic in the target system, and the `ASM_REWRITE_TAC` tactic may require adjustments to accommodate differences in rewriting mechanisms. Additionally, the `NSUM_POS_BOUND` theorem and other dependencies will need to be ported or established in the target system.

---

## CARD_EQ_LEMMA

### Name of formal statement
CARD_EQ_LEMMA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let CARD_EQ_LEMMA = prove
 (`!f:A->B g s t.
        FINITE s /\ FINITE t /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> g(y) IN s) /\
        (!x. x IN s ==> g(f x) = x) /\
        (!y. y IN t ==> f(g y) = y)
        ==> FINITE s /\ FINITE t /\ CARD s = CARD t`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
  EXISTS_TAC `g:B->A` THEN ASM_MESON_TAC[])
```

### Informal statement
For all functions `f` from set `A` to set `B` and `g` from set `B` to set `A`, and for all sets `s` and `t`, if `s` is finite and `t` is finite, and for all `x` in `s`, `f(x)` is in `t`, and for all `y` in `t`, `g(y)` is in `s`, and for all `x` in `s`, `g(f(x))` equals `x`, and for all `y` in `t`, `f(g(y))` equals `y`, then `s` is finite and `t` is finite and the cardinality of `s` equals the cardinality of `t`.

### Informal sketch
* The proof starts by assuming the given conditions about the functions `f` and `g` and the sets `s` and `t`.
* It uses the `CARD_IMAGE_INJ_EQ` theorem, which states that if there exists an injective function from one set to another, then the cardinality of the first set is less than or equal to the cardinality of the second set.
* The proof then uses the `EXISTS_TAC` tactic to introduce the function `g` as a witness to the existence of an inverse function to `f`.
* The `ASM_MESON_TAC` tactic is used to discharge the remaining subgoals, which involves using the assumptions about `f` and `g` to prove the equality of the cardinalities of `s` and `t`.

### Mathematical insight
This theorem provides a way to prove that two finite sets have the same cardinality by exhibiting a bijection between them. The conditions on the functions `f` and `g` ensure that they are inverses of each other, and the theorem uses this to conclude that the sets `s` and `t` have the same cardinality.

### Dependencies
* Theorems:
	+ `CARD_IMAGE_INJ_EQ`
* Definitions:
	+ `FINITE`
	+ `CARD`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `EXISTS_TAC` and `ASM_MESON_TAC` tactics are translated correctly. The `EXISTS_TAC` tactic introduces a witness to the existence of an inverse function, and the `ASM_MESON_TAC` tactic uses the assumptions about the functions to prove the equality of the cardinalities. The `MATCH_MP_TAC` tactic may also need to be translated, as it is used to apply the `CARD_IMAGE_INJ_EQ` theorem. Additionally, the definitions of `FINITE` and `CARD` may need to be ported as well.

---

## index

### Name of formal statement
index

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let index n = if n = 0 then 0 else if ODD n then 0 else SUC(index(n DIV 2))
```

### Informal statement
The function `index` is defined as follows: for any number `n`, `index(n)` is `0` if `n` equals `0`, or if `n` is odd, otherwise `index(n)` is the successor of `index(n DIV 2)`, where `DIV` denotes integer division.

### Informal sketch
* The definition of `index` is recursive, with a base case for when `n` is `0` or odd.
* For even `n`, the function calls itself with the argument `n DIV 2`, effectively reducing the problem size by half.
* The use of `SUC` (successor) indicates that the result of the recursive call is incremented by 1 when `n` is even and not zero.
* This process repeats until `n` is either `0` or odd, at which point the recursion stops.

### Mathematical insight
The `index` function appears to be related to the decomposition of a number into a power of 2 multiplied by an odd number, as hinted in the comment. This is a common technique in number theory and can be useful in various mathematical proofs and constructions.

### Dependencies
* `ODD`
* `SUC`
* `DIV`

### Porting notes
When porting this definition to another proof assistant, note that the recursive nature of `index` and the use of `SUC` for incrementing may require special handling, depending on the target system's support for recursive functions and successor functions. Additionally, the `DIV` operation may need to be explicitly defined or imported, as its behavior can vary between systems.

---

## oddpart

### Name of formal statement
oddpart

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let oddpart = define
 `oddpart n = if n = 0 then 0 else if ODD n then n else oddpart(n DIV 2)`
```

### Informal statement
The function `oddpart` takes an integer `n` and returns an integer. If `n` is 0, it returns 0. Otherwise, if `n` is odd, it returns `n`; if `n` is even, it recursively calls `oddpart` on `n` divided by 2.

### Informal sketch
* The definition of `oddpart` is recursive, relying on the parity of the input `n`.
* The base case is when `n` equals 0, at which point the function returns 0.
* For non-zero `n`, the function checks if `n` is odd using the `ODD` predicate.
* If `n` is odd, the function returns `n` directly.
* If `n` is even, the function recursively applies itself to `n` divided by 2 (`n DIV 2`), effectively stripping away the least significant bit until an odd number is found or the base case is reached.

### Mathematical insight
The `oddpart` function appears to extract the odd part of a given integer, essentially removing all factors of 2. This is a useful operation in number theory and can be applied in various contexts, such as analyzing the properties of integers based on their prime factorization.

### Dependencies
* `ODD`
* Integer division (`DIV`)

### Porting notes
When translating this definition into another proof assistant, pay attention to how recursive functions and integer division are handled. Ensure that the target system supports recursive definitions and has an equivalent `ODD` predicate or a way to check for oddness. Additionally, consider how the system treats integer division, as the behavior of `DIV` might differ slightly between systems, particularly regarding the treatment of negative numbers.

---

## INDEX_ODDPART_WORK

### Name of formal statement
INDEX_ODDPART_WORK

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INDEX_ODDPART_WORK = prove
 (`!n. n = 2 EXP (index n) * oddpart n /\ (ODD(oddpart n) <=> ~(n = 0))`,
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[index; oddpart] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH; MULT_CLAUSES] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_ODD]) THEN
  SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; EXP; GSYM MULT_ASSOC;
           ARITH; ARITH_RULE `(2 * x) DIV 2 = x`; EQ_MULT_LCANCEL] THEN
  ASM_MESON_TAC[ARITH_RULE `~(n = 0) /\ n = 2 * m ==> m < n /\ ~(m = 0)`])
```

### Informal statement
For all natural numbers `n`, it holds that `n` is equal to `2` raised to the power of the `index` of `n`, multiplied by the `oddpart` of `n`. Furthermore, the `oddpart` of `n` is odd if and only if `n` is not equal to `0`.

### Informal sketch
* The proof begins by considering the case where `n` is `0` and the case where `n` is not `0`.
* When `n` is not `0`, the proof uses the `MATCH_MP_TAC` and `GEN_TAC` to set up the induction.
* It then applies `ONCE_REWRITE_TAC` with `index` and `oddpart` to rewrite the expressions.
* The `ASM_CASES_TAC` and `COND_CASES_TAC` are used to handle different cases based on the properties of `n`.
* The `SIMP_TAC` and `ASM_MESON_TAC` are used to simplify and derive the final conclusion, utilizing various arithmetic properties and rules, including `EVEN_EXISTS`, `LEFT_IMP_EXISTS_THM`, and `ARITH_RULE`.
* Key steps involve recognizing that `n` can be represented as `2` raised to some power multiplied by its `oddpart`, and leveraging properties of even and odd numbers to establish the equivalence regarding the oddness of `oddpart(n)`.

### Mathematical insight
This theorem provides a fundamental property relating a number `n` with its `index` and `oddpart`. The `index` of `n` refers to the highest power of `2` that divides `n`, and the `oddpart` of `n` is the result of dividing `n` by the highest power of `2` that divides it. This theorem is crucial in number theory, especially in proofs involving divisibility, parity, and the representation of numbers in terms of their prime factors.

### Dependencies
* Theorems:
  + `num_WF`
  + `EVEN_EXISTS`
  + `LEFT_IMP_EXISTS_THM`
  + `NOT_ODD`
  + `ARITH_RULE`
* Definitions:
  + `index`
  + `oddpart`
  + `ODD`
  + `EXP`
* Axioms and Rules:
  + `MATCH_MP_TAC`
  + `GEN_TAC`
  + `DISCH_TAC`
  + `ONCE_REWRITE_TAC`
  + `ASM_CASES_TAC`
  + `COND_CASES_TAC`
  + `SIMP_TAC`
  + `ASM_MESON_TAC`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles arithmetic, especially the representation of `index` and `oddpart` functions, and how they manage case splits and induction. The `MATCH_MP_TAC` and `GEN_TAC` might have direct counterparts, but tactics like `SIMP_TAC` and `ASM_MESON_TAC` may require careful translation to leverage the target system's simplification and proof search capabilities. Additionally, ensure that the arithmetic properties and rules used, such as `EVEN_EXISTS` and `ARITH_RULE`, are appropriately defined or imported in the target system.

---

## INDEX_ODDPART_DECOMPOSITION

### Name of formal statement
INDEX_ODDPART_DECOMPOSITION

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INDEX_ODDPART_DECOMPOSITION = prove
 (`!n. n = 2 EXP (index n) * oddpart n`,
  MESON_TAC[INDEX_ODDPART_WORK])
```

### Informal statement
For all natural numbers n, n is equal to 2 raised to the power of the index of n, multiplied by the odd part of n.

### Informal sketch
* The proof involves showing that any number `n` can be decomposed into a product of two components: `2` raised to some power (related to the `index` of `n`), and the `oddpart` of `n`.
* The `INDEX_ODDPART_WORK` theorem is used as a basis for the proof, likely providing a key insight or lemma about the relationship between `index`, `oddpart`, and the structure of numbers.
* The `MESON_TAC` tactic is employed to construct the proof, indicating that the proof involves a combination of basic logical rules and possibly some automated reasoning steps to derive the conclusion.

### Mathematical insight
This theorem provides a fundamental decomposition of numbers into their odd part and a power of 2, which is significant in number theory and can be crucial in various proofs involving divisibility, primality, and properties of integers.

### Dependencies
* `INDEX_ODDPART_WORK`

### Porting notes
When translating this theorem into another proof assistant, ensure that the `index` and `oddpart` functions are correctly defined and that their properties are established. The `MESON_TAC` tactic may not have a direct equivalent, so the proof strategy might need to be adapted to fit the target system's automation and tactical style.

---

## ODD_ODDPART

### Name of formal statement
ODD_ODDPART

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ODD_ODDPART = prove
 (`!n. ODD(oddpart n) <=> ~(n = 0)`,
  MESON_TAC[INDEX_ODDPART_WORK])
```

### Informal statement
For all natural numbers n, the `oddpart` of n is odd if and only if n is not equal to 0.

### Informal sketch
* The statement involves proving an equivalence between two conditions: `ODD(oddpart n)` and `~(n = 0)`.
* The proof likely starts with the assumption that `n` is not equal to 0 and shows that `oddpart n` is odd, utilizing properties of the `oddpart` function.
* Conversely, it assumes `oddpart n` is odd and derives that `n` cannot be 0, possibly leveraging the definition of `oddpart` and properties of odd numbers.
* The `MESON_TAC` tactic suggests that the proof involves a combination of basic logical rules and possibly some form of case analysis or simplification, as facilitated by `INDEX_ODDPART_WORK`.

### Mathematical insight
This theorem provides insight into the relationship between a number's `oddpart` and its being non-zero. The `oddpart` function typically returns the odd part of a number, which is crucial in various arithmetic and number-theoretic contexts. Understanding this relationship is essential for further reasoning about odd numbers and their properties in formal developments.

### Dependencies
* `ODD`
* `oddpart`
* `INDEX_ODDPART_WORK`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how the target system handles quantifiers, especially the universal quantification over natural numbers `n`. Additionally, ensure that the `oddpart` function and the `ODD` predicate are defined and behave similarly in the target system. The `MESON_TAC` tactic's role in simplifying or case-analyzing the proof should be replicated using the target system's tactics or automation mechanisms.

---

## ODDPART_LE

### Name of formal statement
ODDPART_LE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ODDPART_LE = prove
 (`!n. oddpart n <= n`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [INDEX_ODDPART_DECOMPOSITION] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * x <= y * x ==> x <= y * x`) THEN
  REWRITE_TAC[LE_MULT_RCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH])
```

### Informal statement
For all natural numbers n, the odd part of n is less than or equal to n.

### Informal sketch
* The proof begins by generalizing the statement for all n.
* It then applies a rewrite rule using `INDEX_ODDPART_DECOMPOSITION` to decompose the odd part of n.
* The `MATCH_MP_TAC` tactic is used with an arithmetic rule to establish a relationship between the odd part and n.
* The proof then simplifies the inequality using `LE_MULT_RCANCEL` and an arithmetic rule regarding the relationship between 1 and n.
* Finally, the `REWRITE_TAC` is applied with `EXP_EQ_0` and arithmetic rules to conclude the proof.

### Mathematical insight
This theorem provides a fundamental property of the odd part function, establishing a bound on its output relative to its input. This is crucial in number theory and arithmetic reasoning, as it allows for the comparison and manipulation of numbers based on their odd components.

### Dependencies
* `INDEX_ODDPART_DECOMPOSITION`
* `ARITH_RULE`
* `LE_MULT_RCANCEL`
* `EXP_EQ_0`

### Porting notes
When translating this theorem into another proof assistant, special attention should be given to the handling of arithmetic rules and the decomposition of the odd part of a number. The `GEN_REWRITE_TAC` and `MATCH_MP_TAC` tactics may have direct counterparts in other systems, but their application and the specific rules used (`INDEX_ODDPART_DECOMPOSITION`, `LE_MULT_RCANCEL`, `EXP_EQ_0`) will need to be carefully translated to ensure the proof structure remains valid.

---

## INDEX_ODDPART_UNIQUE

### Name of formal statement
INDEX_ODDPART_UNIQUE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INDEX_ODDPART_UNIQUE = prove
 (`!i m i' m'. ODD m /\ ODD m'
               ==> (2 EXP i * m = 2 EXP i' * m' <=> i = i' /\ m = m')`,
  REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NUMPAIR; NUMPAIR_INJ] THEN
  ARITH_TAC)
```

### Informal statement
For all integers `i`, `m`, `i'`, and `m'`, if `m` is odd and `m'` is odd, then `2` raised to the power of `i` times `m` equals `2` raised to the power of `i'` times `m'` if and only if `i` equals `i'` and `m` equals `m'`.

### Informal sketch
* Start by assuming `m` and `m'` are odd.
* Use the definition of oddness to rewrite `m` and `m'` in terms of their existence as `2k + 1` for some integer `k`.
* Apply `REWRITE_TAC` with `ODD_EXISTS` and `ADD1` to transform the expressions involving `m` and `m'`.
* Apply `STRIP_TAC` repeatedly to simplify the equation and focus on the exponents and the odd components separately.
* Utilize `ASM_REWRITE_TAC` with `GSYM NUMPAIR` and `NUMPAIR_INJ` to handle the equality of pairs and injectivity, which helps in comparing the exponents `i` and `i'` and the odd numbers `m` and `m'`.
* Finally, apply `ARITH_TAC` to conclude the proof by simplifying any remaining arithmetic expressions and establishing the equivalence.

### Mathematical insight
This theorem provides a unique representation of numbers in terms of their odd part and the power of 2 they are multiplied by. It's essential for establishing a canonical form for integers, which is crucial in various mathematical proofs, especially those involving divisibility, prime factorization, and properties of integers under multiplication.

### Dependencies
* Theorems:
  - `ODD_EXISTS`
  - `ADD1`
  - `GSYM NUMPAIR`
  - `NUMPAIR_INJ`
* Definitions:
  - `ODD`
  - `EXP`

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how these systems handle arithmetic, the representation of odd numbers, and the specifics of their tactic languages. For instance, the direct translation of `REWRITE_TAC`, `STRIP_TAC`, `ASM_REWRITE_TAC`, and `ARITH_TAC` might require understanding the equivalent tactics or built-in decision procedures in the target system. Additionally, ensure that the target system's library includes or can easily express the required theorems and definitions, such as `ODD_EXISTS` and `NUMPAIR_INJ`.

---

## INDEX_ODDPART

### Name of formal statement
INDEX_ODDPART

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let INDEX_ODDPART = prove
 (`!i m. ODD m ==> index(2 EXP i * m) = i /\ oddpart(2 EXP i * m) = m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `m:num`; `index(2 EXP i * m)`; `oddpart(2 EXP i * m)`]
        INDEX_ODDPART_UNIQUE) THEN
  REWRITE_TAC[GSYM INDEX_ODDPART_DECOMPOSITION; ODD_ODDPART] THEN
  ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH] THEN ASM_MESON_TAC[ODD])
```

### Informal statement
For all natural numbers `i` and `m`, if `m` is odd, then the index of `2` raised to the power of `i` times `m` equals `i`, and the odd part of `2` raised to the power of `i` times `m` equals `m`.

### Informal sketch
* The proof starts by assuming `m` is odd and aims to prove two equalities: `index(2 EXP i * m) = i` and `oddpart(2 EXP i * m) = m`.
* It utilizes the `INDEX_ODDPART_UNIQUE` theorem with specific instantiations for `i`, `m`, `index(2 EXP i * m)`, and `oddpart(2 EXP i * m)`.
* The proof involves rewriting using `INDEX_ODDPART_DECOMPOSITION` and `ODD_ODDPART` to simplify expressions.
* It applies `MULT_EQ_0`, `EXP_EQ_0`, and `ARITH` to handle arithmetic properties and then uses `ASM_MESON_TAC` with `ODD` to conclude the proof.

### Mathematical insight
This theorem provides a fundamental property about the decomposition of numbers into their index and odd part when multiplied by powers of 2. It's crucial for establishing relationships between numbers and their representations, especially in contexts where parity and powers of 2 are significant.

### Dependencies
* Theorems:
  - `INDEX_ODDPART_UNIQUE`
  - `ODD_ODDPART`
  - `MULT_EQ_0`
  - `EXP_EQ_0`
  - `ODD`
* Definitions:
  - `index`
  - `oddpart`
  - `EXP`

### Porting notes
When translating this theorem into another proof assistant, pay attention to how each system handles quantifiers, arithmetic, and the specific definitions of `index` and `oddpart`. The use of `REPEAT GEN_TAC`, `STRIP_TAC`, and `ASM_MESON_TAC` might need to be adapted based on the target system's tactic language and automation capabilities.

---

## odd_of_distinct

### Name of formal statement
odd_of_distinct

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let odd_of_distinct = new_definition
 `odd_of_distinct p =
    \i. if ODD i then nsum {j | p(2 EXP j * i) = 1} (\j. 2 EXP j) else 0`;;
```

### Informal statement
The function `odd_of_distinct` takes a predicate `p` and returns a function that, for any integer `i`, if `i` is odd, computes the sum of `2` raised to the power of `j` for all `j` such that `p` applied to `2` raised to the power of `j` times `i` equals `1`; otherwise, it returns `0`.

### Informal sketch
* The definition involves a conditional check on the parity of `i` using the `ODD` predicate.
* If `i` is odd, it calculates a sum using `nsum` over a set of `j` values that satisfy a specific condition involving the predicate `p`.
* The condition `p(2 EXP j * i) = 1` filters the `j` values considered in the sum.
* For each qualifying `j`, the summand is `2 EXP j`.
* If `i` is not odd (i.e., it is even), the function returns `0`.

### Mathematical insight
This definition seems to be related to partitions, particularly in the context of "odd only" and "all distinct" partitions, as hinted by the surrounding context in the HOL Light code. The `odd_of_distinct` function appears to play a role in mapping or characterizing such partitions, possibly in relation to their properties or constructions.

### Dependencies
#### Definitions
* `ODD`
* `nsum`
* `EXP`
#### Theorems and Lemmas
* None explicitly mentioned in this definition, but the context suggests dependencies on partition-related theorems or definitions, such as `partitions`, `PARTITIONS_BOUND`, `FINITE_PARTITIONS_LEMMA`, `FINITE_PARTITIONS`, and `FINITE_SUBSET_PARTITIONS`.

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay close attention to how each system handles conditional expressions, summations (`nsum`), and exponentiation (`EXP`). Additionally, ensure that the `ODD` predicate and any other used predicates or functions are appropriately defined or imported in the target system. The use of `let` for function definition and lambda abstraction (`\i. ...`) should be translated according to the target system's syntax for defining functions.

---

## distinct_of_odd

### Name of formal statement
distinct_of_odd

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let distinct_of_odd = new_definition
 `distinct_of_odd p = \i. if (index i) IN bitset (p(oddpart i)) then 1 else 0`;;
```

### Informal statement
The function `distinct_of_odd` takes a predicate `p` and returns a function that, given an index `i`, checks if the index `i` is in the bitset resulting from applying `p` to the odd part of `i`. If it is, the function returns 1; otherwise, it returns 0.

### Informal sketch
* The definition of `distinct_of_odd` involves a conditional expression that depends on the membership of `index i` in a bitset.
* This bitset is constructed by applying the predicate `p` to the `oddpart` of `i` and then converting the result to a bitset.
* The function uses a lambda abstraction to define a new function that takes `i` as an argument and evaluates the conditional expression.

### Mathematical insight
The `distinct_of_odd` function appears to be related to the concept of checking whether a particular index satisfies a certain property, as defined by the predicate `p`, when applied to the odd part of the index. This could be useful in contexts where bit-level operations or predicate logic are relevant.

### Dependencies
* `index`
* `bitset`
* `oddpart`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles lambda abstractions, conditional expressions, and bitset operations. For example, in Lean, you might use the `if` expression and the `finset` data structure, while in Coq, you could utilize the `if` expression and the `Ensemble` module for set operations. In Isabelle, the `if` expression and the `Code_Bitset` module might be relevant. Ensure that the ported definition preserves the original logic and types.

---

## ODD_ODD_OF_DISTINCT

### Name of formal statement
ODD_ODD_OF_DISTINCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ODD_ODD_OF_DISTINCT = prove
 (`!p i. ~(odd_of_distinct p i = 0) ==> ODD i`,
  REWRITE_TAC[odd_of_distinct] THEN MESON_TAC[]);;
```

### Informal statement
For all predicates `p` and all `i`, if the `odd_of_distinct` of `p` and `i` is not equal to 0, then `i` is odd.

### Informal sketch
* The proof starts by assuming that `odd_of_distinct p i` is not equal to 0 for some predicate `p` and some `i`.
* It then applies the definition of `odd_of_distinct` using `REWRITE_TAC`.
* The `MESON_TAC` tactic is used to derive the conclusion that `i` is odd, leveraging the properties of `odd_of_distinct` and the assumption that its result is not 0.

### Mathematical insight
This theorem establishes a relationship between the `odd_of_distinct` function and the property of being odd. It suggests that if `odd_of_distinct` returns a non-zero value for a given `i`, then `i` itself must be odd. This is likely a foundational result in a theory that involves parity properties and distinctness, highlighting the interplay between these concepts.

### Dependencies
* `odd_of_distinct`
* `ODD`

### Porting notes
When translating this theorem into another proof assistant, pay attention to how the `REWRITE_TAC` and `MESON_TAC` tactics are handled, as different systems may have analogous but distinct tactics for rewriting and deriving conclusions. Additionally, ensure that the `odd_of_distinct` function and the `ODD` predicate are defined and available in the target system, as their properties are crucial for the proof.

---

## DISTINCT_DISTINCT_OF_ODD

### Name of formal statement
DISTINCT_DISTINCT_OF_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DISTINCT_DISTINCT_OF_ODD = prove
 (`!p i. distinct_of_odd p i <= 1`,
  REWRITE_TAC[distinct_of_odd] THEN ARITH_TAC);;
```

### Informal statement
For all predicates `p` and all integers `i`, the number of distinct odd elements of `p` at `i` is less than or equal to 1.

### Informal sketch
* The proof starts by assuming an arbitrary predicate `p` and an integer `i`.
* It then applies the definition of `distinct_of_odd` to rewrite the statement.
* The `ARITH_TAC` tactic is used to perform arithmetic reasoning, which simplifies the statement and leads to the conclusion that the number of distinct odd elements of `p` at `i` is less than or equal to 1.
* The key idea is to use the definition of `distinct_of_odd` to reduce the problem to a simple arithmetic inequality.

### Mathematical insight
This theorem provides a bound on the number of distinct odd elements of a predicate at a given index. The theorem is important because it provides a simple and useful property of the `distinct_of_odd` function, which can be used in further reasoning about predicates and their properties.

### Dependencies
* `distinct_of_odd`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the definition of `distinct_of_odd` is correctly translated. Additionally, the arithmetic reasoning performed by `ARITH_TAC` may need to be replicated using the target system's arithmetic tactics.

---

## SUPPORT_ODD_OF_DISTINCT

### Name of formal statement
SUPPORT_ODD_OF_DISTINCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUPPORT_ODD_OF_DISTINCT = prove
 (`!p. (!i. ~(p i = 0) ==> i <= n)
       ==> !i. ~(odd_of_distinct p i = 0) ==> 1 <= i /\ i <= n`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[ODD; ARITH_RULE `1 <= i <=> ~(i = 0)`; ODD_ODD_OF_DISTINCT];
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))] THEN
  REWRITE_TAC[odd_of_distinct] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[LE_0] THEN
  SUBGOAL_THEN `FINITE {j | p (2 EXP j * i) = 1}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET] THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_ELIM_THM; LE_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP j * i` THEN
    ASM_SIMP_TAC[ARITH_EQ] THEN
    MATCH_MP_TAC(ARITH_RULE `j < ej /\ ej * 1 <= ej * i ==> j <= ej * i`) THEN
    REWRITE_TAC[LT_POW2_REFL; LE_MULT_LCANCEL; EXP_EQ_0; ARITH] THEN
    UNDISCH_TAC `~(i = 0)` THEN ARITH_TAC;
    SIMP_TAC[ARITH_RULE `~((if p then x else 0) = 0) <=> p /\ ~(x = 0)`] THEN
    ASM_SIMP_TAC[NSUM_EQ_0_IFF; EXP_EQ_0; ARITH] THEN
    REWRITE_TAC[NOT_FORALL_THM; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `j:num`)) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP j * i` THEN
    ASM_SIMP_TAC[ARITH; ARITH_RULE `i <= j * i <=> 1 * i <= j * i`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL; ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH]])
```

### Informal statement
For all predicates `p` and all natural numbers `n`, if for all `i`, `p(i)` is not equal to `0` implies `i` is less than or equal to `n`, then for all `i`, if `odd_of_distinct(p, i)` is not equal to `0`, then `1` is less than or equal to `i` and `i` is less than or equal to `n`.

### Informal sketch
* The proof begins by assuming the premise that for all `i`, `p(i)` not equal to `0` implies `i` is less than or equal to `n`.
* It then assumes that `odd_of_distinct(p, i)` is not equal to `0` and aims to prove that `1` is less than or equal to `i` and `i` is less than or equal to `n`.
* The proof proceeds by cases, first considering when `i` equals `0` and then when `i` is not equal to `0`.
* For the case when `i` is not `0`, it uses the definition of `odd_of_distinct` and properties of arithmetic to derive the required inequalities.
* Key steps involve using `FINITE` to establish a subset relationship and applying `MATCH_MP_TAC` with specific arithmetic rules to derive the inequalities.
* The use of `SUBGOAL_THEN` and `ASSUME_TAC` helps in managing the assumptions and subgoals during the proof.
* The `ASM_MESON_TAC` and `ASM_SIMP_TAC` tactics are used to apply specific theorems and simplify expressions, showcasing the interplay between logical deductions and arithmetic properties.

### Mathematical insight
This theorem provides a relationship between the support of a predicate `p` and the `odd_of_distinct` function applied to `p` and some index `i`. The `odd_of_distinct` function seems to count odd occurrences of `p` being true for certain values related to `i`. The theorem ensures that if `odd_of_distinct(p, i)` is not zero, then `i` falls within a certain range defined by the support of `p`. This has implications for how `p` and `odd_of_distinct` interact, particularly in contexts where the support of `p` is bounded.

### Dependencies
* Theorems:
  - `ODD`
  - `ARITH_RULE`
  - `ODD_ODD_OF_DISTINCT`
  - `FINITE_NUMSEG`
  - `IN_NUMSEG`
  - `NSUM_EQ_0_IFF`
  - `NOT_FORALL_THM`
  - `IN_ELIM_THM`
* Definitions:
  - `odd_of_distinct`
* Tactics and rules:
  - `REPEAT`
  - `STRIP_TAC`
  - `ASM_MESON_TAC`
  - `MATCH_MP_TAC`
  - `SUBGOAL_THEN`
  - `ASSUME_TAC`
  - `ASM_SIMP_TAC`
  - `X_GEN_TAC`
  - `X_CHOOSE_TAC`

---

## SUPPORT_DISTINCT_OF_ODD

### Name of formal statement
SUPPORT_DISTINCT_OF_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUPPORT_DISTINCT_OF_ODD = prove
 (`!p. (!i. p(i) * i <= n) /\
       (!i. ~(p i = 0) ==> ODD i)
       ==> !i. ~(distinct_of_odd p i = 0) ==> 1 <= i /\ i <= n`,
  REWRITE_TAC[distinct_of_odd] THEN
  REWRITE_TAC[ARITH_RULE `(if a then 1 else 0) = 0 <=> ~a`] THEN
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i <=> ~(i = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `index 0 IN bitset (p (oddpart 0))` THEN
    REWRITE_TAC[index; oddpart; ARITH] THEN
    UNDISCH_THEN `!i. ~(p i = 0) ==> ODD i` (MP_TAC o SPEC `0`) THEN
    SIMP_TAC[ARITH; BITSET_0; NOT_IN_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP BITSET_BOUND_LEMMA) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p(oddpart i) * oddpart i` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [INDEX_ODDPART_DECOMPOSITION] THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL])
```

### Informal statement
For all predicates `p`, if for all `i`, `p(i)` is true and `i` is less than or equal to `n`, and for all `i`, if `p(i)` is not equal to `0`, then `i` is odd, it follows that for all `i`, if `distinct_of_odd p i` is not equal to `0`, then `i` is between `1` and `n` (inclusive).

### Informal sketch
* The proof starts by assuming the premises: for all `i`, `p(i)` and `i` is less than or equal to `n`, and for all `i`, if `p(i)` is not `0`, then `i` is odd.
* It then uses `REWRITE_TAC` to expand the definition of `distinct_of_odd` and applies an arithmetic rule to simplify the condition `(if a then 1 else 0) = 0 <=> ~a`.
* The proof proceeds by generalizing over `i` and stripping the implications to arrive at the conclusion that `1 <= i` and `i <= n` when `distinct_of_odd p i` is not `0`.
* Key steps involve using `BITSET_BOUND_LEMMA`, `LE_TRANS`, and `INDEX_ODDPART_DECOMPOSITION` to establish the bounds of `i`.
* The proof also involves case analysis and the application of various arithmetic and set properties.

### Mathematical insight
This theorem establishes a relationship between a predicate `p`, its support, and the parity of its indices, providing a bound on the indices `i` for which `distinct_of_odd p i` is not zero. This is crucial in contexts where the parity of indices and the support of predicates are significant, such as in combinatorial or number-theoretic arguments.

### Dependencies
#### Theorems
* `BITSET_BOUND_LEMMA`
* `LE_TRANS`
#### Definitions
* `distinct_of_odd`
* `oddpart`
* `index`
* `bitset`
#### Arithmetic Rules
* `ARITH_RULE `(if a then 1 else 0) = 0 <=> ~a` 
* `ARITH_RULE `1 <= i <=> ~(i = 0)` 
* `LE_MULT_RCANCEL` 

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay special attention to how each system handles arithmetic, set operations, and predicate logic. The `REWRITE_TAC` and `MATCH_MP_TAC` tactics may have direct analogs, but the specific rules and lemmas applied (`BITSET_BOUND_LEMMA`, `LE_TRANS`, etc.) will need to be identified or proved within the target system. Additionally, consider the differences in how binders and quantifiers are handled, as well as the level of automation provided by the proof assistant.

---

## ODD_OF_DISTINCT_OF_ODD

### Name of formal statement
ODD_OF_DISTINCT_OF_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ODD_OF_DISTINCT_OF_ODD = prove
 (`!p. (!i. ~(p(i) = 0) ==> ODD i)
       ==> odd_of_distinct (distinct_of_odd p) = p`,
  REWRITE_TAC[IN_ELIM_THM; odd_of_distinct; distinct_of_odd] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_SIMP_TAC[INDEX_ODDPART] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM BINARYSUM_BITSET] THEN
  REWRITE_TAC[binarysum] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ])
```

### Informal statement
For all `p`, if for all `i`, `p(i)` is not equal to 0 implies `i` is odd, then `odd_of_distinct` of `distinct_of_odd` of `p` is equal to `p`.

### Informal sketch
* The proof starts by assuming a function `p` such that for all `i`, if `p(i)` is not 0, then `i` is odd.
* It then applies several simplification and transformation steps using `REWRITE_TAC` with various theorems (`IN_ELIM_THM`, `odd_of_distinct`, `distinct_of_odd`) to manipulate the expression `odd_of_distinct (distinct_of_odd p)`.
* The proof proceeds by case analysis using `COND_CASES_TAC`, considering the cases where the condition holds and where it does not, and applying `ASM_MESON_TAC` and `ASM_SIMP_TAC` with specific theorems (`INDEX_ODDPART`) to simplify the expressions.
* Further simplifications are made using `GEN_REWRITE_TAC` and `REWRITE_TAC` with theorems like `BINARYSUM_BITSET` and `binarysum`, and applying `AP_THM_TAC` and `AP_TERM_TAC` to transform the expressions.
* The proof concludes by showing the equality `odd_of_distinct (distinct_of_odd p) = p` through a series of rewriting and case analysis steps, utilizing theorems like `EXTENSION` and `IN_ELIM_THM`, and finally applying `ASM_REWRITE_TAC` with `ARITH_EQ` to establish the arithmetic equality.

### Mathematical insight
This theorem provides a key property relating the `odd_of_distinct` and `distinct_of_odd` functions, specifically under the condition that the input function `p` maps non-zero values to odd numbers. It shows that applying `distinct_of_odd` to `p` and then `odd_of_distinct` to the result yields the original function `p`, under the given condition. This kind of result can be crucial in formal developments involving properties of odd and distinct functions, particularly in contexts where the preservation of such properties under function composition is important.

### Dependencies
- Theorems:
  - `IN_ELIM_THM`
  - `odd_of_distinct`
  - `distinct_of_odd`
  - `FUN_EQ_THM`
  - `INDEX_ODDPART`
  - `BINARYSUM_BITSET`
  - `binarysum`
  - `EXTENSION`
  - `IN_ELIM_THM`
  - `ARITH_EQ`
- Definitions:
  - `odd_of_distinct`
  - `distinct_of_odd`

---

## DISTINCT_OF_ODD_OF_DISTINCT

### Name of formal statement
DISTINCT_OF_ODD_OF_DISTINCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DISTINCT_OF_ODD_OF_DISTINCT = prove
 (`!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\ (!i. p(i) <= 1)
       ==> distinct_of_odd (odd_of_distinct p) = p`,
  REWRITE_TAC[distinct_of_odd; odd_of_distinct; IN_ELIM_THM] THEN
  REWRITE_TAC[partitions; ODD_ODDPART] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[BITSET_0; NOT_IN_EMPTY] THENL
   [ASM_MESON_TAC[ARITH_RULE `~(1 <= 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {j | p (2 EXP j * oddpart i) = 1}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[LE_0] THEN
    MATCH_MP_TAC(ARITH_RULE `!x. y <= x /\ 1 <= x /\ x <= n ==> y <= n`) THEN
    EXISTS_TAC `2 EXP j * oddpart i` THEN ASM_SIMP_TAC[ARITH] THEN
    MATCH_MP_TAC(ARITH_RULE `j < ej /\ 1 * ej <= i * ej ==> j <= ej * i`) THEN
    REWRITE_TAC[LT_POW2_REFL; LE_MULT_RCANCEL] THEN
    ASM_MESON_TAC[ODD_ODDPART; ODD; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    ASM_SIMP_TAC[BITSET_BINARYSUM; GSYM binarysum; IN_ELIM_THM] THEN
    REWRITE_TAC[GSYM INDEX_ODDPART_DECOMPOSITION] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    ASM_MESON_TAC[ARITH_RULE `i <= 1 ==> i = 0 \/ i = 1`]])
```

### Informal statement
For all `p`, if for all `i`, `p(i)` is not equal to `0` implies `1` is less than or equal to `i` and `i` is less than or equal to `n`, and for all `i`, `p(i)` is less than or equal to `1`, then `distinct_of_odd` of `odd_of_distinct` of `p` is equal to `p`.

### Informal sketch
* The proof begins by assuming the given conditions on `p` and then applies `REWRITE_TAC` to expand `distinct_of_odd` and `odd_of_distinct`.
* It then proceeds with case analysis on `i = 0`, handling this base case separately.
* For non-zero `i`, it assumes the finiteness of the set of `j` such that `p(2^j * oddpart i) = 1` and proves this assumption by showing that this set is a subset of `0..n`.
* The proof then applies various arithmetic and logical manipulations to simplify the expression and ultimately show that `distinct_of_odd (odd_of_distinct p)` equals `p`.
* Key steps involve using `REWRITE_TAC` with various theorems, `ASM_CASES_TAC` for case analysis, and `SUBGOAL_THEN` to assume and prove the finiteness of a certain set.

### Mathematical insight
This theorem provides a relationship between the `distinct_of_odd` and `odd_of_distinct` functions, showing that their composition equals the identity function under certain conditions on `p`. This is important for understanding the properties and behavior of these functions, particularly in contexts where distinctness and oddness properties are crucial.

### Dependencies
#### Theorems
* `distinct_of_odd`
* `odd_of_distinct`
* `IN_ELIM_THM`
* `partitions`
* `ODD_ODDPART`
* `FINITE_SUBSET`
* `FINITE_NUMSEG`
* `IN_NUMSEG`
* `SUBSET`
* `IN_ELIM_THM`
* `BITSET_BINARYSUM`
* `binarysum`
* `INDEX_ODDPART_DECOMPOSITION`
* `ARITH_RULE` (for various arithmetic properties)

#### Definitions
* `distinct_of_odd`
* `odd_of_distinct`
* `partitions`
* `ODD_ODDPART`
* `BITSET_0`
* `NOT_IN_EMPTY`
* `FUN_EQ_THM`
* `BITSET_BINARYSUM`
* `binarysum`
* `INDEX_ODDPART_DECOMPOSITION`

---

## NSUM_DISTINCT_OF_ODD

### Name of formal statement
NSUM_DISTINCT_OF_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NSUM_DISTINCT_OF_ODD = prove
 (`!p. (!i. ~(p i = 0) ==> 1 <= i /\ i <= n) /\
       (!i. p(i) * i <= n) /\
       (!i. ~(p(i) = 0) ==> ODD i)
       ==> nsum(1..n) (\i. distinct_of_odd p i * i) =
           nsum(1..n) (\i. p i * i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[distinct_of_odd] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV)
   [GSYM BINARYSUM_BITSET] THEN
  REWRITE_TAC[binarysum] THEN REWRITE_TAC[GSYM NSUM_RMUL] THEN
  SIMP_TAC[NSUM_NSUM_PRODUCT; FINITE_BITSET; FINITE_NUMSEG] THEN
  CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM NSUM_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_ADD] THEN
  SUBGOAL_THEN
   `{x | x IN {i,j | i IN 1..n /\ j IN bitset(p i)} /\
         ~((\(i,j). 2 EXP j * i) x = 0)} =
    {i,j | i IN 1..n /\ j IN bitset(p i)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[IN_NUMSEG; EXP_EQ_0; MULT_EQ_0; ARITH] THEN
    MESON_TAC[ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN 1 .. n /\
         ~((if index x IN bitset (p (oddpart x)) then 1 else 0) * x = 0)} =
    {i | i IN 1..n /\ (index i) IN bitset (p(oddpart i))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; MULT_EQ_0] THEN
    REWRITE_TAC[IN_NUMSEG; ARITH_RULE `(if p then 1 else 0) = 0 <=> ~p`] THEN
    MESON_TAC[ARITH_RULE `~(1 <= 0)`];
    ALL_TAC] THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL THEN
  EXISTS_TAC `\(i,b). 2 EXP b * i` THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[ARITH_RULE
   `(if p then 1 else 0) * x * y = (if p then x * y else 0)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> a /\ b /\ (b ==> c)`] THEN
  SIMP_TAC[] THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
  SUBGOAL_THEN `!i j. j IN bitset(p i) ==> ODD i` ASSUME_TAC THENL
   [ASM_MESON_TAC[BITSET_0; NOT_IN_EMPTY]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`oddpart m`; `index m`] THEN
      ASM_REWRITE_TAC[GSYM INDEX_ODDPART_DECOMPOSITION] THEN
      ASM_MESON_TAC[ODDPART_LE; LE_TRANS; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                    ODD_ODDPART; ODD];
      ASM_MESON_TAC[INDEX_ODDPART_UNIQUE]];
    MAP_EVERY X_GEN_TAC [`m:num`; `i:num`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[INDEX_ODDPART]] THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
      REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH] THEN
      ASM_MESON_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`];
      ASM_MESON_TAC[BITSET_BOUND_LEMMA; LE_MULT_RCANCEL; LE_TRANS]]));;
```

### Informal statement
For all functions `p`, if for all `i`, `p(i)` is not equal to `0` implies `1` is less than or equal to `i` and `i` is less than or equal to `n`, and `p(i)` times `i` is less than or equal to `n`, and `p(i)` is not equal to `0` implies `i` is odd, then the sum from `1` to `n` of `distinct_of_odd p i` times `i` is equal to the sum from `1` to `n` of `p i` times `i`.

### Informal sketch
* The proof starts by assuming the given conditions on `p` and then applies various transformations to the sums involved.
* It uses `REPEAT STRIP_TAC` to strip the universal quantifier and `REWRITE_TAC[distinct_of_odd]` to expand the definition of `distinct_of_odd`.
* The proof then proceeds with a series of rewrites and simplifications, including the use of `GEN_REWRITE_TAC` to apply the `BINARYSUM_BITSET` theorem and `NSUM_RMUL` to rearrange the sums.
* It also uses `SUBGOAL_THEN` to prove two subsidiary equalities involving sets and bitsets, which are then used to simplify the main expression.
* The proof involves the application of `MATCH_MP_TAC NSUM_EQ_GENERAL` to establish the equality of the two sums, and `EXISTS_TAC` to introduce a witness for the existential quantifier.
* The `CONV_TAC` and `REWRITE_TAC` tactics are used extensively to simplify and rearrange terms.
* Key steps involve proving that certain sets are equal and using properties of arithmetic and bitsets to simplify expressions.

### Mathematical insight
This theorem relates to the properties of sums and bitsets, particularly in the context of odd numbers and distinct elements. The `distinct_of_odd` function seems to play a crucial role in ensuring that only distinct odd elements are counted in the sum. The theorem provides a way to equate two different expressions involving sums, which can be useful in simplifying complex arithmetic expressions.

### Dependencies
* Theorems:
  + `BINARYSUM_BITSET`
  + `NSUM_RMUL`
  + `NSUM_NSUM_PRODUCT`
  + `FINITE_BITSET`
  + `FINITE_NUMSEG`
  + `NSUM_EQ_GENERAL`
  + `BITSET_0`
  + `NOT_IN_EMPTY`
  + `ODDPART_LE`
  + `LE_TRANS`
  + `ARITH_RULE`
  + `ODDPART_UNIQUE`
  + `INDEX_ODDPART_UNIQUE`
  + `BITSET_BOUND_LEMMA`
  + `LE_MULT_RCANCEL`
* Definitions:
  + `distinct_of_odd`
  + `nsum`
  + `bitset`
  + `oddpart`
  + `index`

### Porting notes
When porting this theorem to another proof assistant, pay close attention to the handling of binders, sums, and bitsets, as these may differ between systems. The use of `GEN_REWRITE_TAC` and `SUBGOAL_THEN` may need to be adapted, and the `CONV_TAC` and `REWRITE_TAC` tactics may have different equivalents. Additionally, the `EXISTS_TAC` and `MATCH_MP_TAC` tactics may require different handling, depending on the target system's support for existential quantification and matching.

---

## DISTINCT_OF_ODD

### Name of formal statement
DISTINCT_OF_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DISTINCT_OF_ODD = prove
 (`!p. p IN {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}
       ==> (distinct_of_odd p) IN {p | p partitions n /\ !i. p(i) <= 1}`,
  GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM; partitions] THEN STRIP_TAC THEN
  REWRITE_TAC[DISTINCT_DISTINCT_OF_ODD] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUPPORT_DISTINCT_OF_ODD;
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC NSUM_DISTINCT_OF_ODD] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(p:num->num) i = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
  ASM_MESON_TAC[NSUM_BOUND_LEMMA])
```

### Informal statement
For all `p`, if `p` is a partition of `n` and for all `i`, if `p(i)` is not equal to `0`, then `i` is odd, then `distinct_of_odd p` is a partition of `n` and for all `i`, `p(i)` is less than or equal to `1`.

### Informal sketch
* The proof starts by assuming `p` is a partition of `n` with the given property regarding odd `i` when `p(i)` is not `0`.
* It then applies `GEN_TAC` to generalize the statement, followed by `REWRITE_TAC` to apply the `IN_ELIM_THM` and `partitions` theorems.
* The `STRIP_TAC` and `REWRITE_TAC` with `DISTINCT_DISTINCT_OF_ODD` are used to simplify and transform the statement.
* The proof proceeds by cases, using `CONJ_TAC` and `MATCH_MP_TAC` with `SUPPORT_DISTINCT_OF_ODD` and `NSUM_DISTINCT_OF_ODD`, to establish the properties of `distinct_of_odd p`.
* It then uses `ASM_REWRITE_TAC` and `X_GEN_TAC` to handle the case for `i`, and `ASM_CASES_TAC` to consider whether `(p:num->num) i = 0`.
* Finally, it applies `ASM_REWRITE_TAC` with `MULT_CLAUSES` and `LE_0`, and `ASM_MESON_TAC` with `NSUM_BOUND_LEMMA` to conclude the proof.

### Mathematical insight
This theorem is important because it establishes a relationship between a partition `p` of `n` with a specific property and the `distinct_of_odd` transformation of `p`. The property that `i` is odd when `p(i)` is not `0` is crucial, and the theorem shows that `distinct_of_odd p` preserves the partition property while ensuring that each `p(i)` is less than or equal to `1`. This has implications for the structure of partitions and the behavior of the `distinct_of_odd` function.

### Dependencies
* Theorems:
  + `IN_ELIM_THM`
  + `partitions`
  + `DISTINCT_DISTINCT_OF_ODD`
  + `SUPPORT_DISTINCT_OF_ODD`
  + `NSUM_DISTINCT_OF_ODD`
  + `NSUM_BOUND_LEMMA`
* Definitions:
  + `distinct_of_odd`
  + `partitions`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay close attention to the handling of quantifiers, the application of theorems like `IN_ELIM_THM`, and the use of tactics like `GEN_TAC` and `MATCH_MP_TAC`. The `distinct_of_odd` function and its properties, as well as the `partitions` definition, will need to be defined or imported appropriately in the target system. Additionally, the use of `ASM_REWRITE_TAC` and `ASM_MESON_TAC` may require careful handling of automatic rewriting and meson-style proof search in the target system.

---

## ODD_OF_DISTINCT

### Name of formal statement
ODD_OF_DISTINCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ODD_OF_DISTINCT = prove
 (`!p. p IN {p | p partitions n /\ !i. p(i) <= 1}
       ==> (odd_of_distinct p) IN
           {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}`,
  GEN_TAC THEN REWRITE_TAC[partitions; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[ODD_ODD_OF_DISTINCT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUPPORT_ODD_OF_DISTINCT]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum(1..n) (\i. distinct_of_odd(odd_of_distinct p) i * i)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_THM_TAC THEN
    ASM_MESON_TAC[DISTINCT_OF_ODD_OF_DISTINCT]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_DISTINCT_OF_ODD THEN
  REWRITE_TAC[ODD_ODD_OF_DISTINCT] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUPPORT_ODD_OF_DISTINCT]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[odd_of_distinct] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_0; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM NSUM_RMUL] THEN
  SUBGOAL_THEN `FINITE {i:num | p(i) = 1}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..n` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
    ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF]
   `(\j. j) o (\j. 2 EXP j * i)`)] THEN
  ASM_SIMP_TAC[GSYM NSUM_IMAGE; INDEX_ODDPART_UNIQUE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {i | p(i) = 1} (\j. j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum {i | p(i) = 1} (\j. p(j) * j)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC NSUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; MULT_CLAUSES];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
    ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`])
```

### Informal statement
For all `p` such that `p` is a partition of `n` and for all `i`, `p(i)` is less than or equal to 1, it holds that `odd_of_distinct p` is a partition of `n` and for all `i`, if `p(i)` is not equal to 0, then `i` is odd.

### Informal sketch
* The proof starts by assuming `p` is a partition of `n` with `p(i) <= 1` for all `i`.
* It then applies several rewrites and simplifications using `REWRITE_TAC` to transform the goal into a more manageable form.
* The `CONJ_TAC` is used to split the goal into two separate subgoals, which are then tackled individually.
* The `MATCH_MP_TAC EQ_TRANS` and `EXISTS_TAC` are used to introduce intermediate terms and apply transitivity of equality.
* The proof also employs `SUBGOAL_THEN` to assume the finiteness of a certain set and then discharge this assumption using `MATCH_MP_TAC FINITE_SUBSET`.
* Further rewrites and simplifications are applied, including `ASM_SIMP_TAC` and `MATCH_MP_TAC LE_TRANS`, to eventually reach the desired conclusion.
* Key `HOL Light` terms like `odd_of_distinct`, `distinct_of_odd`, and `partitions` play crucial roles in the proof.

### Mathematical insight
This theorem provides a relationship between a partition `p` of `n` and the `odd_of_distinct` function applied to `p`. The `odd_of_distinct` function seems to transform the partition `p` into another partition where only odd indices are considered, under the condition that `p(i)` is not zero. This transformation preserves certain properties of the original partition, specifically related to the parity of indices. The theorem is important for establishing connections between different representations or manipulations of partitions, potentially in the context of combinatorial or number-theoretic arguments.

### Dependencies
* Theorems:
	+ `partitions`
	+ `IN_ELIM_THM`
	+ `ODD_ODD_OF_DISTINCT`
	+ `SUPPORT_ODD_OF_DISTINCT`
	+ `DISTINCT_OF_ODD_OF_DISTINCT`
	+ `NSUM_DISTINCT_OF_ODD`
	+ `INDEX_ODDPART_UNIQUE`
* Definitions:
	+ `odd_of_distinct`
	+ `distinct_of_odd`
	+ `nsum`
	+ `FINITE_NUMSEG`
	+ `SUBSET`
	+ `IN_NUMSEG`
	+ `ARITH_RULE`
* Inductive rules or type definitions: None explicitly mentioned, but the use of `GEN_TAC`, `X_GEN_TAC`, and `CONJ_TAC` suggests reliance on basic logical and type rules in HOL Light. 

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, pay close attention to the handling of:
- Quantifiers and their scoping.
- The `SUBGOAL_THEN` and `ASSUME_TAC` tactics, which might be represented differently.
- The `MATCH_MP_TAC` and `EXISTS_TAC` tactics, which are used for applying theorems and introducing terms, respectively.
- The various rewrites and simplifications, ensuring that similar rules and tactics are applied correctly in the target system.
- The representation of sets and partitions, as well as the `odd_of_distinct` and `distinct_of_odd` functions, which might require specific definitions or libraries in the target system.

---

## EULER_PARTITION_THEOREM

### Name of formal statement
EULER_PARTITION_THEOREM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULER_PARTITION_THEOREM = prove
 (`FINITE {p | p partitions n /\ !i. p(i) <= 1} /\
   FINITE {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i} /\
   CARD {p | p partitions n /\ !i. p(i) <= 1} =
   CARD {p | p partitions n /\ !i. ~(p(i) = 0) ==> ODD i}`,
  MATCH_MP_TAC CARD_EQ_LEMMA THEN REWRITE_TAC[FINITE_SUBSET_PARTITIONS] THEN
  MAP_EVERY EXISTS_TAC [`odd_of_distinct`; `distinct_of_odd`] THEN
  REWRITE_TAC[ODD_OF_DISTINCT; DISTINCT_OF_ODD] THEN
  CONJ_TAC THEN X_GEN_TAC `p:num->num` THEN
  REWRITE_TAC[IN_ELIM_THM; partitions] THEN STRIP_TAC THENL
   [MATCH_MP_TAC DISTINCT_OF_ODD_OF_DISTINCT;
    MATCH_MP_TAC ODD_OF_DISTINCT_OF_ODD] THEN
  ASM_REWRITE_TAC[])
```

### Informal statement
The number of partitions of a number `n` into distinct parts is equal to the number of partitions of `n` into odd parts, and both sets of partitions are finite. Formally, for all `n`, the set of partitions `p` such that `p` partitions `n` and for all `i`, `p(i)` is less than or equal to 1, is finite, and the set of partitions `p` such that `p` partitions `n` and for all `i`, if `p(i)` is not equal to 0, then `i` is odd, is also finite. Furthermore, the cardinality of these two sets is equal.

### Informal sketch
* The proof involves showing that the number of partitions into distinct numbers is equal to the number of partitions into odd numbers.
* It uses the `CARD_EQ_LEMMA` to establish the equality of the cardinalities of the two sets of partitions.
* The `FINITE_SUBSET_PARTITIONS` theorem is used to show that both sets of partitions are finite.
* The `MAP_EVERY` and `EXISTS_TAC` tactics are used to introduce the `odd_of_distinct` and `distinct_of_odd` functions, which are used to establish the bijection between the two sets of partitions.
* The `CONJ_TAC` and `X_GEN_TAC` tactics are used to reason about the partitions and their properties.
* The `REWRITE_TAC` and `ASM_REWRITE_TAC` tactics are used to simplify and rearrange the terms in the proof.

### Mathematical insight
The Euler's partition theorem is a fundamental result in number theory, which states that the number of partitions of a number into distinct parts is equal to the number of partitions into odd parts. This theorem has important implications in many areas of mathematics, including combinatorics, algebra, and analysis. The formal proof of this theorem in HOL Light provides a rigorous and detailed account of the mathematical reasoning involved.

### Dependencies
* `CARD_EQ_LEMMA`
* `FINITE_SUBSET_PARTITIONS`
* `ODD_OF_DISTINCT`
* `DISTINCT_OF_ODD`
* `IN_ELIM_THM`
* `partitions`

### Porting notes
When porting this theorem to other proof assistants, such as Lean or Coq, care should be taken to ensure that the `partitions` function is defined and used correctly. Additionally, the `CARD_EQ_LEMMA` and `FINITE_SUBSET_PARTITIONS` theorems may need to be proved or imported separately. The use of `MAP_EVERY` and `EXISTS_TAC` tactics may also require special attention, as they may not have direct equivalents in other proof assistants.

---

