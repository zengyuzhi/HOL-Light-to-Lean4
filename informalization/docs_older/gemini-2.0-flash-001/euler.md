# euler.ml

## Overview

Number of statements: 22

`euler.ml` formalizes Euler's partition theorem along with other basic results in the theory of partitions. The file provides definitions and proofs related to these partition theorems. It does not rely on any external HOL Light libraries.


## NSUM_BOUND_LEMMA

### Name of formal statement
NSUM_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NSUM_BOUND_LEMMA = prove
 (`!f a b n. nsum(a..b) f = n ==> !i. a <= i /\ i <= b ==> f(i) <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM IN_NUMSEG] THEN
  MATCH_MP_TAC NSUM_POS_BOUND THEN ASM_REWRITE_TAC[LE_REFL; FINITE_NUMSEG]);;
```

### Informal statement
For any function `f` from natural numbers to real numbers, and any natural numbers `a`, `b`, and `n`, if the sum of `f(i)` from `i = a` to `i = b` is equal to `n`, then for any `i`, if `a <= i` and `i <= b`, then `f(i) <= n`.

### Informal sketch
The proof proceeds as follows:
- Assume `nsum(a..b) f = n`.
- Assume `a <= i` and `i <= b`.
- Rewrite the interval condition `i IN (a..b)` into `a <= i /\ i <= b`.
- Apply the theorem `NSUM_POS_BOUND`, which states that if `nsum(a..b) f = n`, then `n >= 0` and for all `i` in the interval `a..b`, `n >=f(i)`. This step requires matching `NSUM_POS_BOUND` with the current goal using `MATCH_MP_TAC`.
- Simplify using assumptions and the reflexivity of `<=`, along with the fact that the interval `a..b` is finite.

### Mathematical insight
The theorem states that if the sum of a function's values over an interval equals some number `n`, then each individual value in that sum must be less than or equal to `n`. This is because, in HOL Light, the function `f` has real number values, and by `NSUM_POS_BOUND` the terms `f i` are non-negative; hence the lemma only holds if `f` maps into the non-negative reals.

### Dependencies
- `IN_NUMSEG`
- `NSUM_POS_BOUND`
- `LE_REFL`
- `FINITE_NUMSEG`


---

## CARD_EQ_LEMMA

### Name of formal statement
CARD_EQ_LEMMA

### Type of the formal statement
theorem

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
  EXISTS_TAC `g:B->A` THEN ASM_MESON_TAC[]);;
```
### Informal statement
For all types `A` and `B`, and for all functions `f` from `A` to `B` and `g` from `B` to `A`, and for all sets `s` of type `A` and `t` of type `B`, if `s` is finite and `t` is finite, and for all `x`, if `x` is in `s` then `f(x)` is in `t`, and for all `y`, if `y` is in `t` then `g(y)` is in `s`, and for all `x`, if `x` is in `s` then `g(f(x)) = x`, and for all `y`, if `y` is in `t` then `f(g(y)) = y`; then `s` is finite and `t` is finite and the cardinality of `s` equals the cardinality of `t`.

### Informal sketch
The proof proceeds as follows:
- Assume the hypotheses: `FINITE s`, `FINITE t`, `!x. x IN s ==> f(x) IN t`, `!y. y IN t ==> g(y) IN s`, `!x. x IN s ==> g(f x) = x`, and `!y. y IN t ==> f(g y) = y`.
- Apply the theorem `CARD_IMAGE_INJ_EQ`, which states that if a function `f` is injective on a set `s`, then the cardinality of `s` equals the cardinality of the image of `s` under `f`.
- Show that `f` restricted to `s` is injective. From the hypotheses, `g(f(x)) = x` for all `x` in `s`, so `f` is injective on `s`.
- Show that `t` is the image of `s` under `f`.
   - We know that if `x` is in `s`, then `f(x)` is in `t`. Also, we know that if `y` is in `t`, then `g(y)` is in `s` and `f(g(y)) = y`. This implies that every element `y` in `t` is in the image of `s` under `f`. Therefore, `t` is the image of `s` under `f`.
- Since `f` is injective on `s` and `t` is the image of `s` under `f`, we conclude that `CARD s = CARD t`. The finiteness conditions were proven in the assumptions.

### Mathematical insight
This theorem establishes that if there exist functions `f: A -> B` and `g: B -> A` such that `f` maps set `s` into set `t`, `g` maps set `t` into set `s`, and `f` and `g` are inverses on `s` and `t` respectively, then `s` and `t` have the same cardinality. The existence of such inverse functions between two sets `s` and `t` implies that there is a bijection between them, thus having the same cardinality.

### Dependencies
- Theorems: `CARD_IMAGE_INJ_EQ`

### Porting notes (optional)
The main challenge in porting this theorem lies in replicating the tactic `ASM_MESON_TAC[]`. Meson is essentially a resolution prover and its behavior may need to be emulated via other automated or semi-automated reasoning tools. The `CARD_IMAGE_INJ_EQ` theorem also needs to be ported.


---

## index

### Name of formal statement
- index

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let index = define
 `index n = if n = 0 then 0 else if ODD n then 0 else SUC(index(n DIV 2))`;;
```

### Informal statement
- Define a function `index` on natural numbers such that `index n` is `0` if `n` is `0`, `0` if `n` is odd, and otherwise `SUC(index(n DIV 2))`.

### Informal sketch
- The definition of `index` is given by primitive recursion on the natural number `n`.
- Base case: If `n = 0`, then `index n = 0`.
- Recursive cases:
    - If `n` is odd, then `index n = 0`.
    - If `n` is even (i.e., not odd and not 0), then `index n` is defined recursively as `SUC(index(n DIV 2))`. This means that we divide `n` by 2 and take the successor of the `index` of the quotient.
- The `ODD` and `DIV` functions are assumed to be already defined.

### Mathematical insight
- The `index` function computes the highest power of 2 that divides `n`. In other words, breaking a number up into `2^something * odd_number`, the `index` function computes the `something`. Starting with an even number `n`, we repeatedly divide by 2 until we get an odd number, counting how many times we divided by 2.

### Dependencies
- Definitions: `ODD`, `DIV`, `SUC`


---

## oddpart

### Name of formal statement
- oddpart

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let oddpart = define
 `oddpart n = if n = 0 then 0 else if ODD n then n else oddpart(n DIV 2)`;;
```
### Informal statement
- The function `oddpart` is defined recursively on natural numbers `n` as follows: if `n` is equal to 0, then `oddpart(n)` is 0; otherwise, if `n` is odd, then `oddpart(n)` is `n`; otherwise, `oddpart(n)` is `oddpart(n DIV 2)`.

### Informal sketch
- The definition of `oddpart` is a straightforward recursive definition. 
- Base Case: If the input `n` is 0, return 0.
- Odd Case: If `n` is odd, return `n`.
- Even Case: If `n` is even, recursively call `oddpart` with the argument `n DIV 2`.

### Mathematical insight
- The `oddpart` function extracts the odd part of a natural number `n`. That is, it repeatedly divides `n` by 2 until it becomes odd or zero.
- This can be useful in number theory to analyze the structure of numbers and their prime factorization.

### Dependencies
- `ODD`


---

## INDEX_ODDPART_WORK

### Name of formal statement
INDEX_ODDPART_WORK

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[ARITH_RULE `~(n = 0) /\ n = 2 * m ==> m < n /\ ~(m = 0)`]);;
```

### Informal statement
For all natural numbers `n`, `n` is equal to `2` raised to the power of `index n`, multiplied by `oddpart n`, and `oddpart n` is odd if and only if `n` is not equal to `0`.

### Informal sketch
The proof proceeds as follows:
- Start with general introduction and rewriting with definitions of `index` and `oddpart`.
- Case split on whether `n = 0`.
  - If `n = 0`, then simplify using arithmetic facts to show the equivalence holds.
  - If `n ≠ 0`, then consider whether `oddpart n` is odd.
    - Simplify using arithmetic, the existence of even numbers, and properties of the exponential function.
    - Apply `ASM_MESON_TAC` with an arithmetic rule to complete the proof.

### Mathematical insight
This theorem establishes the fundamental relationship between a natural number and its `index` and `oddpart`. It states that any non-zero natural number can be uniquely represented as a power of 2 multiplied by an odd number. This is a pivotal concept in number theory, providing a way to decompose numbers and prove subsequent theorems about `index` and `oddpart`.

### Dependencies
- Definitions: `index`, `oddpart`
- Theorems: `ARITH`, `MULT_CLAUSES`, `NOT_ODD`, `EVEN_EXISTS`, `LEFT_IMP_EXISTS_THM`, `EXP`, `MULT_ASSOC`, `ARITH_RULE \`(2 * x) DIV 2 = x\``, `EQ_MULT_LCANCEL`, `ARITH_RULE \`~(n = 0) /\ n = 2 * m ==> m < n /\ ~(m = 0)\``


---

## INDEX_ODDPART_DECOMPOSITION

### Name of formal statement
INDEX_ODDPART_DECOMPOSITION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INDEX_ODDPART_DECOMPOSITION = prove
 (`!n. n = 2 EXP (index n) * oddpart n`,
  MESON_TAC[INDEX_ODDPART_WORK]);;
```
### Informal statement
For all natural numbers `n`, `n` is equal to `2` raised to the power of `index n`, multiplied by `oddpart n`.

### Informal sketch
The proof uses the theorem `INDEX_ODDPART_WORK`. It asserts that every natural number `n` can be uniquely decomposed into a power of 2 multiplied by an odd number, where `index n` gives the exponent of 2 in the decomposition, and `oddpart n` gives the odd factor. The decomposition `n = 2 EXP (index n) * oddpart n` is proven by an automated tactic (`MESON_TAC`) using the pre-proved lemma `INDEX_ODDPART_WORK`.

### Mathematical insight
The theorem `INDEX_ODDPART_DECOMPOSITION` states the fundamental decomposition of any natural number into a power of 2 and an odd number. The function `index n` returns the highest power of 2 that divides `n`, and `oddpart n` is the remaining odd factor when that power of 2 is divided out. This decomposition is unique and plays a crucial role in number theory and computer science, particularly in algorithms that rely on bitwise operations or binary representations of numbers.

### Dependencies
- Theorems: `INDEX_ODDPART_WORK`


---

## ODD_ODDPART

### Name of formal statement
ODD_ODDPART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_ODDPART = prove
 (`!n. ODD(oddpart n) <=> ~(n = 0)`,
  MESON_TAC[INDEX_ODDPART_WORK]);;
```

### Informal statement
For all natural numbers `n`, `oddpart n` is odd if and only if `n` is not equal to 0.

### Informal sketch
The proof uses the tactic `MESON_TAC` with the hint `INDEX_ODDPART_WORK`. This indicates that the theorem is proved by appealing to a pre-existing lemma or result called `INDEX_ODDPART_WORK`, likely related to properties of `oddpart` or odd numbers, and the higher-order automated reasoning engine `MESON_TAC`. The proof likely involves unfolding the definitions of `ODD` and `oddpart`, and then using logical reasoning (possibly involving case splitting) based on the aforementioned lemma to derive the equivalence.

### Mathematical insight
The theorem states a fundamental property of the `oddpart` function and the oddness predicate. `oddpart n` is defined to be the largest odd number that divides `n`. An odd number is necessarily non-zero, and if n is zero then `oddpart n` is defined to be 1, i.e. it is odd. So the intention here is that `oddpart n` is odd and non-zero when `n <> 0`.

### Dependencies
- Theorem: `INDEX_ODDPART_WORK`
- Definition: `ODD`
- Definition: `oddpart`


---

## ODDPART_LE

### Name of formal statement
ODDPART_LE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODDPART_LE = prove
 (`!n. oddpart n <= n`,
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [INDEX_ODDPART_DECOMPOSITION] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * x <= y * x ==> x <= y * x`) THEN
  REWRITE_TAC[LE_MULT_RCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  REWRITE_TAC[EXP_EQ_0; ARITH]);;
```

### Informal statement
For all natural numbers `n`, the odd part of `n` is less than or equal to `n`.

### Informal sketch
The proof proceeds as follows:
- Start with `!n. oddpart n <= n`.
- Expand `oddpart n` using its decomposition `n = oddpart n * 2^ (index n)`.
- Apply the arithmetic rule `1 * x <= y * x ==> x <= y * x`.
- Rewrite using `LE_MULT_RCANCEL` to cancel `oddpart n`.
- Rewrite with `1 <= n <=> ~(n = 0)`.
- Rewrite `EXP_EQ_0` and use arithmetic to finish the proof.

### Mathematical insight
The theorem `ODDPART_LE` simply states that the odd part of a number is less than or equal to the number itself. This is a basic property of the `oddpart` function, which decomposes a natural number into its odd part and a power of 2.

### Dependencies
- Definitions: `oddpart`, `index`
- Theorems: `INDEX_ODDPART_DECOMPOSITION`, `LE_MULT_RCANCEL`, `EXP_EQ_0`
- Rules: `ARITH_RULE`, `1 <= n <=> ~(n = 0)`


---

## INDEX_ODDPART_UNIQUE

### Name of formal statement
INDEX_ODDPART_UNIQUE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INDEX_ODDPART_UNIQUE = prove
 (`!i m i' m'. ODD m /\ ODD m'
               ==> (2 EXP i * m = 2 EXP i' * m' <=> i = i' /\ m = m')`,
  REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM NUMPAIR; NUMPAIR_INJ] THEN
  ARITH_TAC);;
```
### Informal statement
For all natural numbers `i`, `m`, `i'`, and `m'`, if `m` is odd and `m'` is odd, then `2^i * m = 2^i' * m'` if and only if `i = i'` and `m = m'`.

### Informal sketch
The proof proceeds as follows:
- First, use `ODD_EXISTS` to express both `m` and `m'` in the form `2k + 1` and `2k' + 1` respectively.
- Strip the quantifiers and the top-level implication.
- Rewrite using the `NUMPAIR` bijection and injectivity lemmas (`NUMPAIR_INJ`) to split the equality `(i, m) = (i', m')` into `i = i'` and `m = m'`.
- Finally, use arithmetic tactics (`ARITH_TAC`) to discharge any remaining arithmetic goals.

### Mathematical insight
This theorem states that the representation of a natural number as a power of 2 times an odd number is unique. This representation is useful in number theory and is often used in algorithms related to binary representations of numbers.

### Dependencies
- Definitions: `ODD`
- Theorems: `ODD_EXISTS`, `NUMPAIR`,`NUMPAIR_INJ`


---

## INDEX_ODDPART

### Name of formal statement
INDEX_ODDPART

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INDEX_ODDPART = prove
 (`!i m. ODD m ==> index(2 EXP i * m) = i /\ oddpart(2 EXP i * m) = m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`i:num`; `m:num`; `index(2 EXP i * m)`; `oddpart(2 EXP i * m)`]
        INDEX_ODDPART_UNIQUE) THEN
  REWRITE_TAC[GSYM INDEX_ODDPART_DECOMPOSITION; ODD_ODDPART] THEN
  ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH] THEN ASM_MESON_TAC[ODD]);;
```
### Informal statement
For all natural numbers `i` and `m`, if `m` is odd, then the index of `2` to the power of `i` times `m` is `i`, and the odd part of `2` to the power of `i` times `m` is `m`.

### Informal sketch
The proof proceeds by induction and uses the uniqueness of the decomposition into powers of `2` and odd factors.
- Start by generalizing over `i` and `m`.
- Assume `m` is odd.
- Apply the uniqueness theorem `INDEX_ODDPART_UNIQUE` to `i`, `m`, `index(2 EXP i * m)`, and `oddpart(2 EXP i * m)`. This allows us to deduce the required properties from the assumption that `m` is odd and that `index(2 EXP i * m)` and `oddpart(2 EXP i * m)` are uniquely determined.
- Use the decomposition theorem `INDEX_ODDPART_DECOMPOSITION` to rewrite `2 EXP i * m` into `2 EXP (index(2 EXP i * m)) * oddpart(2 EXP i * m)`.
- Use `ODD_ODDPART` to rewrite the premise that `oddpart(2 EXP i * m)` is odd.
- Simplify using `MULT_EQ_0`, `EXP_EQ_0`, and arithmetic reasoning to eliminate trivial cases.
- Use `ASM_MESON_TAC` to automatically discharge the remaining goals using the assumption that `m` is odd.

### Mathematical insight
The theorem formalizes the intuitive idea that any number can be uniquely decomposed into a power of `2` and an odd number. The `index` function extracts the exponent of `2` in this decomposition, and the `oddpart` function gives the odd factor. The theorem states that if we start with an odd number `m`, multiply it by `2^i`, then the index of the result will be `i` and the odd part will remain `m`.

### Dependencies
- `INDEX_ODDPART_UNIQUE`
- `INDEX_ODDPART_DECOMPOSITION`
- `ODD_ODDPART`
- `MULT_EQ_0`
- `EXP_EQ_0`
- `ARITH`
- `ODD`


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
The function `odd_of_distinct` maps a function `p` (representing a partition into distinct parts) to another function, defined as follows: for an input `i`, if `i` is odd, then the result is the sum (indexed by `j`) of `2` to the power of `j`, where the sum is taken over all `j` such that `p(2 EXP j * i) = 1`; otherwise, if `i` is even, the result is `0`.

### Informal sketch
- The definition introduces a mapping from partitions into distinct parts (represented by a function `p`) to another function, `odd_of_distinct p`.
- For odd values of the input `i`, `odd_of_distinct p` calculates a sum involving powers of 2 based on the values of `p` at multiples of `i` that are powers of 2.
- For even values of the input `i`, `odd_of_distinct p` simply returns `0`.

### Mathematical insight
The function `odd_of_distinct` is part of a mapping between partitions into distinct parts and partitions into odd parts. The sum `nsum {j | p(2 EXP j * i) = 1} (\j. 2 EXP j)` is constructing a number by summing powers of 2, based on whether `i * 2^j` is a part in the distinct partition `p`. This definition is likely used in a proof showing the equivalence between counting partitions into distinct parts and partitions into odd parts.

### Dependencies
- `ODD`
- `nsum`
- `EXP`


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
The function `distinct_of_odd` takes a function `p` from natural numbers to sets of natural numbers and returns a function that maps an index `i` to 1 if the index `i` (converted to a natural number) is in the set defined by `p` applied to the odd part of `i`, otherwise it maps `i` to 0.

### Informal sketch
- The definition introduces `distinct_of_odd p` as a function.
- The value of `distinct_of_odd p i` is defined by a conditional expression.
- The condition checks whether the natural number representation of `i` is contained in the bitset representation of the set obtained by applying `p` to the odd part of `i`.
- If the condition is true, the function returns 1, otherwise it returns 0.
- The function `index` converts a term of type `:('a, num) index` to a natural number.
- The function `oddpart` returns the odd part of a natural number.
- The function `bitset` converts a set of natural numbers to a bitset representation.

### Mathematical insight
This definition appears to be constructing a mechanism for distinguishing elements based on properties of their odd parts and set membership tests. The `bitset` conversion would be used to efficiently check whether the index `i` belongs to the set returned by `p(oddpart i)`. This could be useful for creating characteristic functions or indicators for specific classes of indices.

### Dependencies
- Definitions:
  - `bitset`
  - `index`
  - `oddpart`


---

## ODD_ODD_OF_DISTINCT

### Name of formal statement
ODD_ODD_OF_DISTINCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_ODD_OF_DISTINCT = prove
 (`!p i. ~(odd_of_distinct p i = 0) ==> ODD i`,
  REWRITE_TAC[odd_of_distinct] THEN MESON_TAC[]);;
```
### Informal statement
For all predicates `p` and natural numbers `i`, if `odd_of_distinct p i` is not equal to 0, then `i` is odd.

### Informal sketch
The proof proceeds as follows:
- The theorem is proved by rewriting with the definition of `odd_of_distinct` and then calling a MESON tactic.
- Rewrite with `odd_of_distinct` unfolds the definition of `odd_of_distinct p i`.
- MESON is a first-order automatic theorem prover that completes the proof, likely by considering the cases where `i` is or is not in the partition induced by `p`, and utilizing the assumption that `odd_of_distinct p i` is not zero.

### Mathematical insight
This theorem states a fundamental property about the `odd_of_distinct` function. If `odd_of_distinct p i` is non-zero, it indicates that `i` must be odd. This constraint is essential since `odd_of_distinct` is defined in terms of modulo 2, and a non-zero result implies that there was a non-zero remainder when counting elements satisfying predicate `p`.

### Dependencies
- Definition: `odd_of_distinct`


---

## DISTINCT_DISTINCT_OF_ODD

### Name of formal statement
DISTINCT_DISTINCT_OF_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISTINCT_DISTINCT_OF_ODD = prove
 (`!p i. distinct_of_odd p i <= 1`,
  REWRITE_TAC[distinct_of_odd] THEN ARITH_TAC);;
```
### Informal statement
For all predicates `p` on natural numbers, and for all natural numbers `i`, `distinct_of_odd p i` is less than or equal to 1.

### Informal sketch
The proof proceeds by rewriting with the definition of `distinct_of_odd` and then using arithmetic tactics.

- The definition of `distinct_of_odd p i` is `if p (2 * i + 1) then 1 else 0`.
- Since the conditional expression evaluates to either 0 or 1, the result is always less than or equal to 1.

### Mathematical insight
The theorem states a simple property about the `distinct_of_odd` function, namely that it only produces 0 or 1 as output. This function is defined in terms of a predicate `p` and natural number `i`. It checks the value of `p` at the odd number `2 * i + 1`, returning 1 if the predicate holds and 0 otherwise.

### Dependencies
- Definitions: `distinct_of_odd`


---

## SUPPORT_ODD_OF_DISTINCT

### Name of formal statement
SUPPORT_ODD_OF_DISTINCT

### Type of the formal statement
theorem

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
    REWRITE_TAC[EXP_EQ_0; ARITH]]);;
```
### Informal statement
For any function `p` from natural numbers to natural numbers, if for all `i`, `p(i)` is not equal to 0 implies that `i` is less than or equal to `n`, then for all `i`, `odd_of_distinct p i` not equal to 0 implies that `1 <= i` and `i <= n`.

### Informal sketch
The proof proceeds as follows:
- Assume `!i. ~(p i = 0) ==> i <= n` and `~(odd_of_distinct p i = 0)`.
- We aim to show `1 <= i /\ i <= n`.
- Use `odd_of_distinct` definition which states `odd_of_distinct p i = NSUM (\j. if p (2 EXP j * i) = 1 then 1 else 0) 0..`.
- Case split on `i = 0`. If `i=0`, use `LE_0` to derive a contradiction.
- Otherwise, assume `i != 0`. Henceforth `1 <= i`.
- Show that the set `{j | p (2 EXP j * i) = 1}` is finite by showing it's a subset of `0..n`. Proceed by showing that if `p (2 EXP j * i) = 1` then `2 EXP j * i <= n`.
- Assume `~(i = 0)` together with the assumption `!i. ~(p i = 0) ==> i <= n`.
- Use `LE_TRANS` to show `2 EXP j * i <= n`.
- We have `p (2 EXP j * i) = 1`. Therefore, `~(p (2 EXP j * i) = 0)`.
- By assumption `!i. ~(p i = 0) ==> i <= n` we get `2 EXP j * i <= n`.
- Thus, `FINITE {j | p (2 EXP j * i) = 1}`.
- Show that `~(odd_of_distinct p i = 0)` implies `FINITE {j | p (2 EXP j * i) = 1}` is false or that there exists a `j` such that `p (2 EXP j * i) = 1`.

### Mathematical insight
The theorem states that if the support of a function `p` is bounded by `n`, then the support of the `odd_of_distinct` transform of `p` is also bounded by `n`. The function `odd_of_distinct` is related to representing numbers as sums of distinct odd numbers.

### Dependencies
- `ODD`
- `ARITH_RULE`
- `ODD_ODD_OF_DISTINCT`
- `odd_of_distinct`
- `LE_0`
- `FINITE_SUBSET`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `SUBSET`
- `IN_ELIM_THM`
- `LE_TRANS`
- `ARITH_EQ`
- `LT_POW2_REFL`
- `LE_MULT_LCANCEL`
- `EXP_EQ_0`
- `ARITH`
- `NSUM_EQ_0_IFF`
- `NOT_FORALL_THM`
- `IN_ELIM_THM`
- `LE_MULT_RCANCEL`


---

## SUPPORT_DISTINCT_OF_ODD

### Name of formal statement
SUPPORT_DISTINCT_OF_ODD

### Type of the formal statement
theorem

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
  ASM_REWRITE_TAC[LE_MULT_RCANCEL]);;
```

### Informal statement
For all `p` and `n`, if for all `i`, `p(i) * i <= n`, and for all `i`, if `p(i)` is not equal to 0, then `i` is odd, then for all `i`, if `distinct_of_odd p i` is not equal to 0, then `1 <= i` and `i <= n`.

### Informal sketch
The proof proceeds as follows:
- Unfold the definition of `distinct_of_odd`.
- Simplify the resulting expression using the rule that `(if a then 1 else 0) = 0` is equivalent to `~a`.
- Generalize and strip quantifiers.
- Introduce `i` as a variable of type `num`.
- Repeatedly strip assumptions.
- Show that `1 <= i` is equivalent to `~(i = 0)`.
- Discharge this equivalence and substitute it into the goal.
- Undischarge `index 0 IN bitset (p (oddpart 0))`.
- Rewrite using the definitions of `index` and `oddpart` and arithmetic.
- Use the assumption that `!i. ~(p i = 0) ==> ODD i` with `0` as the argument, and apply it using `MP_TAC`.
- Simplify using arithmetic, `BITSET_0`, and `NOT_IN_EMPTY`.
- Apply `ALL_TAC`.
- Use `BITSET_BOUND_LEMMA` on the assumption and apply `ASSUME_TAC` and `MATCH_MP`.
- Apply transitivity of less than or equal to using `LE_TRANS`.
- Perform existential instantiation with `p(oddpart i) * oddpart i`.
- Rewrite using assumptions.
- Apply the `LAND_CONV` tactic with `INDEX_ODDPART_DECOMPOSITION` to generalize rewriting.
- Rewrite using assumptions and `LE_MULT_RCANCEL`.

### Mathematical insight
This theorem states that if `p(i) * i <= n` for all `i`, and `p(i)` is only non-zero when `i` is odd, then `distinct_of_odd p i` is only non-zero when `1 <= i <= n`. In other words, `distinct_of_odd p i` represents selecting distinct odd parts within a certain range, defined as `n`.

### Dependencies
- `distinct_of_odd`
- `index`
- `oddpart`
- `ARITH`
- `BITSET_0`
- `NOT_IN_EMPTY`
- `BITSET_BOUND_LEMMA`
- `LE_TRANS`
- `INDEX_ODDPART_DECOMPOSITION`
- `LE_MULT_RCANCEL`


---

## ODD_OF_DISTINCT_OF_ODD

### Name of formal statement
ODD_OF_DISTINCT_OF_ODD

### Type of the formal statement
theorem

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
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;
```

### Informal statement
For any function `p` from natural numbers to boolean values, if for all `i`, `p(i)` is false only when `i` is zero and also `i` is odd, then `odd_of_distinct (distinct_of_odd p)` is equal to `p`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting using the definitions of `IN_ELIM_THM`, `odd_of_distinct`, and `distinct_of_odd` to expand the definitions.
- Perform repeated stripping of quantifiers and implications.
- Rewrite using `FUN_EQ_THM` to establish functional equality.
- Generalize with respect to `i:num`.
- Perform case splitting.
- Use assumptions and meson to discharge one case.
- Simplify using `INDEX_ODDPART`.
- Rewrite using `GSYM BINARYSUM_BITSET` to reverse `BINARYSUM_BITSET`.
- Rewrite using `binarysum`.
- Apply an application theorem twice.
- Rewrite using `EXTENSION` and `IN_ELIM_THM`.
- Generalize.
- Perform case splitting.
- Simplify using the assumptions and arithmetic equality.

### Mathematical insight
The theorem `ODD_OF_DISTINCT_OF_ODD` shows that starting with a predicate `p` that characterizes a set of odd numbers (excluding 0), applying `distinct_of_odd` to get an explicit set representation, and then using `odd_of_distinct` to recover a predicate, we arrive back at the original predicate `p`. This demonstrates a form of equivalence or round-trip property between predicates on odd numbers (not including 0) and their set representations.

### Dependencies
- `IN_ELIM_THM`
- `odd_of_distinct`
- `distinct_of_odd`
- `FUN_EQ_THM`
- `INDEX_ODDPART`
- `BINARYSUM_BITSET`
- `binarysum`
- `EXTENSION`
- `ARITH_EQ`


---

## DISTINCT_OF_ODD_OF_DISTINCT

### Name of formal statement
DISTINCT_OF_ODD_OF_DISTINCT

### Type of the formal statement
theorem

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
    ASM_MESON_TAC[ARITH_RULE `i <= 1 ==> i = 0 \/ i = 1`]]);;
```

### Informal statement
For all `p`, if for all `i`, `p i` is not equal to 0 implies `1 <= i` and `i <= n`, and for all `i`, `p i` is less than or equal to 1, then `distinct_of_odd (odd_of_distinct p)` is equal to `p`.

### Informal sketch
The proof demonstrates that the function `distinct_of_odd` applied to `odd_of_distinct p` returns the original function `p` under the given conditions. The proof proceeds as follows:

- Initially, rewrite using the definitions of `distinct_of_odd` and `odd_of_distinct`.
- Further simplification uses the definitions of `partitions` and `ODD_ODDPART`.
- Repeatedly strip the quantifiers and implications.
- Apply functional equality `FUN_EQ_THM`, introducing a variable `i`.
- Perform case splitting on `i = 0`.  
    - If `i = 0`, simplify using `BITSET_0` and `NOT_IN_EMPTY`, then use `ARITH_RULE` to prove the subgoal is contradictory given the assumptions.
    - Otherwise, it proceeds to proving the finiteness of `{j | p (2 EXP j * oddpart i) = 1}`.
- To show that `{j | p (2 EXP j * oddpart i) = 1}` is finite, show that it is a subset of `0..n.`
    - Show that `j <= n ` using `ARITH_RULE` and that `{j | p (2 EXP j * oddpart i) = 1}` is a subset of `0..n.`
- Simplify using the properties of `BITSET_BINARYSUM`, `binarysum`, and `INDEX_ODDPART_DECOMPOSITION`.
- Case split and rewrite using arithmetic equality. Use `i <= 1 ==> i = 0 \/ i = 1` to complete the proof.

### Mathematical insight
This theorem establishes a relationship between `distinct_of_odd` and `odd_of_distinct`, showing that under certain conditions, the composition of these functions results in the identity function. The conditions ensure that `p` is a function that maps to either 0 or 1, and its non-zero elements are within the range `1` to `n`. The theorem suggests that `odd_of_distinct` extracts the odd parts of the indices where `p` evaluates to 1, and `distinct_of_odd` reconstructs `p` from this information.

### Dependencies
- Definitions: `distinct_of_odd`, `odd_of_distinct`, `partitions`
- Theorems: `IN_ELIM_THM`, `FUN_EQ_THM`, `BITSET_0`, `NOT_IN_EMPTY`, `FINITE_SUBSET`,`FINITE_NUMSEG`, `IN_NUMSEG`, `SUBSET`, `LE_0`, `LT_POW2_REFL`, `LE_MULT_RCANCEL`, `ODD_ODDPART`, `ODD`, `BITSET_BINARYSUM`, `binarysum`, `INDEX_ODDPART_DECOMPOSITION`
- Rules: `ARITH_RULE`

### Porting notes (optional)
- The proof relies on specific arithmetic reasoning (`ARITH_RULE`). Ensure the target proof assistant has comparable automation or the proof may require more manual steps.
- The tactic `ASM_CASES_TAC` and `COND_CASES_TAC` might need to be translated into equivalent case analysis tactics present in other proof assistants.


---

## NSUM_DISTINCT_OF_ODD

### Name of formal statement
NSUM_DISTINCT_OF_ODD

### Type of the formal statement
theorem

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
      ASM_MESON_TAC[BITSET_BOUND_LEMMA; LE_MULT_RCANCEL; LE_TRANS]]]);;
```

### Informal statement
For any function `p` from numbers to numbers, if the following conditions hold:
1. For all `i`, if `p(i)` is not equal to 0, then `i` is between 1 and `n` (inclusive).
2. For all `i`, `p(i) * i` is less than or equal to `n`.
3. For all `i`, if `p(i)` is not equal to 0, then `i` is odd.

Then, the sum from 1 to `n` of `distinct_of_odd p i * i` is equal to the sum from 1 to `n` of `p i * i`.

### Informal sketch
The theorem states that under certain conditions relating `p` and `n`, the sum of `distinct_of_odd p i * i` from 1 to `n` is equal to the sum of `p i * i` from 1 to `n`. The proof proceeds as follows:
- Rewrite `distinct_of_odd` using its definition.
- Transform the sum involving `distinct_of_odd` into a binary sum over a bitset. This involves rewriting using `BINARYSUM_BITSET` and related theorems.
- Simplify using properties of `nsum`, `binarysum`, `support`, and sets. Specifically, it uses `NSUM_NSUM_PRODUCT` to combine sums, and rewrites involving `FINITE_BITSET`, `FINITE_NUMSEG`.
- The core of the proof involves showing that the set `{x | x IN {i,j | i IN 1..n /\ j IN bitset(p i)} /\ ~((\(i,j). 2 EXP j * i) x = 0)}` is equal to the set `{i,j | i IN 1..n /\ j IN bitset(p i)}`. This involves set extensionality and simplification with arithmetic facts.
- Similarly, it shows that `{x | x IN 1 .. n /\ ~((if index x IN bitset (p (oddpart x)) then 1 else 0) * x = 0)}` is equal to `{i | i IN 1..n /\ (index i) IN bitset (p(oddpart i))}`.
- Use `NSUM_EQ_GENERAL` to relate the two sums. This involves exhibiting a function (in this case, `\(i,b). 2 EXP b * i`) that decomposes each number in the range 1..n uniquely.
- Several simplification steps using arithmetic rules, set theory, and properties of `oddpart` and `index`.
- A key subgoal is to prove `!i j. j IN bitset(p i) ==> ODD i`. This relies on the initial hypothesis that if `p(i)` is nonzero, then `i` is odd.
- The proof uses `INDEX_ODDPART_DECOMPOSITION` in conjunction with `oddpart` and `index` to show the unique decomposition. This also relies on properties such as `ODDPART_LE`, `LE_TRANS`, `ODD_ODDPART`, and `INDEX_ODDPART_UNIQUE`.

### Mathematical insight
The theorem essentially states that under the given conditions regarding oddness and the bounds on `p(i)`, selecting only the odd parts of `p(i)` makes no difference to the overall sum. The `distinct_of_odd` function probably has relevance to sums involving distinct odd factors of a number. The conditions ensure that the `p` function has a limited support and respects the divisibility constraints imposed by the theorem.

### Dependencies
- `distinct_of_odd`
- `BINARYSUM_BITSET`
- `binarysum`
- `NSUM_RMUL`
- `NSUM_NSUM_PRODUCT`
- `FINITE_BITSET`
- `FINITE_NUMSEG`
- `NSUM_SUPPORT`
- `support`
- `NEUTRAL_ADD`
- `EXTENSION`
- `FORALL_PAIR_THM`
- `IN_ELIM_PAIR_THM`
- `IN_ELIM_THM`
- `IN_NUMSEG`
- `EXP_EQ_0`
- `MULT_EQ_0`
- `NSUM_EQ_GENERAL`
- `EXISTS_UNIQUE_THM`
- `BITSET_0`
- `NOT_IN_EMPTY`
- `INDEX_ODDPART_DECOMPOSITION`
- `ODDPART_LE`
- `LE_TRANS`
- `ODD_ODDPART`
- `ODD`
- `INDEX_ODDPART_UNIQUE`
- `INDEX_ODDPART`
- `BITSET_BOUND_LEMMA`
- `LE_MULT_RCANCEL`

### Porting notes (optional)
- The proof relies heavily on rewriting with arithmetic rules and set theory. Ensure the target proof assistant has similar capabilities.
- The use of `oddpart` and `index` functions suggests a reliance on number theory. Ensure that the definitions and required lemmas related to these functions are available.
- The tactic `MESON_TAC` is used extensively, so automated reasoning capabilities are beneficial for porting this theorem.


---

## DISTINCT_OF_ODD

### Name of formal statement
DISTINCT_OF_ODD

### Type of the formal statement
theorem

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
  ASM_MESON_TAC[NSUM_BOUND_LEMMA]);;
```

### Informal statement
For any function `p` such that `p` partitions `n` and for all `i`, if `p(i)` is not equal to 0, then `i` is odd, it follows that `distinct_of_odd p` (where `distinct_of_odd` depends on `n` and `p`) partitions `n` and for all `i`, `distinct_of_odd p` at `i` is less than or equal to 1.

### Informal sketch
The proof proceeds as follows:
- The goal is to prove that `distinct_of_odd p` is a partition of `n` into parts that are at most 1, given that `p` is a partition of `n` into odd parts.
- First, rewrite using `IN_ELIM_THM` and `partitions` to expand the definition of `partitions`.
- Then, rewrite using `DISTINCT_DISTINCT_OF_ODD` to relate `distinct_of_odd p` to properties of the distinct parts of `p`.
- The proof splits into two subgoals using `CONJ_TAC`. The first subgoal concerns showing that `distinct_of_odd p` is a partition (i.e., its sum equals `n`). The second subgoal concerns showing that the values of `distinct_of_odd p` are 0 or 1.
    - For the first subgoal:
        - Apply a theorem stating that the support of the partition equals `n`.
        - Rewrite with a given assumption, generalizing over a variable and symmetrizing.
        - A lemma linking `NSUM` with `distinct_of_odd` is then applied.
    - Simplify using assumptions.
- Introduce a variable `i:num` and perform case analysis on whether `p(i) = 0`.
- If `p(i) = 0`, then rewrite using arithmetic lemmas (`MULT_CLAUSES` and `LE_0`).
- Finally, apply a lemma regarding the bound on the sum using `MESON_TAC`.

### Mathematical insight
The theorem `DISTINCT_OF_ODD` establishes that if a partition `p` of `n` consists only of odd parts, then the function `distinct_of_odd p`, which indicates the number of distinct parts in `p`, forms a partition of `n` where each part is at most 1. This implies that the number of parts is equal to `n`, therefore, `n` is the number of distinct items. This is significant because it provides a connection between partitions into odd parts and partitions into parts of size at most 1, and gives a method to calculate the amount of items that can be divided into partition p, based on a function mapping the number of distinct parts.

### Dependencies
- Definitions:
  - `partitions`

- Theorems/Lemmas:
  - `IN_ELIM_THM`
  - `DISTINCT_DISTINCT_OF_ODD`
  - `SUPPORT_DISTINCT_OF_ODD`
  - `NSUM_DISTINCT_OF_ODD`
  - `MULT_CLAUSES`
  - `LE_0`
  - `NSUM_BOUND_LEMMA`

### Porting notes (optional)
- The specific support tactic `ASM_MESON_TAC` may need to be replaced by a different form of automated reasoning in other proof assistants.
- Porting to other systems will depend on how partitions and arithmetic are formalized. Ensure that the definitions of `partitions` and related functions are compatible.


---

## ODD_OF_DISTINCT

### Name of formal statement
ODD_OF_DISTINCT

### Type of the formal statement
theorem

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
    ASM_MESON_TAC[ARITH_RULE `~(1 = 0)`]]);;
```
### Informal statement
For all `p`, if `p` is a partition of `n` such that for all `i`, `p(i)` is less than or equal to 1, then `odd_of_distinct(p)` is a partition of `n` such that for all `i`, if `odd_of_distinct(p)(i)` is not equal to 0, then `i` is odd.

### Informal sketch
The proof proceeds as follows:
- Assume `p` is a partition of `n` and `p(i) <= 1` for all `i`.
- Show that `odd_of_distinct p` is a partition of `n`. This means we have to show that the support is finite and the sum over the support is `n`.
- We use `ODD_ODD_OF_DISTINCT` to show that `odd_of_distinct p` is non-zero only on odd numbers.
- Show that `odd_of_distinct p` is a partition of `n` by showing that the sum of `distinct_of_odd(odd_of_distinct p) i * i` from `i = 1` to `n` is equal to `n`.
- Apply `NSUM_DISTINCT_OF_ODD` to simplify.
- Show that for all `i`, if `odd_of_distinct(p)(i)` is not 0, then `i` is odd.
- Consider the cases where `p(i) = 1` or `p(i) != 1`.
- Establish that the set `{i | p(i) = 1}` is finite by showing that it is a subset of `1..n`, which is finite. This is equivalent to showing that it is a subset of `n`. `FINITE_SUBSET` helps to prove this.
- By `INDEX_ODDPART_UNIQUE`, simplify the equation.
- Show the appropriate inequality by showing each side is less than or equal to `n`.

### Mathematical insight
The theorem states that if `p` is a partition of `n` into distinct parts (i.e., each part appears at most once), then the function `odd_of_distinct p` constructs a partition with only odd parts. `odd_of_distinct` uses `distinct_of_odd` to isolate the powers of 2. This is a standard combinatorial construction.

### Dependencies
- Definitions: `partitions`
- Theorems: `IN_ELIM_THM`, `ODD_ODD_OF_DISTINCT`, `SUPPORT_ODD_OF_DISTINCT`, `DISTINCT_OF_ODD_OF_DISTINCT`, `NSUM_DISTINCT_OF_ODD`, `o_DEF`, `INDEX_ODDPART_UNIQUE`, `FINITE_SUBSET`
- Rules: `ARITH_RULE`, `LE_0`, `MULT_CLAUSES`

### Porting notes (optional)
The definition of `nsum` and the handling of finite sets may require specific attention during porting.
Also, the automation provided by tactics like `ASM_MESON_TAC` might need to be replaced by explicit proof steps depending on the target proof assistant.
The use of indexed sets `{i | p(i) = 1}` for summation is a common pattern.


---

## EULER_PARTITION_THEOREM

### Name of formal statement
EULER_PARTITION_THEOREM

### Type of the formal statement
theorem

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
  ASM_REWRITE_TAC[]);;
```

### Informal statement
The set of partitions of `n` into distinct parts is finite, the set of partitions of `n` into odd parts is finite, and the cardinality of the set of partitions of `n` into distinct parts is equal to the cardinality of the set of partitions of `n` into odd parts. Here, a partition `p` of `n` is a function from natural numbers to natural numbers such that the sum of `p(i)` for all `i` is `n`. A partition `p` into distinct parts satisfies `p(i) <= 1` for all `i`. A partition `p` into odd parts satisfies that if `p(i)` is not zero, then `i` is odd.

### Informal sketch
The proof uses the lemma `CARD_EQ_LEMMA` and rewrites with `FINITE_SUBSET_PARTITIONS` to show that the sets are finite. Then, the proof establishes a bijection between the set of partitions into distinct parts and the set of partitions into odd parts. The bijection is constructed using two functions, `odd_of_distinct` and `distinct_of_odd`, which convert between the two types of partitions. Show that the images of these functions exist using `EXISTS_TAC`. Then rewrite with `ODD_OF_DISTINCT` and `DISTINCT_OF_ODD`. Then split the goal using `CONJ_TAC`, generalize over a partition `p` using `X_GEN_TAC`, rewrite with definitions `IN_ELIM_THM` and `partitions`. Finally, apply `DISTINCT_OF_ODD_OF_DISTINCT` and `ODD_OF_DISTINCT_OF_ODD` using `MATCH_MP_TAC`. Then clear the assumptions using `ASM_REWRITE_TAC`.

### Mathematical insight
Euler's partition theorem is a classical result in number theory that establishes a surprising connection between two seemingly different types of partitions.  It demonstrates a non-obvious combinatorial equality that leads to various insights in enumerative combinatorics and related fields.

### Dependencies
- Definitions:
  - `partitions`

- Theorems, Lemmas, and Axioms:
  - `CARD_EQ_LEMMA`
  - `FINITE_SUBSET_PARTITIONS`
  - `ODD_OF_DISTINCT`
  - `DISTINCT_OF_ODD`
  - `IN_ELIM_THM`
  - `DISTINCT_OF_ODD_OF_DISTINCT`
  - `ODD_OF_DISTINCT_OF_ODD`

### Porting notes (optional)
This theorem relies on the `partitions` definition and related lemmas about finiteness and bijections. Ensure that the target proof assistant has similarly defined partitions and corresponding finiteness results about subsets of partitions. The key is to establish the bijection (`odd_of_distinct` and `distinct_of_odd`) and prove that it is indeed a bijection. Recreating the functions `odd_of_distinct` and `distinct_of_odd` faithfully in the target system is essential.


---

