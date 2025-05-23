# ballot.ml

## Overview

Number of statements: 23

`ballot.ml` formalizes the ballot problem, which concerns the probability of a candidate staying ahead in an election. It imports `binomial.ml` and likely contains definitions and theorems related to counting the number of ways a candidate can maintain a lead given certain vote totals. The file provides a formal treatment of this combinatorial problem within HOL Light.


## vote_INDUCT,vote_RECURSION

### Name of formal statement
vote_INDUCT,vote_RECURSION

### Type of the formal statement
new_type_definition

### Formal Content
```ocaml
let vote_INDUCT,vote_RECURSION = define_type
 "vote = A | B";;
```

### Informal statement
Define a type `vote` which can either be `A` or `B`. The functions `vote_INDUCT` and `vote_RECURSION` are generated automatically.

### Informal sketch
This is a type definition introducing a new type `vote` with two constructors, `A` and `B`, representing the two possible values this type can take. The command `define_type` also automatically generates an induction principle (`vote_INDUCT`) and a recursion operator (`vote_RECURSION`) for this type.

### Mathematical insight
This definition sets up a simple type which could represent a voting choice, ballot, or other binary decision. It illustrates a basic type construction in HOL Light. The automatically generated induction and recursion principles are crucial for proving properties about and defining functions over this type.

### Dependencies
None

### Porting notes (optional)
Most proof assistants have mechanisms to define algebraic datatypes and automatically derive induction principles and recursion operators. The porter should consult the specific documentation of the target proof assistant for the appropriate commands.


---

## all_countings

### Name of formal statement
all_countings

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let all_countings = new_definition
 `all_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b}`;;
```
### Informal statement
The function `all_countings a b` is defined as the cardinality of the set of functions `f` from the interval `1..n` to the set `{A, B}`, where `n` is the sum of `a` and `b`, such that the cardinality of the set of `i` in the interval `1..n` where `f(i)` equals `A` is `a`, and the cardinality of the set of `i` in the interval `1..n` where `f(i)` equals `B` is `b`.

### Informal sketch
The definition `all_countings a b` counts functions from an initial segment of the natural numbers (`1..n`, where `n = a + b`) to a two-element set `{A, B}`, subject to cardinality constraints.  Specifically, we require exactly `a` elements in the domain to map to `A`, and `b` elements to map to `B`.

*   The core of the definition is constructing the set of functions satisfying the given properties.
*   The definition uses set comprehension to define a set of functions `f` from `1..n` to `{A, B}` that satisfy two conditions:
    *   The cardinality of the set of `i` in `1..n` such that `f(i) = A` is `a`.
    *   The cardinality of the set of `i` in `1..n` such that `f(i) = B` is `b`.
*   Then, the cardinality of this constructed set becomes the value of the `all_countings` function for the given `a` and `b`.

### Mathematical insight
The definition `all_countings a b` represents a combinatorial problem. It counts the number of ways to assign `A` to `a` elements and `B` to `b` elements from a set of `n = a + b` elements. This is equivalent to counting the number of ways to choose `a` positions for `A` (and implicitly `b` positions for `B`) from `n` positions, which will eventually relate to binomial coefficients. The function `all_countings` gives a set-theoretic definition of the concept before any theorems about its value are proven.

### Dependencies
None

### Porting notes (optional)
The construction of the set of functions may require choosing the appropriate higher-order logic representation of functions and sets, depending on the target proof assistant. The notion of cardinality (CARD) is a key component, and its appropriate formalization needs to be ensured. The set comprehension notation needs to be adapted to the specific syntax of the target proof assistant.


---

## valid_countings

### Name of formal statement
valid_countings

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let valid_countings = new_definition
 `valid_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b /\
                  !m. 1 <= m /\ m <= n
                      ==> CARD { i | i IN 1..m /\ f(i) = A} >
                          CARD { i | i IN 1..m /\ f(i) = B}}`;;
```
### Informal statement
The function `valid_countings`, when applied to natural numbers `a` and `b`, is defined to be the cardinality of the set of functions `f` from the interval `1..n` to the set `{A, B}`, where `n` equals `a + b`, such that:
1. The cardinality of the set of `i` in `1..n` where `f(i) = A` is equal to `a`.
2. The cardinality of the set of `i` in `1..n` where `f(i) = B` is equal to `b`.
3. For all `m` such that `1 <= m` and `m <= n`, the cardinality of the set of `i` in `1..m` such that `f(i) = A` is strictly greater than the cardinality of the set of `i` in `1..m` such that `f(i) = B`.

### Informal sketch
- The definition introduces a predicate `valid_countings a b`, which represents the number of valid ways to arrange `a` occurrences of `A` and `b` occurrences of `B` in a sequence of length `n = a + b`, such that at any prefix of the sequence, the number of `A`s is strictly greater than the number of `B`s.
- The definition first computes the length of the sequence as `n = a + b`.
- The defined predicate `valid_countings a b` then calculates the cardinality of the set of functions `f` from the interval `1..n` to the set `{A,B}`. These functions must satisfy the following three conditions:
    - The number of times `A` occurs in the sequence (represented by `f`) is equal to `a`.
    - The number of times `B` occurs in the sequence (represented by `f`) is equal to `b`.
    - For every prefix of the sequence (represented by `m` from `1` to `n`), the number of `A`s in that prefix must be strictly greater than the number of `B`s in that prefix.

### Mathematical insight
This definition formalizes the notion of counting sequences of `A`s and `B`s such that the number of `A`s always leads the number of `B`s. This is often related to Catalan numbers and Dyck paths, where `A` can be interpreted as an "up" step and `B` as a "down" step. The condition that the number of `A`s always exceeds the number of `B`s ensures that the path never goes below the x-axis.

### Dependencies
None

### Porting notes (optional)
- Porting this definition requires facilities for defining sets (specifically, set comprehension based on a predicate), defining functions, and working with cardinalities of sets. It also requires the ability to define and manipulate finite ranges of natural numbers (e.g., `1..n`). The most subtle part might be the third condition related to prefixes; ensure the target system can express and reason about such prefix properties effectively.


---

## vote_CASES

### Name of formal statement
vote_CASES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let vote_CASES = cases "vote"
and vote_DISTINCT = distinctness "vote";;
```

### Informal statement
The theorem `vote_CASES` states the exhaustiveness of the cases arising from the inductive type `vote`. The theorem `vote_DISTINCT` states the distinctness of the constructors of the inductive type `vote`.

### Informal sketch
- The theorem `vote_CASES` is automatically generated by the `cases` tactic when an inductive type `vote` is defined. It essentially provides a case-analysis principle for the inductive type `vote`. The proof is trivial as it is a definitional axiom.
- The theorem `vote_DISTINCT` is automatically generated by the `distinctness` tactic when an inductive type `vote` is defined. It states that the constructors for the type `vote` are distinct. The proof is trivial as it is a definitional axiom.

### Mathematical insight
These theorems (`vote_CASES` and `vote_DISTINCT`) are standard properties automatically generated and associated with inductive types in HOL Light. `vote_CASES` allows reasoning by cases on the structure of the inductively defined type `vote`. `vote_DISTINCT` ensures that different constructors represent distinct values of the type `vote`, which is essential for sound reasoning about the type.

### Dependencies
- Requires the definition of the inductive type `vote`.


---

## FINITE_COUNTINGS

### Name of formal statement
FINITE_COUNTINGS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_COUNTINGS = prove
 (`FINITE {f | f IN (1..n --> {A,B}) /\ P f}`,
  MATCH_MP_TAC FINITE_RESTRICT THEN
  MATCH_MP_TAC FINITE_FUNSPACE THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_INSERT; FINITE_RULES]);;
```
### Informal statement
For any natural number `n`, the set of functions `f` from the interval `1..n` to the set `{A, B}` such that `P f` holds, is finite.

### Informal sketch
The proof proceeds by showing that the set of functions from `1..n` to `{A, B}` satisfying a property `P` is finite.
- First apply `FINITE_RESTRICT` to show that if `X` is finite then `{x | x IN X /\ P x}` is finite. Here, we need to show that the set of functions from `1..n` to `{A, B}` is finite.
- Then, apply `FINITE_FUNSPACE` to show that if `A --> B` denotes the set of all functions from `A` to `B`, then `FINITE A /\ FINITE B ==> FINITE (A --> B)`. In this case, we need to show that `1..n` and `{A, B}` are both finite.
- The goal `FINITE (1..n)` is rewritten using `FINITE_NUMSEG`, which states that for any `n`, the set `1..n` is finite.
- The goal `FINITE {A,B}` is rewritten using `FINITE_INSERT` and `FINITE_RULES`. The theorem `FINITE_INSERT` states that `FINITE s ==> FINITE (INSERT x s)`. The theorem `FINITE_RULES` contains various rules concerning `FINITE`, including the following two, `FINITE EMPTY` and `!s t. FINITE (UNION s t) <=> FINITE s /\ FINITE t`.

### Mathematical insight
This theorem states that a set of functions with a finite domain and a finite codomain such that they satisfy a certain property is finite. The result uses the fact that any restriction of a finite set is finite, and the set of all functions from a finite set to a finite set is finite. This result is used in counting arguments.

### Dependencies
- `FINITE_RESTRICT`
- `FINITE_FUNSPACE`
- `FINITE_NUMSEG`
- `FINITE_INSERT`
- `FINITE_RULES`


---

## UNIV_VOTE

### Name of formal statement
UNIV_VOTE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let UNIV_VOTE = prove
 (`(:vote) = {A,B}`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY; vote_CASES]);;
```

### Informal statement
It is provable that the type `:vote` is equal to the set containing `A` and `B`.

### Informal sketch
The proof proceeds by rewriting the goal `(:vote) = {A,B}` using several lemmas:
- `EXTENSION`: This is likely the axiom of extensionality, which states that two sets are equal if and only if they have the same members.
- `IN_UNIV`: This lemma likely defines the characteristic property that states all elements of the type `:vote` are members of the universe set of `:vote` i.e., `x IN UNIV` means `x` is of type `:vote`.
- `IN_INSERT`: This lemma describes the membership of an element in a set formed by inserting an element into another set.
- `NOT_IN_EMPTY`: This lemma states that no element is a member of the empty set.
- `vote_CASES`: This is most likely a case analysis rule that states that an arbitrary `x` is of type `:vote` (a member of the carrier set of `:vote`) if and only if `x = A` or `x = B`.

The combination of these rewrite rules establishes the equality between the type `:vote` and the set `{A, B}`, presumably by showing that they have the same members.

### Mathematical insight
The theorem formally establishes that the type `:vote` is equivalent to the set consisting of the two elements `A` and `B`. This likely means that `:vote` is a type that represents a choice between two alternatives.

### Dependencies
- `EXTENSION`
- `IN_UNIV`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `vote_CASES`


---

## ADD1_NOT_IN_NUMSEG

### Name of formal statement
ADD1_NOT_IN_NUMSEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ADD1_NOT_IN_NUMSEG = prove
 (`!m n. ~((n + 1) IN m..n)`,
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `m` and `n`, it is not the case that `n + 1` is an element of the set of natural numbers from `m` up to `n` (inclusive).

### Informal sketch
The proof proceeds by:
- Rewriting using the definition of `IN_NUMSEG`. This expands `x IN m..n` to `m <= x /\ x <= n`.
- Applying arithmetic tactics (`ARITH_TAC`) to prove the resulting goal `!m n. ~ (m <= n + 1 /\ n + 1 <= n)`. The arithmetic tactic automatically proves that the implication `n+1 <= n` is false.

### Mathematical insight
The theorem states that `n+1` cannot be in the set `{m, m+1, ..., n}`. This is because if `n+1` is in this set, it must be less than or equal to `n`, which is impossible for natural numbers. It highlights the discrete nature of natural numbers and their ordering.

### Dependencies
- Definitions: `IN_NUMSEG`

### Porting notes (optional)
The automation via `ARITH_TAC` may need to be replicated via a suitable arithmetic decision procedure in other systems. Be aware of built-in arithmetic capabilities when porting this proof to other provers.


---

## NUMSEG_1_CLAUSES

### Name of formal statement
NUMSEG_1_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMSEG_1_CLAUSES = prove
 (`!n. 1..(n+1) = (n + 1) INSERT (1..n)`,
  REWRITE_TAC[GSYM ADD1; NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`]);;
```
### Informal statement
For all natural numbers `n`, the set of natural numbers from 1 to `n+1` is equal to the set obtained by inserting `n+1` into the set of natural numbers from 1 to `n`.

### Informal sketch
The proof proceeds as follows:
- The goal is `!n. 1..(n+1) = (n + 1) INSERT (1..n)`.
- The proof starts by rewriting using `GSYM ADD1`. Here `ADD1` is the theorem that `(m :num) + 1 = SUC m`, i.e., addition of one equals successor. Hence, we rewrite `n+1` with `SUC n` in a reverse direction.
- Further rewriting using `NUMSEG_CLAUSES` unfolds the definition of `1..(SUC n)` as `(1..n) UNION {SUC n}`.
- Finally, we use `ARITH_RULE` to prove `1 <= SUC n`, which discharges the goal. Specifically, `ARITH_RULE` can automatically prove arithmetic facts such as `1 <= SUC n.`

### Mathematical insight
This theorem provides a recursive characterization of the set of natural numbers from 1 to `n`. It states that to get the numbers from 1 to `n+1`, we can simply take the numbers from 1 to `n` and add `n+1` to the set. This is a fundamental property used in inductive proofs and reasoning about natural numbers.

### Dependencies
- Theorems:
  - `ADD1`
  
- Definitions:
  - `NUMSEG_CLAUSES`


---

## NUMSEG_RESTRICT_SUC

### Name of formal statement
NUMSEG_RESTRICT_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMSEG_RESTRICT_SUC = prove
 (`{i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then (n + 1) INSERT {i | i IN 1..n /\ P i}
        else {i | i IN 1..n /\ P i}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; NUMSEG_1_CLAUSES; IN_INSERT] THEN
  ASM_MESON_TAC[ADD1_NOT_IN_NUMSEG]);;
```

### Informal statement
For any set `P` of natural numbers and any natural number `n`, the set of natural numbers `i` such that `i` is in the range from 1 to `n+1` and `P(i)` holds is equal to: if `P(n+1)` holds, then the set consisting of `n+1` inserted into the set of natural numbers `i` such that `i` is in the range from 1 to `n` and `P(i)` holds; otherwise, the set of natural numbers `i` such that `i` is in the range from 1 to `n` and `P(i)` holds.

### Informal sketch
The proof proceeds by induction on `n`.
- Base Case: Automatically handled by conditional case splitting since the condition `P(n + 1)` is either true or false.
- Inductive Step: Assume the theorem holds for `n`. We must show that it holds for `n+1`. The proof proceeds by cases based on whether `P(n+1)` holds:
  - Case 1: `P(n+1)` holds. The set `{i | i IN 1..(n+1+1) /\ P i}` is rewritten to `(n+1+1) INSERT {i | i IN 1..(n+1) /\ P i}` and, by the inductive hypothesis, to `(n+1+1) INSERT (if P(n + 1) then (n + 1) INSERT {i | i IN 1..n /\ P i} else {i | i IN 1..n /\ P i})`. Since we are in the case `P(n+1)`, this last is simplified to `(n+1+1) INSERT ((n + 1) INSERT {i | i IN 1..n /\ P i})`.
  - Case 2: `P(n+1)` does not hold. The set `{i | i IN 1..(n+1+1) /\ P i}` is equivalent to `{ i | i IN 1..(n+1) /\ P i}`.

The proof uses rewriting with definitions of set equality (`EXTENSION`), the elimination rule for set membership (`IN_ELIM_THM`), properties of the range `1..n` (`NUMSEG_1_CLAUSES`), and membership in an insertion (`IN_INSERT`), as well as resolution with `ADD1_NOT_IN_NUMSEG`, which states that n+1 is not in the range 1..n.

### Mathematical insight
This theorem describes how to restrict the indexing set `1..(n+1)` with predicate `P`. It decomposes the range `1..(n+1)` into the range `1..n` and the single element `n+1`. Based on the condition `P (n+1)`, it decides whether to include `n+1` or not in the filtered set. This is a common pattern when reasoning about inductive properties on sets defined over ranges.

### Dependencies
- Theorems: `EXTENSION`, `IN_ELIM_THM`, `IN_INSERT`, `ADD1_NOT_IN_NUMSEG`
- Definitions: `NUMSEG_1_CLAUSES`


---

## CARD_NUMSEG_RESTRICT_SUC

### Name of formal statement
CARD_NUMSEG_RESTRICT_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_NUMSEG_RESTRICT_SUC = prove
 (`CARD {i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then CARD {i | i IN 1..n /\ P i} + 1
        else CARD {i | i IN 1..n /\ P i}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMSEG_RESTRICT_SUC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_ELIM_THM; ADD1_NOT_IN_NUMSEG; ADD1]);;
```

### Informal statement
The cardinality of the set of elements `i` such that `i` is in the integer interval from 1 to `n + 1` and `P(i)` holds, is equal to the following: if `P(n + 1)` holds, then it is the cardinality of the set of elements `i` such that `i` is in the integer interval from 1 to `n` and `P(i)` holds, plus 1; otherwise, it is the cardinality of the set of elements `i` such that `i` is in the integer interval from 1 to `n` and `P(i)` holds.

### Informal sketch
The proof proceeds by:
- Applying `NUMSEG_RESTRICT_SUC` to split the set `{i | i IN 1..(n+1) /\ P i}` into the set `{i | i IN 1..n /\ P i}` and the element `n+1`.
- Performing a case split on whether `P(n + 1)` holds.
- Simplifying using `CARD_CLAUSES`, `FINITE_RESTRICT`, and `FINITE_NUMSEG`.
- Rewriting using `IN_ELIM_THM`, `ADD1_NOT_IN_NUMSEG`, and `ADD1`.

### Mathematical insight
This theorem provides a recursive way to compute the cardinality of a set restricted to a numerical interval. It reduces the problem to computing the cardinality of a smaller interval and checking a condition on the endpoint. This is useful for inductive proofs about cardinalities of sets defined over intervals.

### Dependencies
- Theorems: `NUMSEG_RESTRICT_SUC`, `CARD_CLAUSES`, `FINITE_RESTRICT`, `FINITE_NUMSEG`, `IN_ELIM_THM`, `ADD1_NOT_IN_NUMSEG`, `ADD1`


---

## FORALL_RANGE_SUC

### Name of formal statement
FORALL_RANGE_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FORALL_RANGE_SUC = prove
 (`(!i. 1 <= i /\ i <= n + 1 ==> P i) <=>
      P(n + 1) /\ (!i. 1 <= i /\ i <= n ==> P i)`,
  REWRITE_TAC[ARITH_RULE `i <= n + 1 <=> i <= n \/ i = n + 1`] THEN
  MESON_TAC[ARITH_RULE `1 <= n + 1`]);;
```
### Informal statement
For all `n`, the statement that `P(i)` holds for all `i` such that `1 <= i` and `i <= n + 1` is equivalent to the conjunction of `P(n + 1)` and the statement that `P(i)` holds for all `i` such that `1 <= i` and `i <= n`.

### Informal sketch
The proof proceeds as follows:

- First, rewrite the condition `i <= n + 1` as `i <= n \/ i = n + 1` using the arithmetic rule `i <= n + 1 <=> i <= n \/ i = n + 1`.
- Then, use a MESON-based automatic proof search, utilizing the arithmetic rule `1 <= n + 1`, to establish the equivalence.

### Mathematical insight
This theorem provides a way to decompose a universally quantified statement over a range up to `n + 1` into a statement about `n + 1` and a universally quantified statement over a range up to `n`. This is a standard technique for inductive proofs or recursive definitions where a property or function is defined in terms of its value at smaller inputs.

### Dependencies
- Arithmetic Rules: `i <= n + 1 <=> i <= n \/ i = n + 1`, `1 <= n + 1`


---

## IN_NUMSEG_RESTRICT_FALSE

### Name of formal statement
IN_NUMSEG_RESTRICT_FALSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IN_NUMSEG_RESTRICT_FALSE = prove
 (`m <= n
   ==> (i IN 1..m /\ (if i = n + 1 then p i else q i) <=> i IN 1..m /\ q i)`,
  REWRITE_TAC[IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `i <= m /\ m <= n ==> ~(i = n + 1)`]);;
```
### Informal statement
If `m` is less than or equal to `n`, then `i` is in the inclusive integer range from 1 to `m` and, if `i` equals `n + 1` then `p i` else `q i`, if and only if `i` is in the inclusive integer range from 1 to `m` and `q i`.

### Informal sketch
- The proof starts by rewriting using the definition of `IN_NUMSEG`.
- The proof uses the fact that if `i` is less than or equal to `m` and `m` is less than or equal to `n`, then `i` cannot be equal to `n + 1`. Thus, the `if` condition is always false and `q i` is always selected.

### Mathematical insight
The statement asserts that when considering a subrange `1..m` of `1..n`, the condition `i = n + 1` is always false for any `i` within the subrange `1..m`. Therefore, the conditional expression reduces to simply `q i` within that subrange.

### Dependencies
- Definitions:
    - `IN_NUMSEG`
- Theorems:
    - `ARITH_RULE i <= m /\ m <= n ==> ~(i = n + 1)`


---

## CARD_NUMSEG_RESTRICT_EXTREMA

### Name of formal statement
CARD_NUMSEG_RESTRICT_EXTREMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_NUMSEG_RESTRICT_EXTREMA = prove
 (`(CARD {i | i IN 1..n /\ P i} = n <=> !i. 1 <= i /\ i <= n ==> P i) /\
   (CARD {i | i IN 1..n /\ P i} = 0 <=> !i. 1 <= i /\ i <= n ==> ~(P i))`,
  SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL [`{i | i IN 1..n /\ P i}`; `1..n`] SUBSET_CARD_EQ) THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; CARD_NUMSEG_1] THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_NUMSEG; IN_ELIM_THM] THEN
  MESON_TAC[]);;
```
### Informal statement
For any predicate `P` on natural numbers and any natural number `n`, the cardinality of the set of natural numbers `i` such that `i` is in the range `1` to `n` inclusive and `P(i)` holds is equal to `n` if and only if for all `i`, if `i` is in the range `1` to `n` inclusive, then `P(i)` holds; and the cardinality of the set of natural numbers `i` such that `i` is in the range `1` to `n` inclusive and `P(i)` holds is equal to `0` if and only if for all `i`, if `i` is in the range `1` to `n` inclusive, then `P(i)` does not hold.

### Informal sketch
The proof proceeds as follows:
- Start by using simplifications with `CARD_EQ_0`, `FINITE_RESTRICT`, and `FINITE_NUMSEG`.
- Then specialize the theorem `SUBSET_CARD_EQ` to the set `{i | i IN 1..n /\ P i}` and `1..n` and use Modus Ponens.
- Then use simplifications with `FINITE_NUMSEG`, `SUBSET`, `IN_ELIM_THM`, and `CARD_NUMSEG_1`.
- Discharge the assumptions using `K ALL_TAC`.
- Rewrite using `EXTENSION`,`NOT_IN_EMPTY`,`IN_NUMSEG`, `IN_ELIM_THM`.
- Call MESON to complete the proof.

### Mathematical insight
This theorem provides a characterization of when the cardinality of a set defined by restricting the natural numbers from 1 to `n` inclusive using a predicate `P` equals `n` or `0`. It essentially states that the cardinality is `n` if and only if the predicate `P` holds for every number in the range, and the cardinality is `0` if and only if the predicate `P` does not hold for any number in the range. This is an important connection between cardinality and universal quantification over a restricted range of natural numbers.

### Dependencies
- `CARD_EQ_0`
- `FINITE_RESTRICT`
- `FINITE_NUMSEG`
- `SUBSET_CARD_EQ`
- `SUBSET`
- `IN_ELIM_THM`
- `CARD_NUMSEG_1`
- `EXTENSION`
- `NOT_IN_EMPTY`
- `IN_NUMSEG`


---

## VOTE_NOT_EQ

### Name of formal statement
VOTE_NOT_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VOTE_NOT_EQ = prove
 (`(!x. ~(x = A) <=> x = B) /\
   (!x. ~(x = B) <=> x = A)`,
  MESON_TAC[vote_CASES; vote_DISTINCT]);;
```

### Informal statement
For all `x`, `x` is not equal to `A` if and only if `x` is equal to `B`, and for all `x`, `x` is not equal to `B` if and only if `x` is equal to `A`.

### Informal sketch
The theorem is proved using the tactic `MESON_TAC` with the hints `vote_CASES` and `vote_DISTINCT`. This indicates that the proof likely relies on case splitting based on the possible values of `x` (presumably either `A` or `B`) and using the distinctness of `A` and `B`.

*   The statement breaks down into two universally quantified biconditionals.
*   The proof probably utilizes the assumption that `A` and `B` are the only possible values for `x`, covered by hint `vote_CASES`, which allows case splitting on `x = A` and `x = B`.
*   The distinctness assumption `vote_DISTINCT` (i.e., `A` is not equal to `B`) is essential to prove the biconditionals. For example, if `x = A`, then since `A` is not `B`, it follows that `x` is not equal to `B`.

### Mathematical insight
This theorem captures the fact that if there are only two distinct alternatives, `A` and `B`, then not being `A` is equivalent to being `B`, and vice-versa. It establishes a fundamental property of a two-element set.

### Dependencies
- Theorems/Definitions: `vote_CASES`, `vote_DISTINCT`

### Porting notes (optional)
The `MESON_TAC` tactic in HOL Light is an automated theorem prover. When porting, one may need to manually perform the case splits and apply the distinctness assumption. The key is to ensure that the porting environment knows that only two distinct values exist as defined from `vote_CASES` and `vote_DISTINCT`.


---

## FUNSPACE_FIXED

### Name of formal statement
FUNSPACE_FIXED

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FUNSPACE_FIXED = prove
 (`{f | f IN (s --> t) /\ (!i. i IN s ==> f i = a)} =
   if s = {} \/ a IN t then {(\i. if i IN s then a else @x. T)} else {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN GEN_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; funspace; NOT_IN_EMPTY; IN_SING] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;
```

### Informal statement
The set of functions from `s` to `t` such that for all `i` in `s`, `f i` equals `a`, is equal to the singleton set containing the function that maps `i` to `a` if i is in `s` and to an arbitrary element from the type of x otherwise, if and only if `s` is empty or `a` is in `t`; otherwise the set is empty.

### Informal sketch
The proof proceeds by showing the equality of two sets. The main steps are:

- First, rewrite the initial goal using `EXTENSION` (set extensionality) and `NOT_IN_EMPTY`.
- Apply `GEN_TAC` to introduce a variable `f` and assume it's a member of the set on the left-hand side.
- Perform case splitting on the condition `s = {} \/ a IN t`.
- In each case, rewrite using `IN_ELIM_THM`, `funspace`, `NOT_IN_EMPTY`, `IN_SING`. These rewrites simplify the membership conditions and function space definitions.
- Apply `REWRITE_TAC[FUN_EQ_THM]` to introduce function equality.
- Finally, use `ASM_MESON_TAC[]` to complete the proof automatically, discharging any remaining assumptions.

### Mathematical insight
This theorem characterizes a specific subset of the function space `s --> t`. It identifies the conditions under which the set of functions from `s` to `t` that are constantly equal to `a` on `s` is non-empty.  The key idea is that if `s` is empty, any function from `s` to `t` satisfies the condition, and if `s` is non-empty, then `a` must be an element of `t` for such a function to exist.

### Dependencies
- Theorems: `EXTENSION`, `NOT_IN_EMPTY`, `IN_ELIM_THM`, `funspace`, `IN_SING`, `FUN_EQ_THM`


---

## COUNTING_LEMMA

### Name of formal statement
COUNTING_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COUNTING_LEMMA = prove
 (`CARD {f | f IN (1..(n+1) --> {A,B}) /\ P f} =
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then A else f i)} +
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then B else f i)}`,
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = A /\ P f} +
              CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = B /\ P f}` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    REWRITE_TAC[FINITE_COUNTINGS; EXTENSION; IN_INTER; IN_UNION] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[vote_CASES; vote_DISTINCT];
    ALL_TAC] THEN
  BINOP_TAC THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  EXISTS_TAC `\f i. if i = n + 1 then @x:vote. T else f i` THENL
   [EXISTS_TAC `\f i. if i = n + 1 then A else f i`;
    EXISTS_TAC `\f i. if i = n + 1 then B else f i`] THEN
  REWRITE_TAC[FINITE_COUNTINGS] THEN
  REWRITE_TAC[IN_ELIM_THM; funspace; GSYM UNIV_VOTE; IN_UNIV] THEN
  REWRITE_TAC[NUMSEG_1_CLAUSES; IN_INSERT] THEN REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `P x ==> x = y ==> P y`))) THEN
  TRY(GEN_REWRITE_TAC I [FUN_EQ_THM]) THEN ASM_MESON_TAC[ADD1_NOT_IN_NUMSEG]);;  
```

### Informal statement
Given a set of functions from `1..(n+1)` to `{A, B}`, and a predicate `P` on these functions, the cardinality of the subset of these functions that satisfy `P` is equal to the sum of the cardinalities of two subsets of functions from `1..n` to `{A, B}`.  The first subset consists of functions `f` such that `P` holds for the function `g` from `1..(n+1)` to `{A, B}` where `g(i) = A` if `i = n+1` and `g(i) = f(i)` otherwise.  The second subset is defined similarly, but with `g(i) = B` if `i = n+1`.

### Informal sketch
- First, prove that the set `{f | f IN (1..(n+1) --> {A,B}) /\ P f}` can be partitioned into two disjoint sets based on the value of `f(n+1)`. That is, `{f | f IN (1..(n+1) --> {A,B}) /\ P f}` is equal to the union of `{f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = A /\ P f}` and `{f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = B /\ P f}`. This uses `CARD_UNION_EQ` and rewriting rules related to set membership (`IN_INTER`, `IN_UNION`, `IN_ELIM_THM`, `NOT_IN_EMPTY`), finiteness of countings (`FINITE_COUNTINGS`), extensionality (`EXTENSION`) and predicates on votes (`vote_CASES`, `vote_DISTINCT`).

- Next, show that the function spaces `1..n --> {A,B}` and `{f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = A}` (and similarly for B) are in bijection.  This uses `BIJECTIONS_CARD_EQ`. Specifically, a bijection is established between `1..n --> {A, B}` and `{f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = A /\ P f}` with the function `\f i. if i = n + 1 then @x:vote. T else f i`.

- Finally, apply rewriting steps with `FINITE_COUNTINGS`, `IN_ELIM_THM`, `funspace`, `UNIV_VOTE`, `IN_UNIV`, `NUMSEG_1_CLAUSES`, and `IN_INSERT` to simplify the set membership conditions.  Use assumptions to simplify where possible, and apply `FUN_EQ_THM` for functional equality.

### Mathematical insight
This theorem decomposes the problem of counting functions of type `1..(n+1) --> {A,B}` satisfying property `P` into two smaller counting problems based on the value of the function at `n+1`. It provides a recursive approach for counting such functions, which is standard in combinatorics and discrete mathematics.

### Dependencies

**Theorems:**
- `CARD_UNION_EQ`
- `BIJECTIONS_CARD_EQ`
- `FUN_EQ_THM`
- `IN_ELIM_THM`
- `NOT_IN_EMPTY`

**Definitions/Axioms:**
- `FINITE_COUNTINGS`
- `EXTENSION`
- `IN_INTER`
- `IN_UNION`
- `vote_CASES`
- `vote_DISTINCT`
- `funspace`
- `UNIV_VOTE`
- `IN_UNIV`
- `NUMSEG_1_CLAUSES`
- `IN_INSERT`
- `ADD1_NOT_IN_NUMSEG`

### Porting notes (optional)
The key would be ensuring how the target proof assistant deals with dependent types, function spaces, cardinality, and the construction of bijections. The definitions of set membership and cardinalities would need to be verified in the target system to ensure consistency.


---

## ALL_COUNTINGS_0

### Name of formal statement
ALL_COUNTINGS_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALL_COUNTINGS_0 = prove
 (`!a. all_countings a 0 = 1 /\ all_countings 0 a = 1`,
  REWRITE_TAC[all_countings; CARD_NUMSEG_RESTRICT_EXTREMA; GSYM IN_NUMSEG;
              LET_DEF; LET_END_DEF; ADD_CLAUSES; VOTE_NOT_EQ] THEN
  REWRITE_TAC[FUNSPACE_FIXED; IN_INSERT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH_SUC]);;
```

### Informal statement
For all `a`, `all_countings a 0 = 1` and for all `a`, `all_countings 0 a = 1`.

### Informal sketch
The proof proceeds by rewriting with the definition of `all_countings`, `CARD_NUMSEG_RESTRICT_EXTREMA`, `GSYM IN_NUMSEG`, `LET_DEF`, `LET_END_DEF`, `ADD_CLAUSES`, and `VOTE_NOT_EQ`. Then rewriting with simplification rules related to functions in a function space (`FUNSPACE_FIXED`) and `IN_INSERT` is performed. Finally, simplifying with cardinality clauses (`CARD_CLAUSES`), finiteness rules (`FINITE_RULES`), the fact that something is not in the empty set (`NOT_IN_EMPTY`) and arithmetic simplification (`ARITH_SUC`) completes the proof.

### Mathematical insight
This theorem establishes the base cases for the `all_countings` function when either the number of candidates or the number of votes is zero. It states that if there are no votes (`0`), there is only one way to count the votes i.e. assign no vote to any of the candidates. Similarly, if there are no candidates (`0`), there is one way to count i.e assign any votes anywhere from existing candidates to no candidates.

### Dependencies
- Definitions: `all_countings`, `LET_DEF`, `LET_END_DEF`, `ADD_CLAUSES`, `VOTE_NOT_EQ`
- Theorems/Lemmas: `CARD_NUMSEG_RESTRICT_EXTREMA`, `GSYM IN_NUMSEG`, `FUNSPACE_FIXED`, `IN_INSERT`, `CARD_CLAUSES`, `FINITE_RULES`, `NOT_IN_EMPTY`, `ARITH_SUC`


---

## VALID_COUNTINGS_0

### Name of formal statement
VALID_COUNTINGS_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VALID_COUNTINGS_0 = prove
 (`valid_countings 0 0 = 1 /\
   !a. valid_countings (SUC a) 0 = 1 /\ valid_countings 0 (SUC a) = 0`,
  let lemma = prove
   (`{x} INTER s = if x IN s then {x} else {}`,
    COND_CASES_TAC THEN ASM SET_TAC[]) in
  REWRITE_TAC[valid_countings; CARD_NUMSEG_RESTRICT_EXTREMA; GSYM IN_NUMSEG;
              LET_DEF; LET_END_DEF; ADD_CLAUSES; VOTE_NOT_EQ;
              TAUT `a /\ a /\ b <=> a /\ b`] THEN
  REWRITE_TAC[CONJUNCT1 NUMSEG_CLAUSES; ARITH_EQ; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[funspace; IN_ELIM_THM; NOT_IN_EMPTY; GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `{x | P x /\ Q x /\ R x} =
                             {x | P x /\ Q x} INTER {x | R x}`] THEN
  REWRITE_TAC[FUNSPACE_FIXED; IN_INSERT; lemma] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_TAC THEN CONJ_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `b = 0 /\ ~(a = 0) ==> a > b`) THEN
    ASM_SIMP_TAC[CARD_NUMSEG_RESTRICT_EXTREMA] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `1 <= k /\ k <= a ==> 1 <= k /\ !i. i <= k ==> i <= a`)) THEN
    ASM_SIMP_TAC[IN_NUMSEG; vote_DISTINCT] THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    EXISTS_TAC `1` THEN REWRITE_TAC[NUMSEG_SING; IN_SING] THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC(ARITH_RULE `b = 0 /\ ~(a = 0) ==> ~(b > a)`) THEN
    ONCE_REWRITE_TAC[SET_RULE `{x | x = a /\ P x} = {x | x = a /\ P a}`] THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    SIMP_TAC[vote_DISTINCT; SET_RULE `{x | F} = {} /\ {x | x = a} = {a}`;
             CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH]]);;
```
### Informal statement
The theorem `VALID_COUNTINGS_0` states that:
1.  `valid_countings 0 0 = 1`.
2.  For all `a`, `valid_countings (SUC a) 0 = 1`.
3.  For all `a`, `valid_countings 0 (SUC a) = 0`.

### Informal sketch
The proof proceeds as follows:

*   First, rewrite the goal using definitions and simplification rules: `valid_countings`, `CARD_NUMSEG_RESTRICT_EXTREMA`, `IN_NUMSEG` (after generalization), LET definitions, `ADD_CLAUSES`, `VOTE_NOT_EQ`, and tautological equivalences.
*   Then, simplify further using `CONJUNCT1 NUMSEG_CLAUSES`, `ARITH_EQ`, and `NOT_IN_EMPTY`.
*   Then, split the conjunction into three subgoals and solve each one individually.
    *   The first subgoal involves rewriting with `funspace`, `IN_ELIM_THM`, `NOT_IN_EMPTY`, `FUN_EQ_THM`, `SET_RULE `{x | x = a} = {a}``, and simplification with cardinality rules, finiteness rules, and arithmetic.
    *   The second subgoal is solved automatically.
*   Then, rewrite using set intersection introduction, `FUNSPACE_FIXED`, and a simplifying lemma `{x} INTER s = if x IN s then {x} else {}`.
*   Further rewrite and generalization yield a goal suitable for conditional case splitting.
*   After case splitting proceed by automatic simplification using cardinality rules, finiteness rules, arithmetic.
*   Then eliminate one assumption and rewrite with a theorem for negation of forall quantified statement.
*   Then solve the subgoal by generalization, discharging assumption, matching and applying an arithmetic rule `b = 0 /\ ~(a = 0) ==> a > b`, and using assumptions and simplification rules for `CARD_NUMSEG_RESTRICT_EXTREMA`, `IN_NUMSEG`, `vote_DISTINCT`. Arithmetical reasoning, and discharging of assumptions finishes this part of goal.
*   In the final step existentially instantiate with `1`, rewrite with `NUMSEG_SING`, `IN_SING`, `IN_NUMSEG`, `LE_REFL`, `ARITH_RULE 1 <= SUC n`. Then use `b = 0 /\ ~(a = 0) ==> ~(b > a)` and `SET_RULE {x | x = a /\ P x} = {x | x = a /\ P a}`. The goal is finished using similar rules as earlier.

### Mathematical insight

The `valid_countings m n` function likely represents the number of ways to select `n` votes from a pool of numbered voters `1` to `m` such that each vote is distinct. The theorem `VALID_COUNTINGS_0` establishes base cases for this function:

1.  When there are no voters (`m = 0`) and zero votes are selected (`n = 0`), there is exactly one valid way to do this – selecting nothing.
2.  Regardless of how many voters there are (`m = SUC a`), there is always one way to select zero votes – selecting nothing.
3.  When there are no voters (`m = 0`) and a positive number of votes must be selected (`n = SUC a`), it is impossible, so there are zero valid ways.

These base cases are crucial for inductive proofs involving the `valid_countings` function.

### Dependencies

*   Definitions: `valid_countings`
*   Theorems: `CARD_NUMSEG_RESTRICT_EXTREMA`, `IN_NUMSEG`, `CONJUNCT1 NUMSEG_CLAUSES`, `ARITH_EQ`, `NOT_IN_EMPTY`, `funspace`, `IN_ELIM_THM`, `FUN_EQ_THM`, `SET_RULE `{x | x = a} = {a}`, `CARD_CLAUSES`, `FINITE_RULES`, `VOTE_NOT_EQ`, `FUNSPACE_FIXED`, `IN_INSERT`, `NOT_FORALL_THM`, `NUMSEG_SING`, `LE_REFL`, `SET_RULE `{x | x = a /\ P x} = {x | x = a /\ P a}``, `ADD_CLAUSES`, `vote_DISTINCT`, `vote_DISTINCT`
*   Rules: `ARITH_RULE b = 0 /\ ~(a = 0) ==> a > b`, `ARITH_RULE 1 <= SUC n`,
*   Tactics: `REWRITE_TAC`, `ASM_SIMP_TAC`, `ONCE_REWRITE_TAC`, `MP_TAC`, `MATCH_MP`, `MATCH_MP_TAC`, `TAUT`, `COND_CASES_TAC`, `COND_CASES_TAC`, `EXISTS_TAC`, `GEN_TAC`, `GEN_REWRITE_RULE`

### Porting notes (optional)

*   The proof relies heavily on rewriting and simplification with set theory and arithmetic rules. A target proof assistant needs similar automation capabilities, especially for arithmetic reasoning.
*   Pay close attention to how sets are represented in the target system, as this proof involves operations like intersection and checking membership.
*   HOL Light's tactic `COND_CASES_TAC` automatically performs case splitting based on conditional expressions. This might need to be done manually in other proof assistants.


---

## ALL_COUNTINGS_SUC

### Name of formal statement
ALL_COUNTINGS_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALL_COUNTINGS_SUC = prove
 (`!a b. all_countings (a + 1) (b + 1) =
                all_countings a (b + 1) + all_countings (a + 1) b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_countings] THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + (b + 1) = (a + b + 1) + 1`) THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + b = a + b + 1`) THEN
  ABBREV_TAC `n = a + b + 1` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [COUNTING_LEMMA] THEN
  REWRITE_TAC[] THEN BINOP_TAC THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[vote_DISTINCT] THEN
  REWRITE_TAC[CARD_NUMSEG_RESTRICT_SUC] THEN
  SIMP_TAC[IN_NUMSEG_RESTRICT_FALSE; LE_REFL; EQ_ADD_RCANCEL]);;
```
### Informal statement
For all natural numbers `a` and `b`, the number of countings of `a + 1` into `b + 1` is equal to the number of countings of `a` into `b + 1` plus the number of countings of `a + 1` into `b`.

### Informal sketch
The proof proceeds by induction and simplification using arithmetic reasoning and rewriting with lemmas about 'all_countings'.
- Rewrite using the definition of 'all_countings'.
- Simplify arithmetic expressions using `ARITH_RULE` to rewrite `(a + 1) + (b + 1)` as `(a + b + 1) + 1` and `(a + 1) + b` as `a + b + 1`.
- Introduce a variable `n` with the definition `n = a + b + 1`.
- Apply a conversion to simplify an `let` expression.
- Rewrite using the `COUNTING_LEMMA` and simplify.
- Apply a binary operation tactic and rewrite with lemmas such as `COND_RAND`, `COND_RATOR`, `vote_DISTINCT`, `CARD_NUMSEG_RESTRICT_SUC`.
- Simplify using theorems such as `IN_NUMSEG_RESTRICT_FALSE`, `LE_REFL` and `EQ_ADD_RCANCEL`.

### Mathematical insight
This theorem establishes a recurrence relation for the number of countings, expressing `all_countings (a+1) (b+1)` in terms of `all_countings a (b+1)` and `all_countings (a+1) b`. This is useful for computing or reasoning about counting numbers inductively.

### Dependencies
- Definition: `all_countings`
- Theorem: `COUNTING_LEMMA`
- Theorem: `vote_DISTINCT`
- Theorem: `CARD_NUMSEG_RESTRICT_SUC`
- Theorem: `IN_NUMSEG_RESTRICT_FALSE`


---

## VALID_COUNTINGS_SUC

### Name of formal statement
VALID_COUNTINGS_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VALID_COUNTINGS_SUC = prove
 (`!a b. valid_countings (a + 1) (b + 1) =
                if a <= b then 0
                else valid_countings a (b + 1) + valid_countings (a + 1) b`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `b:num < a` THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  REWRITE_TAC[valid_countings] THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + (b + 1) = (a + b + 1) + 1`) THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + b = a + b + 1`) THEN
  ABBREV_TAC `n = a + b + 1` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [COUNTING_LEMMA] THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[vote_DISTINCT] THEN
  REWRITE_TAC[FORALL_RANGE_SUC] THEN
  REWRITE_TAC[CARD_NUMSEG_RESTRICT_SUC] THEN
  SIMP_TAC[IN_NUMSEG_RESTRICT_FALSE; LE_REFL; EQ_ADD_RCANCEL] THEN
  SIMP_TAC[MESON[] `x = a /\ y = b /\ P x y <=> x = a /\ y = b /\ P a b`] THEN
  ASM_REWRITE_TAC[GT; LT_ADD_RCANCEL] THEN
  REWRITE_TAC[SET_RULE `{x | F} = EMPTY`; CARD_CLAUSES; ADD_CLAUSES]);;
```

### Informal statement
For all natural numbers `a` and `b`, `valid_countings (a + 1) (b + 1)` is equal to `0` if `a` is less than or equal to `b`; otherwise, it is equal to `valid_countings a (b + 1) + valid_countings (a + 1) b`.

### Informal sketch
The proof proceeds by induction on the relationship between `a` and `b`.

- First, the base case `b < a` is considered using `ASM_CASES_TAC`. This case uses the definition of `valid_countings` and arithmetic simplification.
- Substitution is applied using theorems `(a + 1) + (b + 1) = (a + b + 1) + 1` and `(a + 1) + b = a + b + 1`.
- An abbreviation `n = a + b + 1` is introduced to simplify further reasoning.
- Simplification and rewriting using combinatorial lemmas such as `COUNTING_LEMMA`, along with lemmas regarding `vote_DISTINCT`, `FORALL_RANGE_SUC`, and `CARD_NUMSEG_RESTRICT_SUC` are applied to transform the expression.
- Simplification steps related to sets are then performed involving rewrite rules such as `SET_RULE `{x | F} = EMPTY`; `CARD_CLAUSES`; and `ADD_CLAUSES`.
- Logical reasoning (using `MESON`) is employed to complete the proof.

### Mathematical insight
This theorem provides a recursive characterization of the `valid_countings` function when both arguments are incremented by 1. It essentially states that the number of valid countings for `(a+1, b+1)` can be computed recursively in terms of valid countings for `(a, b+1)` and `(a+1, b)`. This recurrence relation is crucial for computing the values of `valid_countings` function efficiently.

### Dependencies
- Definition: `valid_countings`
- Theorems: `GSYM NOT_LT`, `COUNTING_LEMMA`, `COND_RAND`, `COND_RATOR`, `vote_DISTINCT`, `FORALL_RANGE_SUC`, `CARD_NUMSEG_RESTRICT_SUC`, `IN_NUMSEG_RESTRICT_FALSE`, `LE_REFL`, `EQ_ADD_RCANCEL`, `GT`, `LT_ADD_RCANCEL`, `SET_RULE `{x | F} = EMPTY``, `CARD_CLAUSES`, `ADD_CLAUSES`


---

## ALL_COUNTINGS

### Name of formal statement
ALL_COUNTINGS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ALL_COUNTINGS = prove
 (`!a b. all_countings a b = binom(a + b,a)`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; BINOM_REFL; binom; ALL_COUNTINGS_0] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; BINOM_REFL; binom; ALL_COUNTINGS_0] THEN
  REWRITE_TAC[ARITH_RULE `1 = a + 1 <=> a = 0`; BINOM_EQ_0;
              ARITH_RULE `a < SUC a`] THEN
  REWRITE_TAC[ALL_COUNTINGS_SUC; ADD1] THEN
  ASM_REWRITE_TAC[binom; GSYM ADD1] THEN
  REWRITE_TAC[ADD_CLAUSES; ADD_AC]);;
```
### Informal statement
For all natural numbers `a` and `b`, `all_countings a b` is equal to `binom(a + b, a)`.

### Informal sketch
The theorem is proved by induction on `a` and then on `b`.

- Base case `a = 0`: The goal `all_countings 0 b = binom(0 + b, 0)` is proved by induction on `b`.
    - Base case `b = 0`: `all_countings 0 0 = binom(0 + 0, 0)` simplifies to `1 = 1`.
    - Inductive step for `b`: Assuming `all_countings 0 b = binom(0 + b, 0)` we must prove `all_countings 0 (SUC b) = binom(0 + SUC b, 0)`. This simplifies using the definition of `all_countings` and binomial coefficients, and using arithmetic reasoning.
- Inductive step for `a`: Assuming `all_countings a b = binom(a + b, a)` we must prove `all_countings (SUC a) b = binom(SUC a + b, SUC a)`. This is proved by induction on `b`.
    - Base case `b = 0`. We must show `all_countings (SUC a) 0 = binom(SUC a + 0, SUC a)`. This case requires rewriting with the definition of `all_countings`.
    - Inductive step for `b`: Assuming `all_countings (SUC a) b = binom(SUC a + b, SUC a)`, we must show `all_countings (SUC a) (SUC b) = binom(SUC a + SUC b, SUC a)`. This case requires rewriting with the definitions of `all_countings` and applying the inductive hypothesis, then using arithmetic.

### Mathematical insight
This theorem expresses a fundamental relationship between the `all_countings` function and binomial coefficients, likely connecting combinatorics of counting paths or arrangements with the algebraic properties of binomials.

### Dependencies

- Arithmetic: `ADD_CLAUSES; ARITH_RULE \`1 = a + 1 <=> a = 0\`; ARITH_RULE \`a < SUC a\`; ADD1; ADD_AC`
- Binomial coefficients: `BINOM_REFL; binom; BINOM_EQ_0`
- Main result: `ALL_COUNTINGS_0; ALL_COUNTINGS_SUC`

### Porting notes (optional)
The proof relies on inductive reasoning and rewriting with definitions of `all_countings` and binomial coefficients. The specific tactic `ASM_REWRITE_TAC` suggests that assumptions are used during rewriting.
One may need to ensure assumptions from the context are used during simplification or rewriting steps in other proof assistants. The HOL Light `ARITH_RULE` tactic is used to apply arithmetic reasoning, which might need to be replaced with equivalent tactics or manual proof steps in other systems.


---

## VALID_COUNTINGS

### Name of formal statement
VALID_COUNTINGS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VALID_COUNTINGS = prove
 (`!a b. (a + b) * valid_countings a b = (a - b) * binom(a + b,a)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[VALID_COUNTINGS_0; SUB_0; MULT_CLAUSES] THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[VALID_COUNTINGS_0; MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[VALID_COUNTINGS_0; ADD_CLAUSES; BINOM_REFL; SUB_0];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1; VALID_COUNTINGS_SUC] THEN REWRITE_TAC[GSYM ADD1] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ARITH_RULE `a <= b ==> SUC a - SUC b = 0`] THEN
  MATCH_MP_TAC(NUM_RING
   `~(a + b + 1 = 0) /\
    (SUC a + SUC b) *
    ((SUC a + b) * (a + SUC b) * y + (a + SUC b) * (SUC a + b) * z) =
    (SUC a + b) * (a + SUC b) * w
    ==> (SUC a + SUC b) * (y + z) = w`) THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH] THEN
  MP_TAC(SPECL [`SUC b`; `a:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`b:num`; `SUC a`] BINOM_FACT) THEN
  MP_TAC(SPECL [`SUC b`; `SUC a`] BINOM_FACT) THEN
  REWRITE_TAC[ADD_CLAUSES; FACT] THEN
  SUBST1_TAC(ARITH_RULE `b + a:num = a + b`) THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t FACT_LT))
   [`a:num`; `b:num`; `a + b:num`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
    GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_SUB; REAL_OF_NUM_LE; LT_NZ;
    ARITH_RULE `~(a <= b) ==> b <= SUC a /\ SUC b <= a /\ SUC b <= SUC a`] THEN
  CONV_TAC REAL_RING);;
```
### Informal statement
For all natural numbers `a` and `b`, `(a + b) * valid_countings a b = (a - b) * binom(a + b, a)`.

### Informal sketch
The proof proceeds by induction on `a` and `b`.

- Base case 1: Induction on `a`.
  - Sub-base case: `a = 0`. Simplify using `VALID_COUNTINGS_0`, `SUB_0`, and `MULT_CLAUSES`.
  - Inductive step: Assume the theorem holds for `a`. Show that it holds for `SUC a`, using `VALID_COUNTINGS_0`, `MULT_CLAUSES`, and `ADD_CLAUSES`.
- Base case 2: Induction on `b`.
  - Sub-base case: `b = 0`. Simplify using `VALID_COUNTINGS_0`, `ADD_CLAUSES`, `BINOM_REFL`, and `SUB_0`.
  - Inductive Step.
- The main induction is followed by rewriting with `ADD1` and `VALID_COUNTINGS_SUC`, and rewriting again with `GSYM ADD1`.
- `COND_CASES_TAC` introduces a case split.
- Simplify the cases using arithmetic (`a <= b ==> SUC a - SUC b = 0`) and ring properties to eliminate the conditional.
- Apply `BINOM_FACT` three times with suitable instantiations.
- Rewrite using `ADD_CLAUSES` and `FACT`.
- Use `SUBST1_TAC` with commutativity of addition.
- Use `FACT_LT` via `MAP_EVERY` on `a`, `b` and `a + b`.
- Simplify with ring conversion and arithmetic rules to complete the proof.

### Mathematical insight
The theorem establishes a relationship between `valid_countings a b` and the binomial coefficient `binom(a + b, a)`. The function `valid_countings a b` likely represents a combinatorial counting such as the number of ways to reach the point (a,b) on a discrete grid and the theorem says that this number can be deduced by analyzing the difference between `a` and `b` and the number of paths via the binomial theorem.

### Dependencies
- `VALID_COUNTINGS_0`
- `SUB_0`
- `MULT_CLAUSES`
- `ADD_CLAUSES`
- `BINOM_REFL`
- `ADD1`
- `VALID_COUNTINGS_SUC`
- `ADD_EQ_0`
- `BINOM_FACT`
- `FACT`
- `FACT_LT`
- `REAL_OF_NUM_EQ`
- `REAL_OF_NUM_MUL`
- `REAL_OF_NUM_ADD`
- `REAL_OF_NUM_SUC`
- `REAL_OF_NUM_SUB`
- `REAL_OF_NUM_LE`
- `LT_NZ`


---

## BALLOT

### Name of formal statement
BALLOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let BALLOT = prove
 (`!a b. &(valid_countings a b) =
            if a <= b then if b = 0 then &1 else &0
            else (&a - &b) / (&a + &b) *  &(all_countings a b)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[ALL_COUNTINGS_0; VALID_COUNTINGS_0] THEN
  REWRITE_TAC[LE_REFL; REAL_MUL_LID; LE_0; NOT_SUC; CONJUNCT1 LE] THEN
  SIMP_TAC[REAL_ADD_RID; REAL_SUB_RZERO; REAL_DIV_REFL; REAL_OF_NUM_EQ;
           NOT_SUC; REAL_MUL_LID] THEN
  MP_TAC(SPECL [`SUC a`; `SUC b`] VALID_COUNTINGS) THEN
  REWRITE_TAC[GSYM ALL_COUNTINGS; LE_SUC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> (SUC a - SUC b) = 0`] THEN
  REWRITE_TAC[MULT_EQ_0; MULT_CLAUSES; ADD_EQ_0; NOT_SUC; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
               GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_SUB;
               ARITH_RULE `~(a <= b) ==> SUC b <= SUC a`] THEN
  CONV_TAC REAL_FIELD);;
```
### Informal statement
For all natural numbers `a` and `b`, `&(valid_countings a b)` is equal to: if `a` is less than or equal to `b`, then if `b` is equal to 0 then `&1` else `&0`; otherwise, `(&a - &b) / (&a + &b) * &(all_countings a b)`.

### Informal sketch
The proof proceeds by induction, using the tactic `REPEAT INDUCT_TAC`.
- **Base Case:** The base case involves showing the property holds when both `a` and `b` are 0. Simplification using `ALL_COUNTINGS_0` and `VALID_COUNTINGS_0` reduces both sides of the equality to 1, thus proving the base case. Further simplifications using arithmetic properties such as `LE_REFL`, `REAL_MUL_LID`, `LE_0`, `NOT_SUC` are applied.
- **Inductive Step:** The main part of the proof handles the inductive step. First, the theorem `VALID_COUNTINGS` is specialized to `SUC a` and `SUC b`. Then, the definition of `ALL_COUNTINGS` is rewritten using `GSYM ALL_COUNTINGS`, and `LE_SUC` is used. Conditional cases are then considered using `COND_CASES_TAC`. Arithmetic simplifications such as: `a <= b ==> (SUC a - SUC b) = 0`, `MULT_EQ_0`, `MULT_CLAUSES`, `ADD_EQ_0`, `NOT_SUC`, `REAL_OF_NUM_EQ`, `GSYM REAL_OF_NUM_MUL`, `GSYM REAL_OF_NUM_ADD`, `GSYM REAL_OF_NUM_SUC`, `GSYM REAL_OF_NUM_SUB` and `~(a <= b) ==> SUC b <= SUC a` are applied using `ASM_SIMP_TAC`. Finally, the `REAL_FIELD` tactic is used to complete the proof, which involves simplification of real arithmetic expressions.

### Mathematical insight
The theorem relates the number of valid countings (`valid_countings`) to the total number of possible countings (`all_countings`) in a ballot problem. The ballot problem states that in an election where candidate A receives `a` votes and candidate B receives `b` votes, with `a > b`, the probability that A is always strictly ahead of B throughout the counting process. The term `(a - b) / (a + b)` represents the probability that A is always strictly ahead of B during the counting.

### Dependencies
- Definitions: `ALL_COUNTINGS_0`, `VALID_COUNTINGS_0`, `ALL_COUNTINGS`, `VALID_COUNTINGS`
- Theorems: `LE_REFL`, `REAL_MUL_LID`, `LE_0`, `NOT_SUC`, `CONJUNCT1 LE`, `REAL_ADD_RID`, `REAL_SUB_RZERO`, `REAL_DIV_REFL`, `REAL_OF_NUM_EQ`, `LE_SUC`, `MULT_EQ_0`, `MULT_CLAUSES`, `ADD_EQ_0`
- Rules: `ARITH_RULE`
- Tactics: `REAL_FIELD`


---

