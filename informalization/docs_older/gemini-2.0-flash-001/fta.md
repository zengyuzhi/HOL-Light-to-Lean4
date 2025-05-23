# fta.ml

## Overview

Number of statements: 10

`fta.ml` formalizes the fundamental theorem of arithmetic, also known as the unique prime factorization theorem. It relies on definitions and theorems from the `prime.ml` library regarding prime numbers. The file likely contains definitions related to factorization and primality, culminating in the proof of the unique prime factorization theorem.


## nproduct

### Name of formal statement
- nproduct

### Type of the formal statement
- new_definition

### Formal Content
```ocaml
let nproduct = new_definition `nproduct = iterate ( * )`;;
```

### Informal statement
- The iterated product `nproduct` is defined as the result of applying the multiplication operation `(*)` iteratively.

### Informal sketch
- The definition of `nproduct` is given directly by using the function `iterate` with the multiplication operator `(*)` as the combining function. Thus, `nproduct f n` will compute `f(0) * f(1) * ... * f(n-1)`.

### Mathematical insight
- This definition provides a concise way to express the product of a sequence of numbers. It's analogous to the summation operator, but for multiplication. This is a fundamental building block for many number-theoretic results. The iterated product is useful for expressing factorials, products of primes, and other constructs within number theory.

### Dependencies
- Definitions:
  - `iterate`


---

## NPRODUCT_CLAUSES

### Name of formal statement
NPRODUCT_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_CLAUSES = prove
 (`(!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_MUL]);;
```
### Informal statement
For all functions `f`, the product of `f` over the empty set is equal to 1.
Furthermore, for all `x`, `f`, and finite sets `s`, if `s` is finite, then the product of `f` over the set `x INSERT s` is equal to the product of `f(x)` and the product of `f` over `s`, provided that `x` is not an element of `s`; otherwise, it equals the product of `f` over `s`.

### Informal sketch
The proof aims to establish the base case for the empty set and the inductive step for inserting an element into a finite set.
-  The proof starts by rewriting using the definition of `nproduct` and the symmetry of `NEUTRAL_MUL` (i.e., rewriting `1 = nproduct {} f` to `nproduct {} f = 1`).
- The quantifier is moved inwards using `SWAP_FORALL_THM`.
- The proof uses `ITERATE_CLAUSES`, which takes the clauses from the current theorem (in this case, the clauses that define `nproduct`) and makes them available.
- Finally, the proof rewrites using `MONOIDAL_MUL`, which probably simplifies multiplication expressions within the `nproduct`.

### Mathematical insight
This theorem provides the defining clauses for the `nproduct` function, specifying how to compute the product of a function over a finite set. The first part asserts that the product over the empty set is the multiplicative identity (1). The second part offers a recursive definition, showing how to compute the product when a new element is added to the set.

### Dependencies
- `nproduct`
- `GSYM`
- `NEUTRAL_MUL`
- `SWAP_FORALL_THM`
- `ITERATE_CLAUSES`
- `MONOIDAL_MUL`
- `FINITE`
- `INSERT`
- `IN`


---

## NPRODUCT_EQ_1_EQ

### Name of formal statement
NPRODUCT_EQ_1_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_EQ_1_EQ = prove
 (`!s f. FINITE s ==> (nproduct s f = 1 <=> !x. x IN s ==> f(x) = 1)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT; MULT_EQ_1; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;
```
### Informal statement
For all sets `s` and functions `f`, if `s` is finite, then the product of `f(x)` over all `x` in `s` is equal to 1 if and only if for all `x`, if `x` is in `s`, then `f(x)` is equal to 1.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `s`.

- Base case: If `s` is empty, then `nproduct s f = 1` holds, and `!x. x IN s ==> f x = 1` also holds vacuously because `x IN s` is always false.
- Inductive step: Assume the theorem holds for all subsets of `s`. We want to show that it also holds for `s`. Let `s` be `INSERT a s'`, where `s'` is a subset of `s`. The assumption is that `s` is finite.  We use the definition of `nproduct` on `INSERT`: `nproduct (INSERT a s') f = f a * nproduct s' f`.
    - If `nproduct (INSERT a s') f = 1`, then `f a * nproduct s' f = 1`. By the inductive hypothesis on `s'`, `nproduct s' f = 1` iff `!x. x IN s' ==> f x = 1`. Also `!x. x IN INSERT a s' ==> f x = 1` is equivalent to `f a = 1 /\ (!x. x IN s' ==> f x = 1)`. Combine these to get the inductive step.
    - The proof uses rewriting with `IMP_CONJ` `RIGHT_FORALL_IMP_THM`, `NPRODUCT_CLAUSES`, `IN_INSERT`, `MULT_EQ_1` and `NOT_IN_EMPTY` to simplify the goal, followed by an ASM_MESON call to finish the proof.

### Mathematical insight
This theorem provides a necessary and sufficient condition for the product of a function `f` over a finite set `s` to be equal to 1. This is a useful result when dealing with multiplicative structures and finite sets, it links the global property (the product) to a local property (the value of the function at each point in the set).

### Dependencies
- `FINITE_INDUCT_STRONG`
- `NPRODUCT_CLAUSES`
- `IN_INSERT`
- `MULT_EQ_1`
- `NOT_IN_EMPTY`
- `IMP_CONJ`
- `RIGHT_FORALL_IMP_THM`


---

## NPRODUCT_SPLITOFF

### Name of formal statement
NPRODUCT_SPLITOFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_SPLITOFF = prove
 (`!x:A f s. FINITE s
             ==> nproduct s f =
                 (if x IN s then f(x) else 1) * nproduct (s DELETE x) f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MULT_CLAUSES; SET_RULE `~(x IN s) ==> s DELETE x = s`] THEN
  SUBGOAL_THEN `s = (x:A) INSERT (s DELETE x)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th] THEN
              ASM_SIMP_TAC[NPRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE]) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]);;
```

### Informal statement
For any element `x` of type `A`, any function `f` from `A` to numbers, and any set `s` of type `A`, if `s` is finite, then the product of `f` over `s` equals `f(x)` if `x` is in `s`, and 1 otherwise, multiplied by the product of `f` over the set `s` with `x` removed.

### Informal sketch
The proof proceeds by induction on the finiteness property of the set `s`.

- The goal is to prove `!x:A f s. FINITE s ==> nproduct s f = (if x IN s then f(x) else 1) * nproduct (s DELETE x) f`. First, strip the quantifiers and implication.
- Split into cases based on whether `x IN s` or not.
- In the case `~(x IN s)`, simplify using the definition that `s DELETE x = s` if `x` is not in `s`. Further simplification handles cases where `nproduct s f = 1 * nproduct s f`.
- For the case where `x IN s`, show that `s = (x:A) INSERT (s DELETE x)`. Then, rewrite using this equality.
- Simplify using the properties of `nproduct`, `FINITE_DELETE`, and `IN_DELETE`.
- Conclude by discharging the assumptions and setting the goal.

### Mathematical insight
This theorem provides a way to decompose the product over a finite set by splitting off a single element. This is a fundamental property used in many inductive proofs involving finite sets and products. It's a canonical way to relate `nproduct s f` to a smaller set `s DELETE x`.

### Dependencies
- `MULT_CLAUSES`
- `SET_RULE` such as `~(x IN s) ==> s DELETE x = s`
- `NPRODUCT_CLAUSES`
- `FINITE_DELETE`
- `IN_DELETE`


---

## NPRODUCT_SPLITOFF_HACK

### Name of formal statement
NPRODUCT_SPLITOFF_HACK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_SPLITOFF_HACK = prove
 (`!x:A f s. nproduct s f =
             if FINITE s then
               (if x IN s then f(x) else 1) * nproduct (s DELETE x) f
             else nproduct s f`,
  REPEAT STRIP_TAC THEN MESON_TAC[NPRODUCT_SPLITOFF]);;
```
### Informal statement
For any set `s` of type `:A`, any function `f` from `:A` to `:num`, and any element `x` of type `:A`, the generalized product of `f` over `s` is equal to: if `s` is finite, then the product of (if `x` is in `s` then `f(x)` else 1) and the generalized product of `f` over `s` with `x` removed; otherwise, the generalized product of `f` over `s`.

### Informal sketch
The proof proceeds by stripping the quantifiers and then applying the theorem `NPRODUCT_SPLITOFF` using `MESON_TAC`. MESON is a tableau-based automated reasoning tool. `NPRODUCT_SPLITOFF` likely states the same result without the conditional expression to deal with potentially infinite sets. The finiteness check ensures that when `s` is infinite, both sides are equal to `nproduct s f`.

### Mathematical insight
This theorem provides a way to decompose a generalized product by extracting a single element. If the set is finite, one can split off a term corresponding to an element `x` from the product, accounting for the case where the element `x` is not in the set `s` by multiplying by 1. If the set `s` is infinite, then the generalized product remains the same. The hack probably refers to specializing for finite sets, to avoid the `DELETE` operator acting on possibly infinite sets, where things get tricky.

### Dependencies
- Theorems: `NPRODUCT_SPLITOFF`


---

## NPRODUCT_EQ

### Name of formal statement
NPRODUCT_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_EQ = prove
 (`!f g s. FINITE s /\ (!x. x IN s ==> f x = g x)
           ==> nproduct s f = nproduct s g`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT]);;
```
### Informal statement
For any functions `f` and `g`, and any set `s`, if `s` is finite and for all `x` in `s`, `f(x)` equals `g(x)`, then the product of `f` over `s` equals the product of `g` over `s`.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `s`.

- The base case is handled implicitly by the inductive step when `s` is empty.
- In the inductive step, we assume the theorem holds for all subsets of `s`. We consider an arbitrary element `x` in `s` and rewrite the product over `s` as `nproduct (INSERT x (s DIFF x)) f`. Then, since `x` is in `s`, `f x = g x`, so we can rewrite the product as `f x * nproduct (s DIFF x) f`. By the inductive hypothesis, since `s DIFF x` is a subset of `s`, `nproduct (s DIFF x) f = nproduct (s DIFF x) g`. We then reverse the initial steps to rewrite `nproduct s g` from `g x * nproduct (s DIFF x) g` to `nproduct s g`.

### Mathematical insight
This theorem states that if two functions agree on a finite set, then their products over that set are equal. This is a fundamental property used when manipulating and reasoning about products of functions over finite sets.

### Dependencies
- Theorems: `FINITE_INDUCT_STRONG`
- Definitions: `NPRODUCT_CLAUSES`, `IN_INSERT`


---

## NPRODUCT_EQ_GEN

### Name of formal statement
NPRODUCT_EQ_GEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_EQ_GEN = prove
 (`!f g s t. FINITE s /\ s = t /\ (!x. x IN s ==> f x = g x)
             ==> nproduct s f = nproduct t g`,
  MESON_TAC[NPRODUCT_EQ]);;
```

### Informal statement
For all functions `f` and `g`, and for all finite sets `s` and `t`, if `s` is finite, `s` equals `t`, and for all `x`, if `x` is in `s` then `f x` equals `g x`, then the product of `f x` over `s` equals the product of `g x` over `t`.

### Informal sketch
- The theorem states that if two functions agree on a finite set, and that finite set is equal to another set, then the product of the functions over the respective sets is equal.
- Proof is performed using `MESON_TAC` and the theorem `NPRODUCT_EQ`.

### Mathematical insight
This theorem establishes a condition under which the product of a function over a finite set remains invariant. Specifically, if we have two functions, `f` and `g`, that agree on a finite set `s`, and we have another set `t` that is equal to `s`, then the product of `f` over `s` will be equal to the product of `g` over `t`. This is a standard and useful result when manipulating finite products.

### Dependencies
- Theorems: `NPRODUCT_EQ`


---

## PRIME_DIVIDES_NPRODUCT

### Name of formal statement
PRIME_DIVIDES_NPRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let PRIME_DIVIDES_NPRODUCT = prove
 (`!p s f. prime p /\ FINITE s /\ p divides (nproduct s f)
           ==> ?x. x IN s /\ p divides (f x)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[PRIME_DIVPROD; DIVIDES_ONE; PRIME_1]);;
```

### Informal statement
For all primes `p`, all finite sets `s`, and all functions `f`, if `p` is prime and `s` is finite and `p` divides the product of `f(x)` over all `x` in `s`, then there exists an `x` in `s` such that `p` divides `f(x)`.

### Informal sketch
The theorem states that if a prime `p` divides a product of values `f(x)` over a finite set `s`, then `p` must divide at least one of the factors `f(x)` for some `x` in `s`.  This is proved by strong induction on the size of the finite set `s`.

- Base case: `s` is empty. The product over the empty set is 1. Since `p` is prime, it cannot divide 1 unless `p` is equal to 1 (which violates the condition `prime p`). Thus, the antecedent is false, and the implication holds vacuously.
- Inductive step: `s` is non-empty, so it can be written as `insert x t` where `x` is an element and `t` is a finite set. Then `nproduct (insert x t) f = f x * nproduct t f`. If `p` divides `nproduct (insert x t) f`, then `p` divides `f x * nproduct t f`.  We can then use the theorem `PRIME_DIVPROD` which states that if a prime divides a product, then it divides one of the factors.  Thus, either `p` divides `f x` or `p` divides `nproduct t f`. If `p` divides `f x`, then we are done because `x IN insert x t`. If `p` divides `nproduct t f`, then by the inductive hypothesis, there exists some `y IN t` such that `p` divides `f y`. Since `y IN t`, we also have `y IN insert x t`, so we are done.

### Mathematical insight
This theorem expresses a fundamental property of prime numbers: if a prime divides a product, it must divide at least one of the factors. This is a crucial property in number theory and is essential for reasoning about divisibility, factorization, and modular arithmetic.

### Dependencies
- `PRIME_DIVPROD`: If a prime divides a product, it divides one of the factors.
- `DIVIDES_ONE`: No number other than 1 and -1 divides 1.
- `PRIME_1`: 1 is not prime.
- `NPRODUCT_CLAUSES`: Defines the product over a set recursively.
- `IN_INSERT`: Defines set membership for the insert operation.
- `NOT_IN_EMPTY`: No element is in the empty set.
- `FINITE_INDUCT_STRONG`: Strong induction principle for finite sets.

### Porting notes (optional)
This theorem is a standard result in number theory and should be easily translated into most proof assistants. Ensure that the definition of `nproduct` is consistent with the HOL Light definition, where `nproduct {} f = 1`. The theorem `PRIME_DIVPROD` may need to be proven separately if it is not already available in the target proof assistant's library. The inductive proof strategy is fairly standard. The main challenge may lie in finding or proving appropriate versions of supporting lemmas related to divisibility and prime numbers.


---

## NPRODUCT_CANCEL_PRIME

### Name of formal statement
NPRODUCT_CANCEL_PRIME

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_CANCEL_PRIME = prove
 (`!s p m f j.
        p EXP j * nproduct (s DELETE p) (\p. p EXP (f p)) = p * m
        ==> prime p /\ FINITE s /\ (!x. x IN s ==> prime x)
            ==> ~(j = 0) /\
                p EXP (j - 1) * nproduct (s DELETE p) (\p. p EXP (f p)) = m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(j = 0) ==> j = SUC(j - 1)`)) THEN
    REWRITE_TAC[SUC_SUB1; EXP; GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
    MESON_TAC[PRIME_0]] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num`; `s DELETE (p:num)`; `\p. p EXP (f p)`]
                 PRIME_DIVIDES_NPRODUCT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[divides; FINITE_DELETE]; ALL_TAC] THEN
  REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[PRIME_1; prime; PRIME_DIVEXP]);;
```

### Informal statement
For all sets `s` of numbers, prime numbers `p`, numbers `m`, functions `f` from numbers to numbers, and numbers `j`, if `p` raised to the power of `j` multiplied by the product of `x` raised to the power of `f x` for each `x` in the set `s` excluding `p` equals `p` times `m`, then `p` is prime, `s` is a finite set of prime numbers, `j` is not equal to 0, and `p` raised to the power of `j - 1` multiplied by the product of `x` raised to the power of `f x` for each `x` in the set `s` excluding `p` equals `m`.

### Informal sketch
The proof proceeds by assuming the antecedent `p EXP j * nproduct (s DELETE p) (\p. p EXP (f p)) = p * m` and `prime p /\ FINITE s /\ (!x. x IN s ==> prime x)` and showing `~(j = 0) /\ p EXP (j - 1) * nproduct (s DELETE p) (\p. p EXP (f p)) = m`.
- First, we consider the case where `j = 0`. This leads to a contradiction since a prime `p` would divide 1, which isn't possible unless `p = 0`.
- Therefore, `j` is not equal to 0, thus enabling us to rewrite `j` as `SUC(j - 1)`.
- Applying `SUC_SUB1`, `EXP`, associativity of multiplication (`GSYM MULT_ASSOC`), and cancellation of multiplication (`EQ_MULT_LCANCEL`), we can deduce the second part of the conclusion, that `p EXP (j - 1) * nproduct (s DELETE p) (\p. p EXP (f p)) = m`.
- The proof uses `PRIME_DIVIDES_NPRODUCT` to relate primes and the product of other prime powers.
- The proof uses set manipulation, particularly properties of `DELETE`, to eliminate `p` from consideration in the product.

### Mathematical insight
The theorem essentially states that if a product of prime powers (including `p^j`) equals `p * m`, then we can extract one factor of `p` from the product, reducing the exponent of `p` from `j` to `j-1`. The main point is to ensure that the removal of `p` is valid given the constraints on the set `s` and the primality of its elements.

### Dependencies
- `SUC_SUB1`
- `EXP`
- `MULT_ASSOC`
- `EQ_MULT_LCANCEL`
- `PRIME_DIVIDES_NPRODUCT`
- `divides`
- `FINITE_DELETE`
- `IN_DELETE`
- `PRIME_1`
- `prime`
- `PRIME_DIVEXP`
- `DELETE`
- `FINITE`
- `GSYM CONTRAPOS_THM`
- `MULT_CLAUSES`
- `PRIME_0`

### Porting notes (optional)
- The `ASM_CASES_TAC` tactic in HOL Light may need to be emulated by a case split in other proof assistants.
- The handling of arithmetic and simplification of exponents may require adjustments based on the target proof assistant's capabilities.
- `PRIME_DIVIDES_NPRODUCT` will almost certainly have to be proven separately.


---

## FTA

### Name of formal statement
FTA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FTA = prove
 (`!n. ~(n = 0)
       ==> ?!i. FINITE {p | ~(i p = 0)} /\
                (!p. ~(i p = 0) ==> prime p) /\
                n = nproduct {p | ~(i p = 0)} (\p. p EXP (i p))`,
  ONCE_REWRITE_TAC[ARITH_RULE `n = nproduct s f <=> nproduct s f = n`] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
    SIMP_TAC[NPRODUCT_EQ_1_EQ; EXP_EQ_1; IN_ELIM_THM] THEN
    REWRITE_TAC[FUN_EQ_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [EXISTS_TAC `\n:num. 0` THEN
      REWRITE_TAC[SET_RULE `{p | F} = {}`; FINITE_RULES];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      X_GEN_TAC `q:num` THEN ASM_CASES_TAC `q = 1` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PRIME_1]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  REWRITE_TAC[divides; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `m:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[PRIME_FACTOR_LT]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num->num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\q:num. if q = p then i(q) + 1 else i(q)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `p INSERT {p:num | ~(i p = 0)}` THEN
      ASM_SIMP_TAC[SUBSET; FINITE_INSERT; IN_INSERT; IN_ELIM_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN CONJ_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPEC `p:num` NPRODUCT_SPLITOFF_HACK) THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; ADD_EQ_0; ARITH] THEN
    REWRITE_TAC[MULT_ASSOC] THEN BINOP_TAC THENL
     [ASM_CASES_TAC `(i:num->num) p = 0` THEN
      ASM_REWRITE_TAC[EXP_ADD; EXP_1; EXP; MULT_AC];
      ALL_TAC] THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN RULE_ASSUM_TAC(SIMP_RULE[]) THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; EXTENSION; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `p:num` NPRODUCT_SPLITOFF_HACK) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[TAUT
   `p /\ q /\ ((if p then x else y) = z) <=> p /\ q /\ x = z`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[EXP] `(if ~(x = 0) then p EXP x else 1) = p EXP x`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`j:num->num`; `k:num->num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\i:num. if i = p then j(i) - 1 else j(i)`;
    `\i:num. if i = p then k(i) - 1 else k(i)`]) THEN
  REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP NPRODUCT_CANCEL_PRIME)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[SET_RULE
   `!j k. {q | ~((if q = p then j q else k q) = 0)} DELETE p =
          {q | ~(k q = 0)} DELETE p`] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
     [`~(j(p:num) = 0)`; `~(k(p:num) = 0)`] THEN ARITH_TAC] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | ~(j p = 0)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    ASM_MESON_TAC[SUB_0];
    FIRST_X_ASSUM(fun th -> SUBST1_TAC(SYM th) THEN AP_TERM_TAC) THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[IN_DELETE; IN_ELIM_THM];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p:num | ~(k p = 0)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
    ASM_MESON_TAC[SUB_0];
    FIRST_X_ASSUM(fun th -> SUBST1_TAC(SYM th) THEN AP_TERM_TAC) THEN
    MATCH_MP_TAC NPRODUCT_EQ_GEN THEN ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[IN_DELETE; IN_ELIM_THM]]);;
```

### Informal statement
For all natural numbers `n`, if `n` is not equal to 0, then there exists a function `i` from natural numbers to natural numbers such that:
1. The set of all `p` such that `i p` is not equal to 0 is finite, and
2. For all `p`, if `i p` is not equal to 0, then `p` is prime, and
3. `n` is equal to the product over the set of all `p` such that `i p` is not equal to 0, of `p` raised to the power of `i p`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n = 1`. We need to show that there exists a function `i` satisfying the three conditions.  The function `i` that always returns 0 satisfies these conditions, since the empty product is 1.
- Inductive step: Assume `n > 1`. Then we use `PRIME_FACTOR` to find a prime factor `p` of `n`.  Define a new function `i'` such that `i'(p) = i(p) + 1` and `i'(q) = i(q)` for `q != p`.
  - Show `FINITE {p | ~(i' p = 0)}`.
  - Show `!p. ~(i' p = 0) ==> prime p`.
  - Show `n = nproduct {p | ~(i' p = 0)} (\p. p EXP (i' p))`.  This step involves splitting off the prime factor `p` from the product using `NPRODUCT_SPLITOFF_HACK` and simplifying using the inductive hypothesis. Then use `NPRODUCT_CANCEL_PRIME` to reduce this to `nproduct {q | ~(j q = 0)} (\q. q EXP (j q)) = nproduct {q | ~(k q = 0)} (\q. q EXP (k q))`, where where `j` and `k` are function `i` before the current step.
  - The final steps rewrite and simplify the conditions related to `nproduct`, handling cases where `~(j(p:num) = 0)` and `~(k(p:num) = 0)`.

### Mathematical insight
This theorem is the Fundamental Theorem of Arithmetic, which states that every natural number greater than 1 can be uniquely represented as a product of prime numbers, up to the order of the factors. The function `i` represents the exponents of the prime factors in the prime factorization of `n`.

### Dependencies
- `ARITH_RULE`
- `EXISTS_UNIQUE_THM`
- `num_WF`
- `PRIME_FACTOR`
- `divides`
- `RIGHT_AND_EXISTS_THM`
- `LEFT_IMP_EXISTS_THM`
- `MONO_AND`
- `FINITE_SUBSET`
- `NPRODUCT_SPLITOFF_HACK`
- `NPRODUCT_CANCEL_PRIME`
- `prime`

### Porting notes (optional)
The theorem relies on the `nproduct` function, which might need to be defined in other proof assistants if it is not already available. The `NPRODUCT_SPLITOFF_HACK` and `NPRODUCT_CANCEL_PRIME` theorems are custom theorems used to manipulate nproducts in HOL Light; similar lemmas might need to be proved in other systems.


---

