# wilson.ml

## Overview

Number of statements: 6

`wilson.ml` formalizes Wilson's theorem, a fundamental result in number theory relating primality to the factorial function. The file likely contains a formal definition of Wilson's theorem and its corresponding proof within HOL Light. It depends on the theories developed in `prime.ml` and `pocklington.ml`.


## FACT_NPRODUCT

### Name of formal statement
FACT_NPRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_NPRODUCT = prove
 (`!n. FACT(n) = nproduct(1..n) (\i. i)`,
  INDUCT_TAC THEN
  REWRITE_TAC[FACT; NUMSEG_CLAUSES; ARITH; NPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; NPRODUCT_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, the factorial of `n`, denoted `FACT(n)`, is equal to the product of the numbers from 1 to `n`, denoted `nproduct(1..n) (\i. i)`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: When `n = 0`, we need to show `FACT(0) = nproduct(1..0) (\i. i)`.  This follows from the definitions of `FACT` and `nproduct`.
- Inductive step: Assume `FACT(n) = nproduct(1..n) (\i. i)`. We need to show `FACT(SUC n) = nproduct(1..SUC n) (\i. i)`.
    - We rewrite `FACT(SUC n)` to `(SUC n) * FACT n` using the definition of `FACT`.
    - We rewrite `nproduct(1..SUC n) (\i. i)` to `nproduct(1..n) (\i. i) * (SUC n)` using the properties of `nproduct` and the fact that `SUC n` is the last element of the segment `1..SUC n`. The condition `1 <= SUC n` is necessary for the application of `NPRODUCT_CLAUSES` involving `FINITE_NUMSEG` and `IN_NUMSEG`.
    - By the inductive hypothesis, `FACT(n) = nproduct(1..n) (\i. i)`.
    - The result follows by simplification.

### Mathematical insight
This theorem provides a link between the recursive definition of the factorial function (`FACT`) and its representation as a product of integers. This equivalence is fundamental and useful in many contexts, especially when dealing with combinatorial arguments or deriving analytic properties of the factorial function.

### Dependencies
- Definitions: `FACT`, `nproduct`
- Theorems/Lemmas: `NUMSEG_CLAUSES`, `ARITH`, `NPRODUCT_CLAUSES`, `ARITH_RULE '1 <= SUC n'`, `FINITE_NUMSEG`, `IN_NUMSEG`


---

## FACT_NPRODUCT_ALT

### Name of formal statement
FACT_NPRODUCT_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_NPRODUCT_ALT = prove
 (`!n. FACT(n) = nproduct(2..n) (\i. i)`,
  GEN_TAC THEN REWRITE_TAC[FACT_NPRODUCT] THEN
  DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THEN
  ASM_REWRITE_TAC[num_CONV `1`; NUMSEG_CLAUSES] THEN
  REWRITE_TAC[ARITH; NPRODUCT_CLAUSES; FACT] THEN
  ASM_SIMP_TAC[GSYM NUMSEG_LREC] THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG; MULT_CLAUSES] THEN
  ARITH_TAC);;
```

### Informal statement
For all natural numbers `n`, the factorial of `n`, denoted `FACT(n)`, is equal to the product of the numbers from 2 to `n`, where the product is defined as `nproduct(2..n) (\i. i)`.

### Informal sketch
The proof proceeds as follows:
- Start by rewriting the goal using the theorem `FACT_NPRODUCT`.
- Perform a case split based on whether `n` is zero or greater than or equal to 1. This splits the proof into two subgoals.
- In the case where `n` is zero, simplify the goal using the fact that `1` equals to `FACT(0)` and properties of number segments. Then, simplify using arithmetic and the definition of `nproduct` and `FACT`. Further simplification using rewriting with `NUMSEG_LREC` which defines list of numbers from m to n recursively.
- In the case where `n` is greater than or equal to 1, simplify the goal using arithmetic and the definition of `nproduct`, `FACT`, and number segments, and properties about membership and finiteness on numeric segments.
- Apply an arithmetic tactic to close both goals.

### Mathematical insight
This theorem provides an alternative characterization of the factorial function using the `nproduct` function, which computes the product of a function over a finite set of natural numbers. This is useful because it relates the factorial to a more general concept of products over sets.

### Dependencies
- Theorems: `FACT_NPRODUCT`
- Definitions: `FACT`, `NPRODUCT_CLAUSES`, `FINITE_NUMSEG`, `IN_NUMSEG`
- Other: `NUMSEG_CLAUSES`, `MULT_CLAUSES` (likely from arithmetic library)


---

## NPRODUCT_PAIRUP_INDUCT

### Name of formal statement
NPRODUCT_PAIRUP_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_PAIRUP_INDUCT = prove
 (`!f r n s. FINITE s /\ CARD s = n /\
             (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                    (f(x) * f(y) == 1) (mod r))
             ==> (nproduct s f == 1) (mod r)`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[NPRODUCT_CLAUSES; CONG_REFL] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_MESON_TAC[CARD_EQ_0]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n - 2`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 2 < n`] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[ASSUME `(a:A) IN s`] THEN
  REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `(s DELETE a) DELETE (b:A)`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_DELETE] THEN
    SIMP_TAC[FINITE_DELETE; ASSUME `FINITE(s:A->bool)`; CARD_DELETE] THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `y:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[MULT_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(b:A) IN s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:A`; `x:A`] o CONJUNCT2) THEN
    ASM_MESON_TAC[MULT_SYM];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s = (a:A) INSERT (b INSERT (s DELETE a DELETE b))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_INSERT; FINITE_DELETE;
           ASSUME `FINITE(s:A->bool)`] THEN
  ASM_REWRITE_TAC[IN_INSERT; IN_DELETE; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_ASSOC] THEN
  ONCE_REWRITE_TAC[SYM(NUM_REDUCE_CONV `1 * 1`)] THEN
  MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For any function `f` from elements of type `A` to numbers, any number `r`, any natural number `n`, and any set `s` of type `A` such that `s` is finite, the cardinality of `s` is `n`, and for all `x` in `s` there exists a unique `y` in `s` such that `x` is not equal to `y` and `f(x) * f(y)` is congruent to `1` modulo `r`; then the product of `f` over `s` is congruent to `1` modulo `r`.

### Informal sketch
The proof proceeds by induction on the cardinality `n` of the finite set `s`.

- Base Case: If `s` is empty, then the product over `s` is defined to be `1`, hence trivially congruent to 1 (mod r).
- Inductive Step: Assume that the theorem holds for sets of cardinality `n`. Now, consider a set `s` of cardinality `n+1` that satisfies the hypothesis.

  - Since `s` is non-empty, we can pick an element `a` from `s`.
  - By the assumption that for every element `x` in `s` there exists a unique `y` in `s` such that `f(x) * f(y)` is congruent to `1` modulo `r`, we can find an element `b` in `s` such that `f(a) * f(b)` is congruent to `1` modulo `r`.
  - Now we can consider the set `s` without `a` and `b`: `(s DELETE a) DELETE b`.
  - This set `(s DELETE a) DELETE b` has cardinality `n-1`. Furthermore, the main inductive hypothesis applies to `(s DELETE a) DELETE b`.
  - The induction hypothesis says that the product of `f` over `(s DELETE a) DELETE b` is congruent to 1 (mod r).
  - Note that `s` is equal to `(a INSERT (b INSERT (s DELETE a DELETE b)))`
  - Using the properties of `nproduct`, specifically `nproduct (a INSERT t) f = f a * nproduct t f` and modular arithmetic, it follows that `nproduct s f` is congruent to `f a * f b * 1 (mod r)`, then congruent to `1 * 1 (mod r)`, and then congruent to `1 (mod r)`.
- Therefore, the statement holds for any set `s` satisfying the given conditions.

### Mathematical insight
This theorem provides a condition under which the product of a function over a finite set is guaranteed to be congruent to 1 modulo `r`. The key condition is the existence of a pairing within the set such that the product of the function applied to each pair is congruent to 1 modulo `r`. This is a useful result in number theory and algebra.

### Dependencies
- `NPRODUCT_CLAUSES`
- `CARD_EQ_0`
- `MEMBER_NOT_EMPTY`
- `FINITE_DELETE`
- `CARD_DELETE`
- `IN_DELETE`
- `MONO_EXISTS`
- `MULT_SYM`
- `EXISTS_UNIQUE_THM`
- `FINITE_INSERT`
- `IN_INSERT`
- `MULT_CLAUSES`
- `MULT_ASSOC`
- `CONG_MULT`
- `num_WF`

### Porting notes (optional)
- Most proof assistants have similar concepts of set cardinality and finite sets, so these parts should be straightforward to port.
- The handling of the `mod` operator and modular arithmetic might differ slightly between proof assistants and could require some adjustments.
- The `nproduct` might need to be defined by importing a library depending on the target proof assistant. Lean's `Data.Finset.Basic` or Coq's `FinSet` provide similar functionalities.


---

## NPRODUCT_PAIRUP

### Name of formal statement
NPRODUCT_PAIRUP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_PAIRUP = prove
 (`!f r s. FINITE s /\
           (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                  (f(x) * f(y) == 1) (mod r))
           ==> (nproduct s f == 1) (mod r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
  EXISTS_TAC `CARD(s:A->bool)` THEN ASM_REWRITE_TAC[]);;
```
### Informal statement
For all functions `f` from type `A` to numbers modulo `r`, and for all sets `s` of elements of type `A`, if `s` is finite and for all `x` in `s` there exists a `y` in `s` distinct from `x` such that `f(x) * f(y)` is congruent to 1 modulo `r`, then the product of `f(x)` for `x` in `s` is congruent to 1 modulo `r`.

### Informal sketch
The proof proceeds by induction on the `FINITE` set `s`.
- Base Case: If `s` is empty, then `nproduct s f` is 1 by definition, and thus congruent to 1 modulo `r`.
- Inductive Step: Assume the theorem holds for `s`. We want to show it holds for `s U {a}` for some `a` not in `s`.
    - The existence of a `y` such that `f(a) * f(y) == 1 (mod r)` along with the inductive hypothesis on `s` allows concluding `(nproduct (s U {a}) f) == 1 (mod r)`.
    - The core of the argument is handled by `NPRODUCT_PAIRUP_INDUCT` which encapsulates the inductive reasoning.

### Mathematical insight
The theorem states that if a finite set `s` can be partitioned into pairs `(x, y)` such that `f(x) * f(y) == 1 (mod r)` for each pair, then the product of `f` over `s` is congruent to 1 modulo `r`. This captures the idea that if elements in a finite set can be paired such that their product is 1 (mod r), then the overall product of the elements is also 1 (mod r).

### Dependencies
- `FINITE`
- `nproduct`
- `NPRODUCT_PAIRUP_INDUCT`
- `CARD`


---

## WILSON

### Name of formal statement
WILSON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WILSON = prove
 (`!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  ASM_CASES_TAC `p = 2` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONG_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `FACT(p - 1) = FACT(p - 2) * (p - 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `p - 1 = SUC(p - 2)`
     (fun th -> REWRITE_TAC[th; FACT; MULT_AC]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = 1 * x`] THEN
  MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
  REWRITE_TAC[FACT_NPRODUCT_ALT] THEN MATCH_MP_TAC NPRODUCT_PAIRUP THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `x:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `x:num`] CONG_UNIQUE_INVERSE_PRIME) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS;
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  X_GEN_TAC `y:num` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `y = 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `2 <= y <=> 0 < y /\ ~(y = 1)`] THEN
    UNDISCH_TAC `(x * y == 1) (mod p)` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_SIMP_TAC[CONG; MOD_LT; ARITH_RULE `x <= p - 2 /\ ~(p = 0) ==> x < p`;
                 ARITH_RULE `~(p = 0) /\ ~(p = 1) ==> 1 < p`] THEN
    UNDISCH_TAC `2 <= x` THEN ARITH_TAC;
    MATCH_MP_TAC(ARITH_RULE `y < p /\ ~(y = p - 1) ==> y <= p - 2`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x * y == 1) (mod p)` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN SUBGOAL_THEN `(x + 1 == 0) (mod p)` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[CONG_0] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
      MAP_EVERY UNDISCH_TAC [`2 <= x`; `x <= p - 2`] THEN ARITH_TAC] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `x * p:num` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[CONG_0] THEN MESON_TAC[divides; MULT_SYM]] THEN
    SUBGOAL_THEN `x * p = x + x * (p - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC(GSYM SUB_ADD) THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
      UNDISCH_TAC `~(p = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC CONG_ADD THEN
    ASM_REWRITE_TAC[CONG_REFL];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `((x + 1) * (x - 1) == 0) (mod p)` MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[CONG_0] THEN
      DISCH_THEN(MP_TAC o CONJ (ASSUME `prime p`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP PRIME_DIVPROD) THEN
      DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP DIVIDES_LE)) THEN
      MAP_EVERY UNDISCH_TAC
        [`2 <= x`; `x <= p - 2`; `~(p = 1)`; `~(p = 0)`] THEN
      ARITH_TAC] THEN
    ONCE_REWRITE_TAC[GSYM(SPEC `1` CONG_ADD_LCANCEL_EQ)] THEN
    SUBGOAL_THEN `1 + (x + 1) * (x - 1) = x * x`
     (fun th -> ASM_REWRITE_TAC[th; ARITH]) THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
    MATCH_MP_TAC(ARITH_RULE
     `(x + 1) * 1 <= (x + 1) * x
      ==> 1 + (x + 1) * x - (x + 1) * 1 = x * x`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `2 <= x` THEN ARITH_TAC]);;
```

### Informal statement
For all `p`, if `p` is prime, then the factorial of `p - 1` is congruent to `p - 1` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- The goal is to prove that for any `p`, if `p` is `prime(p)`, then `FACT(p - 1) == p - 1 (mod p)`.
- The proof does case splitting on `p = 0`, `p = 1`, and `p = 2`. The `prime` condition quickly dispatches these cases with `PRIME_0` and `PRIME_1`, in the case of primes 0 and 1, and by direct calculation when `p = 2`.
- For the main case where `p > 2`, we perform the following steps:
 - Reduce `FACT(p - 1)` to `FACT(p - 2) * (p - 1)`.
 - Show that `p - 1 = SUC(p - 2)`.
 - Rewrite using `FACT` and associativity and commutativity of multiplication (`MULT_AC`).
 - Use `FACT_NPRODUCT_ALT` to rewrite `FACT(p - 2)` to `NPRODUCT numseg(1, p - 2) (\x. x)`.
 - Pair up the terms in the product.
 - Instantiate `CONG_UNIQUE_INVERSE_PRIME` with `p` and `x`.
 - Apply `EXISTS_UNIQUE_THM`, `MONO_AND`, `MONO_EXISTS`, and `MONO_FORALL`.
 - Introduce a variable `y`.
 - Case split on `y = 1`.
  - Assume `y = 1`. Use `MULT_CLAUSES` and modular arithmetic.
  - Show `(x + 1 == 0) (mod p)`.
  - Use the fact that `prime p` and congruence mod p implies divisibility.
 - Apply `CONG_TRANS`, exists tactic and `divides` to find a `k` : `x * y -1 = k*p`
 - Show `x * p = x + x * (p - 1)`.
 - Apply congruence properties and arithmetic reasoning, utilizing the condition that `p` is prime.
 - Show `((x + 1) * (x - 1) == 0) (mod p)`.
 - Apply several congruence relations.
 - Show `1 + (x + 1) * (x - 1) = x * x`.
 - Use modular arithmetic, primality of p, and previous assumptions to complete the proof.

### Mathematical insight
This is a statement of Wilson's Theorem, a fundamental result in number theory. It provides a necessary and sufficient condition for a number to be prime. The theorem connects the concept of primality to the factorial function and modular arithmetic.

### Dependencies
- `PRIME_0`: A theorem stating that 0 is not prime.
- `PRIME_1`: A theorem stating that 1 is not prime.
- `FACT`: Definition of the factorial function.
- `MULT_AC`: Theorem stating associativity and commutativity of multiplication.
- `FACT_NPRODUCT_ALT`: Theorem relating the factorial function to `NPRODUCT`.
- `NPRODUCT_PAIRUP`:  A theorem about pairing up in the `NPRODUCT` function
- `FINITE_NUMSEG`: Theorem about finiteness of `NUMSEG`
- `IN_NUMSEG`: Theorem to check if Number in `NUMSEG`
- `CONG_UNIQUE_INVERSE_PRIME`: Theorem about the existence of unique inverses modulo a prime.
- `EXISTS_UNIQUE_THM`:  Theorem dealing with existence and uniqueness
- `MONO_AND`: Theorem about monotonicity and conjunction
- `MONO_EXISTS`: Theorem about monotonicity and existential quantifiers
- `MONO_FORALL`: Theorem about monotonicity and universal quantifiers
- `divides` : Divides definition
- `PRIME_DIVPROD`: Theorem relating prime numbers and divisibility of a product.
- `CONG_ADD_LCANCEL_EQ`: Theorem concerning the cancellation of addition under congruence.

### Porting notes (optional)
- The heavy use of tactics like `ASM_CASES_TAC`, `ASM_REWRITE_TAC`, and arithmetic reasoning suggest that a proof assistant with strong automation in these areas (e.g. Z3 in Lean) would be beneficial for porting.
- The tactic `ANTS_TAC` is used to solve for the antecedents. Be aware that it might have to be solved by decomposing it manually, depending on the other system's level of automation.
- The `SUBGOAL_THEN` tactic allows one to insert intermediate goals. This tactic is important in controlling the reasoning path and may require careful adaptation in other proof assistants.


---

## WILSON_EQ

### Name of formal statement
WILSON_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WILSON_EQ = prove
 (`!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))`,
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN EQ_TAC THEN SIMP_TAC[WILSON] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[CONG_MOD_0] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[LE_LT] THEN ASM_CASES_TAC `n:num = p` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `x < y ==> x <= y - 1`)) THEN
  ASM_SIMP_TAC[GSYM DIVIDES_FACT_PRIME] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  SUBGOAL_THEN `p divides FACT(n - 1) <=> p divides (n - 1)` SUBST1_TAC THENL
   [MATCH_MP_TAC CONG_DIVIDES THEN
    MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `p divides 1` MP_TAC THENL
   [MATCH_MP_TAC DIVIDES_ADD_REVR THEN EXISTS_TAC `n - 1` THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 + 1 = n`];
    REWRITE_TAC[DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]]);;
```
### Informal statement
For all `p`, if `p` is not equal to 1, then `p` is prime if and only if the factorial of `p - 1` is congruent to `p - 1` modulo `p`.

### Informal sketch
The proof proceeds by showing that `p` is prime if and only if `FACT(p - 1) == p - 1) (mod p)`. The proof starts by discharging the assumption `~(p = 1)`.

*   First, it uses `WILSON` to rewrite the goal.
*   Then, using `PRIME_FACTOR`, it shows that `p` has a prime factor.
*   A prime factor `q` of `p` is chosen. Since `q` divides `p`, `q <= p` is proved using `DIVIDES_LE`.
*   Then, the proof considers two cases: `p` is zero or not.
    *   If `n = 0`, then the case is handled by congruence modulo 0.
    *   If `n` is not zero, it is checked whether `n = p`. Several arithmetic simplifications are done. Assuming `n = p`, it proves `p divides FACT(n - 1) <=> p divides (n - 1)`.
*   Then, it proves that `p divides 1` and then using `DIVIDES_ADD_REVR`, it shows that `p` divides `1`, and by `PRIME_1`, it leads to contradiction.

### Mathematical insight
This theorem formalizes Wilson's Theorem, which provides a necessary and sufficient condition for primality. It is a classical result in number theory that connects primality with modular arithmetic and factorials. Because calculating factorials is computationally expensive, Wilson's theorem is not used in practice for primality testing, but it is of theoretical interest.

### Dependencies
*   `WILSON`
*   `PRIME_FACTOR`
*   `DIVIDES_LE`
*   `CONG_MOD_0`
*   `LE_LT`
* `ARITH_RULE x < y ==> x <= y - 1`
*   `GSYM DIVIDES_FACT_PRIME`
*   `CONG_DIVIDES`
*   `CONG_DIVIDES_MODULUS`
*   `DIVIDES_ADD_REVR`
*   `ARITH_RULE ~(n = 0) ==> n - 1 + 1 = n`
*   `DIVIDES_ONE`
*   `PRIME_1`


---

