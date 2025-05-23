# wilson.ml

## Overview

Number of statements: 6

The `wilson.ml` file formalizes Wilson's theorem, a fundamental result in number theory. It relies on definitions and theorems imported from `prime.ml` and `pocklington.ml`, suggesting a connection to primality testing and factorization. The file's purpose is to provide a formal proof of Wilson's theorem, likely using HOL Light's formal logic and proof assistant capabilities. This contributes to the library's coverage of number theoretic concepts and results.

## FACT_NPRODUCT

### Name of formal statement
FACT_NPRODUCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FACT_NPRODUCT = prove
 (`!n. FACT(n) = nproduct(1..n) (\i. i)`,
  INDUCT_TAC THEN
  REWRITE_TAC[FACT; NUMSEG_CLAUSES; ARITH; NPRODUCT_CLAUSES] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= SUC n`; NPRODUCT_CLAUSES; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC)
```

### Informal statement
For all natural numbers n, the factorial of n (denoted as FACT(n)) is equal to the product of all numbers from 1 to n.

### Informal sketch
* The proof proceeds by induction on n, using `INDUCT_TAC`.
* The base case and inductive step involve rewriting expressions using various definitions and clauses, including `FACT`, `NUMSEG_CLAUSES`, `ARITH`, and `NPRODUCT_CLAUSES`.
* Simplification is performed using `ASM_SIMP_TAC` and `REWRITE_TAC` to manipulate the expressions and ultimately prove the equality.
* Key steps involve recognizing the `nproduct` over a range and applying properties of arithmetic and finite segments.

### Mathematical insight
This theorem provides an alternative characterization of the factorial function in terms of a product over a range, which can be useful in various mathematical derivations and proofs. The factorial function is a fundamental concept in number theory and combinatorics, and this representation can offer insights into its properties and relationships with other mathematical constructs.

### Dependencies
* Theorems and definitions:
  + `FACT`
  + `NUMSEG_CLAUSES`
  + `ARITH`
  + `NPRODUCT_CLAUSES`
  + `FINITE_NUMSEG`
  + `IN_NUMSEG`
* Inductive rules:
  + `INDUCT_TAC`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of binders, induction, and rewriting. The `nproduct` function and its properties may need to be defined or imported, and the arithmetic and simplification tactics may have different names or behaviors. Additionally, the `ASM_SIMP_TAC` and `REWRITE_TAC` tactics may need to be replaced with equivalent tactics in the target system.

---

## FACT_NPRODUCT_ALT

### Name of formal statement
FACT_NPRODUCT_ALT

### Type of the formal statement
Theorem

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
  ARITH_TAC)
```

### Informal statement
For all natural numbers `n`, the factorial of `n` is equal to the product of all natural numbers `i` from 2 to `n`.

### Informal sketch
* The proof starts by considering all possible cases for `n`, split into `n = 0` and `1 <= n` using `DISJ_CASES_TAC`.
* For each case, it applies various rewrite rules and simplifications, including `REWRITE_TAC[FACT_NPRODUCT]`, `ASM_REWRITE_TAC`, and `SIMP_TAC`, to transform the expression for the factorial into a form involving `nproduct`.
* The `nproduct` is then simplified using `NPRODUCT_CLAUSES` and properties of arithmetic, such as `MULT_CLAUSES`.
* The proof leverages the `ARITH_TAC` tactic for arithmetic simplifications and uses `GSYM NUMSEG_LREC` for handling numerical segments.
* Key steps involve recognizing the equivalence between the factorial function `FACT` and the product over a range, facilitated by `REWRITE_TAC[ARITH; NPRODUCT_CLAUSES; FACT]`.

### Mathematical insight
This theorem provides an alternative characterization of the factorial function in terms of a product over a range, which can be useful in various mathematical proofs and derivations. The factorial function is a fundamental concept in mathematics, and expressing it as a product has implications for understanding its properties and behavior.

### Dependencies
* `FACT`
* `NPRODUCT`
* `ARITH`
* `NPRODUCT_CLAUSES`
* `FACT_NPRODUCT`
* `NUMSEG_CLAUSES`
* `FINITE_NUMSEG`
* `IN_NUMSEG`
* `MULT_CLAUSES`

### Porting notes
When translating this theorem into other proof assistants, pay close attention to how each system handles arithmetic, products over ranges, and the factorial function. Specifically, the equivalent of `nproduct` and its properties, as well as the arithmetic tactics like `ARITH_TAC`, may need to be carefully ported or reimplemented. Additionally, the use of `DISJ_CASES_TAC` for case splitting and various rewrite rules might require adjustments based on the target system's approach to proof automation and term rewriting.

---

## NPRODUCT_PAIRUP_INDUCT

### Name of formal statement
NPRODUCT_PAIRUP_INDUCT

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[])
```

### Informal statement
For all functions `f`, numbers `r` and `n`, and sets `s`, if `s` is finite with `n` elements, and for every `x` in `s`, there exists a unique `y` in `s` such that `y` is not equal to `x` and the product of `f(x)` and `f(y)` is congruent to `1` modulo `r`, then the product of `f` over `s` is congruent to `1` modulo `r`.

### Informal sketch
* The proof starts by assuming `s` is not empty and using `GEN_TAC` and `MATCH_MP_TAC` to set up the induction.
* It then considers the case where `s` has `n` elements and `n` is not `0`, using `X_GEN_TAC` and `DISCH_TAC` to manage the assumptions.
* The proof proceeds by choosing an element `a` from `s` using `FIRST_X_ASSUM` and `X_CHOOSE_TAC`, and then finding a unique `b` in `s` such that `f(a)` and `f(b)` multiply to `1` modulo `r`, using `REWRITE_TAC` and `DISCH_THEN`.
* The proof then uses `DISCH_THEN` and `MP_TAC` to apply the induction hypothesis to the set `s` with `a` and `b` removed, and `ANTS_TAC` to prove the result for the smaller set.
* Finally, the proof uses `SUBGOAL_THEN` and `SUBST1_TAC` to rewrite `s` as the union of `a`, `b`, and the rest of `s`, and `SIMP_TAC` and `ASM_REWRITE_TAC` to simplify the expression and apply the `CONG_MULT` theorem.

### Mathematical insight
This theorem provides a way to reduce the computation of a product over a set `s` to the computation of products over smaller subsets, under certain conditions. The key idea is that if for every element `x` in `s`, there is a unique `y` in `s` such that `f(x)` and `f(y)` multiply to `1` modulo `r`, then the product of `f` over `s` can be simplified using this pairing.

### Dependencies
* `num_WF`
* `NPRODUCT_CLAUSES`
* `FINITE_DELETE`
* `CARD_DELETE`
* `IN_DELETE`
* `EXISTS_UNIQUE`
* `EXISTS_UNIQUE_THM`
* `MULT_SYM`
* `CONG_MULT`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to preserve the precise logical structure and quantifiers. The use of `GEN_TAC` and `MATCH_MP_TAC` to set up the induction, and the application of `CONG_MULT` to simplify the expression, may require special attention. Additionally, the `SUBGOAL_THEN` and `SUBST1_TAC` tactics may need to be replaced with equivalent constructs in the target proof assistant.

---

## NPRODUCT_PAIRUP

### Name of formal statement
NPRODUCT_PAIRUP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NPRODUCT_PAIRUP = prove
 (`!f r s. FINITE s /\
           (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                  (f(x) * f(y) == 1) (mod r))
           ==> (nproduct s f == 1) (mod r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
  EXISTS_TAC `CARD(s:A->bool)` THEN ASM_REWRITE_TAC[])
```

### Informal statement
For all functions `f`, numbers `r`, and sets `s`, if `s` is finite and for every `x` in `s`, there exists a unique `y` in `s` such that `y` is not equal to `x` and the product of `f(x)` and `f(y)` is congruent to 1 modulo `r`, then the product of `f` over `s` is congruent to 1 modulo `r`.

### Informal sketch
* The proof starts by assuming the premises: `s` is finite, and for every `x` in `s`, there exists a unique `y` in `s` such that `y` is not equal to `x` and `f(x) * f(y)` is congruent to 1 modulo `r`.
* The `REPEAT STRIP_TAC` tactic is used to strip away the universal quantifiers and implications, leaving the main statement to be proved.
* The `MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT` tactic applies the `NPRODUCT_PAIRUP_INDUCT` rule to the current goal, which likely involves inductive reasoning over the finite set `s`.
* The `EXISTS_TAC `CARD(s:A->bool)` tactic introduces an existential quantifier, claiming the existence of a specific value related to the cardinality of `s`.
* Finally, `ASM_REWRITE_TAC[]` is applied to simplify the resulting expression using any available equalities or congruences.
* The overall structure suggests an inductive argument over the finite set `s`, leveraging the unique pairing property to establish the congruence of the product of `f` over `s`.

### Mathematical insight
This theorem provides a condition under which the product of a function `f` over a finite set `s` is congruent to 1 modulo `r`. The key idea is that if for every element `x` in `s`, there is a unique pair `y` in `s` such that `f(x) * f(y)` is congruent to 1 modulo `r`, then the overall product of `f` over `s` will also be congruent to 1 modulo `r`. This is likely useful in number theory or algebra, where such pairing and congruence properties are crucial.

### Dependencies
* `NPRODUCT_PAIRUP_INDUCT`
* `FINITE`
* `nproduct`
* `CARD`

### Porting notes
When translating this theorem into other proof assistants, pay attention to how they handle finite sets, modular arithmetic, and inductive proofs. Specifically, the use of `REPEAT STRIP_TAC` and `MATCH_MP_TAC` might need to be adapted, as different systems have different tactics for stripping quantifiers and applying rules. Additionally, the representation of the `nproduct` function and the `CARD` function may vary, requiring adjustments in the ported version.

---

## WILSON

### Name of formal statement
WILSON

### Type of the formal statement
Theorem

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
    REWRITE_TAC[LE_MULT_LCANCEL] THEN UNDISCH_TAC `2 <= x` THEN ARITH_TAC])
```

### Informal statement
For all prime numbers `p`, the statement `(FACT(p - 1) == p - 1) (mod p)` holds. This means that for any prime `p`, the factorial of `p-1` is congruent to `p-1` modulo `p`.

### Informal sketch
The proof of Wilson's theorem involves several key steps:
* Handling edge cases where `p` equals 0, 1, or 2.
* Using the definition of factorial (`FACT`) and properties of modular arithmetic.
* Employing the `CONG_UNIQUE_INVERSE_PRIME` theorem to establish unique inverses modulo `p`.
* Applying various properties of congruence, including `CONG_MULT`, `CONG_REFL`, and `CONG_TRANS`.
* Utilizing the `MONO_AND` and `MONO_EXISTS` theorems for monotonicity of logical operators.
* Case analysis on the value of `y` to prove the main statement.
* Leveraging properties of divisibility (`DIVIDES_LE`), prime numbers (`PRIME_DIVPROD`), and arithmetic (`ARITH_RULE`).

### Mathematical insight
Wilson's theorem is a fundamental result in number theory, stating that a natural number `n` is a prime if and only if `(n-1)! ≡ -1 (mod n)`. This theorem provides a criterion for primality and has numerous applications in mathematics and computer science.

### Dependencies
* Theorems:
  + `PRIME_0`
  + `PRIME_1`
  + `CONG_UNIQUE_INVERSE_PRIME`
  + `PRIME_DIVPROD`
  + `DIVIDES_LE`
  + `MONO_AND`
  + `MONO_EXISTS`
* Definitions:
  + `FACT` (factorial)
  + `CONG` (congruence modulo)
* Inductive rules and type definitions:
  + `NAT` (natural numbers)
  + `NUM` (numbers)

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay attention to the handling of:
* Modular arithmetic and congruences
* Factorial function and its properties
* Prime numbers and their properties
* Monotonicity of logical operators
* Case analysis and proof by contradiction
* Arithmetic and divisibility properties
Note that the specific tactics and theorems used in HOL Light might not have direct counterparts in other systems, so understanding the mathematical structure and intent behind the proof is crucial for successful porting.

---

## WILSON_EQ

### Name of formal statement
WILSON_EQ

### Type of the formal statement
Theorem

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
    REWRITE_TAC[DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]])
```

### Informal statement
For all prime numbers `p` not equal to 1, `p` is prime if and only if `(p-1)!` is congruent to `p-1` modulo `p`.

### Informal sketch
* The proof starts by assuming `~(p = 1)` and then proceeds to prove the equivalence between `prime p` and `(FACT(p - 1) == p - 1) (mod p)`.
* It uses `X_GEN_TAC` to introduce a generic `n` and then `DISCH_TAC` to discharge assumptions.
* The `EQ_TAC` and `SIMP_TAC` with `WILSON` theorem are applied to simplify the statement.
* The proof then proceeds with case analysis using `ASM_CASES_TAC` on `n = 0` and `n = p`.
* Key steps involve applying `MATCH_MP_TAC` with `PRIME_FACTOR`, `DIVIDES_LE`, and `CONG_DIVIDES` to establish relationships between divisibility and congruence.
* The `SUBGOAL_THEN` tactic is used to substitute and simplify subgoals, particularly in establishing the equivalence `p divides FACT(n - 1) <=> p divides (n - 1)`.

### Mathematical insight
This theorem relates the primality of a number `p` to a congruence property involving the factorial of `p-1`. It's a formalization of Wilson's theorem, which states that a number `p` is prime if and only if `(p-1)!` is congruent to `-1` modulo `p`, but here it's stated as `p-1` modulo `p` due to the nature of the formalization. This theorem is significant in number theory as it provides a criterion for primality.

### Dependencies
* Theorems:
  + `WILSON`
  + `PRIME_FACTOR`
  + `DIVIDES_LE`
  + `CONG_DIVIDES`
  + `CONG_DIVIDES_MODULUS`
  + `DIVIDES_ONE`
  + `PRIME_1`
* Definitions:
  + `prime`
  + `FACT`
  + `divides`

### Porting notes
When translating this theorem into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how each system handles:
- Quantifiers and generic variables (e.g., `!p`, `X_GEN_TAC `n:num``).
- Modular arithmetic and congruences (e.g., `(mod p)`).
- Case analysis and assumption discharge (e.g., `ASM_CASES_TAC`, `DISCH_TAC`).
- Application of theorems and tactics (e.g., `MATCH_MP_TAC`, `SIMP_TAC`).
- Factorial function and divisibility predicates.
- Potential differences in handling of `WILSON` theorem or its equivalent in the target system.

---

