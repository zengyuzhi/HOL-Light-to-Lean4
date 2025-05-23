# reciprocity.ml

## Overview

Number of statements: 38

`reciprocity.ml` formalizes quadratic reciprocity. It builds upon prime number theory and modular arithmetic from imported files (`prime.ml`, `pocklington.ml`, `products.ml`). The file likely contains definitions related to quadratic residues and culminates in a proof of the law of quadratic reciprocity.


## IN_NUMSEG_1

### Name of formal statement
IN_NUMSEG_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IN_NUMSEG_1 = prove
 (`!p i. i IN 1..p - 1 <=> 0 < i /\ i < p`,
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `p` and `i`, `i` is in the set `1..p - 1` if and only if `0 < i` and `i < p`.

### Informal sketch
The theorem states an equivalence. The proof proceeds as follows:
- Expand the definition of `IN_NUMSEG`.
- Apply arithmetic simplification to complete the proof.

### Mathematical insight
This theorem provides a more convenient characterization of the set `1..p-1` by relating membership in the set to inequalities. This is a basic but useful lemma when reasoning about ranges of numbers.

### Dependencies
- Definitions: `IN_NUMSEG`
- Theorems: N/A
- Tactics: `REWRITE_TAC`, `ARITH_TAC`


---

## EVEN_DIV

### Name of formal statement
EVEN_DIV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EVEN_DIV = prove
 (`!n. EVEN n <=> n = 2 * (n DIV 2)`,
  GEN_TAC THEN REWRITE_TAC[EVEN_MOD] THEN
  MP_TAC(SPEC `n:num` (MATCH_MP DIVISION (ARITH_RULE `~(2 = 0)`))) THEN
  ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, `EVEN n` if and only if `n` is equal to `2` times (`n` divided by `2`).

### Informal sketch
The proof proceeds as follows:
- Start with `!n. EVEN n <=> n = 2 * (n DIV 2)`.
- Rewrite using the theorem `EVEN_MOD`, which states that `EVEN n <=> n MOD 2 = 0`. This turns the goal into `n MOD 2 = 0 <=> n = 2 * (n DIV 2)`.
- Apply `DIVISION` after specializing to `n:num` and discharging `~(2 = 0)`. This introduces `n = n DIV 2 * 2 + n MOD 2`.
- Use arithmetic reasoning to simplify the equation.

### Mathematical insight
This theorem establishes a fundamental relationship between the `EVEN` predicate and integer division. It shows that a number is even if and only if it is equal to 2 times its integer quotient. This makes explicit the implicit characterization of even numbers using division by 2 and relates integer division and remainders.

### Dependencies
- Theorems: `EVEN_MOD`, `DIVISION`


---

## CONG_MINUS1_SQUARE

### Name of formal statement
CONG_MINUS1_SQUARE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONG_MINUS1_SQUARE = prove
 (`2 <= p ==> ((p - 1) * (p - 1) == 1) (mod p)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cong; nat_mod; ARITH_RULE `(2 + x) - 1 = x + 1`] THEN
  MAP_EVERY EXISTS_TAC [`0`; `d:num`] THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `p`, if `2 <= p`, then `(p - 1) * (p - 1)` is congruent to `1` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- Assume `2 <= p`.
- Rewrite the congruence relation `((p - 1) * (p - 1) == 1) (mod p)` using the definition of congruence (`cong`) and the definition of the modulo operation on natural numbers (`nat_mod`). This reduces the goal to proving `EX d. (p - 1) * (p - 1) = 1 + d * p`.
- Prove the existence of `d` by exhibiting `0` when `p=2`, and `d:num` when `p > 2`.
- Use arithmetic reasoning (`ARITH_TAC`) to discharge the goals.

### Mathematical insight
This theorem states that for any integer `p` greater than or equal to 2, the square of `p-1` is congruent to 1 modulo `p`. In particular, if `p` is prime, then this is related to the fact that in the field of integers modulo `p`, `p-1` is the same as `-1`, so `(p-1)*(p-1)` is the same as `(-1)*(-1) = 1`.

### Dependencies
- Definitions: `cong`, `nat_mod`
- Theorems: `LE_EXISTS`, `LEFT_IMP_EXISTS_THM`
- Others: `ARITH_RULE \`(2 + x) - 1 = x + 1\``


---

## CONG_EXP_MINUS1

### Name of formal statement
CONG_EXP_MINUS1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONG_EXP_MINUS1 = prove
 (`!p n. 2 <= p ==> ((p - 1) EXP n == if EVEN n then 1 else p - 1) (mod p)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH; CONG_REFL] THEN
  MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC `(p - 1) * (if EVEN n then 1 else p - 1)` THEN
  ASM_SIMP_TAC[CONG_MULT; CONG_REFL; EVEN] THEN
  ASM_CASES_TAC `EVEN n` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; CONG_REFL; CONG_MINUS1_SQUARE]);;
```

### Informal statement
For all `p` and `n`, if `2 <= p`, then `(p - 1)^n` is congruent to `1` modulo `p` if `n` is even, and congruent to `p - 1` modulo `p` if `n` is odd.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: When `n = 0`, `(p - 1)^0 = 1`. Since `EVEN 0` is true, the result follows.
- Inductive step: Assume the result holds for `n`. We want to show it holds for `n + 1`.
  - We have `(p - 1)^(n + 1) = (p - 1) * (p - 1)^n`. By the inductive hypothesis, `(p - 1)^n` is congruent to `1` modulo `p` if `n` is even, and congruent to `p - 1` modulo `p` if `n` is odd.
  - Therefore, `(p - 1) * (p - 1)^n` is congruent to `(p - 1) * (if EVEN n then 1 else p - 1)` modulo `p`.
  - Now, we consider two cases:
    - If `n` is even, then `(p - 1) * (if EVEN n then 1 else p - 1)` simplifies to `p - 1`, and `EVEN (n + 1)` is false. Thus, we need to show that `p - 1` is congruent to `p - 1` modulo `p`, which is true.
    - If `n` is odd, then `(p - 1) * (if EVEN n then 1 else p - 1)` simplifies to `(p - 1) * (p - 1) = (p - 1)^2`. Since `(p - 1)^2 == 1 (mod p)` (by `CONG_MINUS1_SQUARE`), and `EVEN (n + 1)` is true, we need to show that `1` is congruent to `1` modulo `p`, which is true.

### Mathematical insight
This theorem states that powers of `p - 1` have a simple form modulo `p`: even powers are congruent to 1, and odd powers are congruent to `p - 1`. This can be useful for simplifying expressions involving powers modulo `p`.

### Dependencies
Congruence arithmetic:
- `CONG_REFL`
- `CONG_TRANS`
- `CONG_MULT`
Arithmetic:
- `ARITH`
- `EXP`
- `MULT_CLAUSES`
- `EVEN`
- `RIGHT_FORALL_IMP_THM`
- `CONG_MINUS1_SQUARE`


---

## NOT_CONG_MINUS1

### Name of formal statement
NOT_CONG_MINUS1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_CONG_MINUS1 = prove
 (`!p. 3 <= p ==> ~(p - 1 == 1) (mod p)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `(2 == 0) (mod p)` MP_TAC THENL
   [MATCH_MP_TAC CONG_ADD_LCANCEL THEN EXISTS_TAC `p - 1` THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN
    ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `3 <= p ==> (p - 1) + 2 = p + 1`] THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `0 + 1` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    MATCH_MP_TAC CONG_ADD THEN
    MESON_TAC[CONG_0; CONG_SYM; DIVIDES_REFL; CONG_REFL];
    REWRITE_TAC[CONG_0] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_ARITH_TAC]);;
```
### Informal statement
For all `p`, if `3 <= p`, then it is not the case that `p - 1` is congruent to `1` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- Assume `3 <= p` and `p - 1 == 1 (mod p)`.
- Show that this implies `2 == 0 (mod p)`.
- From `p - 1 == 1 (mod p)`, deduce `(p - 1) + 2 == 1 + 2 (mod p)` or `p + 1 == 3 (mod p)` using `CONG_ADD_LCANCEL`, existential instantiation and rewriting.
- Transform `3 == 0 + 3 (mod p)` to `3 == 3 + 0 (mod p)` using `CONG_SYM`, and then deduce `p + 1 == 3 + 0 (mod p)` using transitivity `CONG_TRANS`, existential instantiation and conjunction tactic.
- Using `CONG_ADD`, we can deduce `p + 1+(-1) == 3 +0+(-1) (mod p)` which reduces to `p == 2 (mod p)`.
- This further reduces to `0 == 2 (mod p)`.
- From `0 == 2 (mod p)`, it follows that `p` divides `2 - 0`, which means `p` divides `2`.
- Since `3 <= p` and `p` divides `2`, we have a contradiction, proving the theorem using `ASM_ARITH_TAC`.

### Mathematical insight
The theorem states that if `p` is greater than or equal to 3, then `p - 1` cannot be congruent to `1` modulo `p`. This arises from the fact that if `p - 1 == 1 (mod p)`, then `p` would have to divide `p - 2`, which is only possible if `p <= 2`. This contradicts the initial constraint `3 <= p`. Thus, the theorem establishes a basic property of modular arithmetic.

### Dependencies
- `ADD_CLAUSES`
- `CONG_ADD_LCANCEL`
- `CONG_SYM`
- `CONG_TRANS`
- `CONG_ADD`
- `CONG_0`
- `DIVIDES_REFL`
- `CONG_REFL`
- `DIVIDES_LE`


---

## CONG_COND_LEMMA

### Name of formal statement
CONG_COND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONG_COND_LEMMA = prove
 (`!p x y. 3 <= p /\
           ((if x then 1 else p - 1) == (if y then 1 else p - 1)) (mod p)
           ==> (x <=> y)`,
  REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[CONG_SYM; NOT_CONG_MINUS1]);;
```

### Informal statement
For all `p`, `x`, and `y`, if `3 <= p` and `(if x then 1 else p - 1)` is congruent modulo `p` to `(if y then 1 else p - 1)`, then `x` is equivalent to `y`.

### Informal sketch
The theorem states that under the condition `3 <= p`, the conditional expressions `(if x then 1 else p - 1)` and `(if y then 1 else p - 1)` being congruent modulo `p` implies that `x` and `y` are logically equivalent. The proof proceeds by considering the cases where `x` and `y` are either true or false.

- The `REPEAT GEN_TAC` part universally quantifies over `p`, `x`, and `y`.
- `REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[])` handles the four cases resulting from whether `x` and `y` are true or false by case splitting using `COND_CASES_TAC` and then simplifying using the assumptions in each case with `ASM_REWRITE_TAC[]`.
- `ASM_MESON_TAC[CONG_SYM; NOT_CONG_MINUS1]` concludes the proof using the lemmas `CONG_SYM` and `NOT_CONG_MINUS1`.

### Mathematical insight
This theorem encodes a property of modular arithmetic related to conditional expressions. It basically states that under the constraint `3 <= p`, the value of boolean variables `x` and `y` can be inferred from the result of a conditional expression taken modulo `p`.

### Dependencies
- `CONG_SYM`
- `NOT_CONG_MINUS1`


---

## FINITE_SUBCROSS

### Name of formal statement
FINITE_SUBCROSS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FINITE_SUBCROSS = prove
 (`!s:A->bool t:B->bool.
       FINITE s /\ FINITE t ==> FINITE {x,y | x IN s /\ y IN t /\ P x y}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(s:A->bool) CROSS (t:B->bool)` THEN
  ASM_SIMP_TAC[FINITE_CROSS; SUBSET; IN_CROSS; FORALL_PAIR_THM;
               IN_ELIM_PAIR_THM]);;
```

### Informal statement
For all sets `s` of type `A->bool` and `t` of type `B->bool`, if `s` and `t` are finite, then the set of pairs `{x, y | x IN s /\ y IN t /\ P x y}` is finite.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the quantifiers and implication using `REPEAT STRIP_TAC`. This moves the assumptions `FINITE s` and `FINITE t`  into the assumption list.
- Apply `MATCH_MP_TAC FINITE_SUBSET`. This step uses the theorem `FINITE_SUBSET`, which states that any subset of a finite set is finite. To apply it, we must show that `{x, y | x IN s /\ y IN t /\ P x y}` is a subset of some finite set.
- Construct the cartesian product `s CROSS t` using `EXISTS_TAC \`(s:A->bool) CROSS (t:B->bool)\``. This provides the witness `s CROSS t` for the existential in `FINITE_SUBSET`, and introduces the goal `SUBSET {x, y | x IN s /\ y IN t /\ P x y} (s CROSS t)`.
- Simplify using `ASM_SIMP_TAC` with the theorems `FINITE_CROSS`, `SUBSET`, `IN_CROSS`, `FORALL_PAIR_THM`, and `IN_ELIM_PAIR_THM`. This step proves that `{x, y | x IN s /\ y IN t /\ P x y}` is indeed a subset of `s CROSS t`, and then leverages the fact that the cartesian product of two finite sets is finite.

### Mathematical insight
This theorem states that if we have two finite sets, and we define a subset of their cartesian product based on some predicate `P`, then that subset is also finite. This is a basic and important result when dealing with cardinality and finiteness in set theory. The proof relies on the fact that subsets of finite sets are finite and the cartesian product of two finite sets is finite.

### Dependencies
- Definitions
  - `FINITE`
  - `SUBSET`
  - `IN`
  - `CROSS`
- Theorems
  - `FINITE_SUBSET`
  - `FINITE_CROSS`
  - `IN_CROSS`
  - `FORALL_PAIR_THM`
  - `IN_ELIM_PAIR_THM`


---

## CARD_SUBCROSS_DETERMINATE

### Name of formal statement
CARD_SUBCROSS_DETERMINATE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_SUBCROSS_DETERMINATE = prove
 (`FINITE s /\ FINITE t /\ (!x. x IN s /\ p(x) ==> f(x) IN t)
   ==> CARD {(x:A),(y:B) | x IN s /\ y IN t /\ y = f x /\ p x} =
       CARD {x | x IN s /\ p(x)}`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN EXISTS_TAC `\(x:A,y:B). x` THEN
  ASM_SIMP_TAC[FINITE_SUBCROSS; FORALL_PAIR_THM; EXISTS_UNIQUE_THM] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  SIMP_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[]);;
```

### Informal statement
If `s` and `t` are finite sets, and for all `x`, if `x` is in `s` and `p(x)` holds, then `f(x)` is in `t`, then the cardinality of the set of pairs `(x, y)` such that `x` is in `s`, `y` is in `t`, `y` equals `f(x)`, and `p(x)` holds, is equal to the cardinality of the set of `x` such that `x` is in `s` and `p(x)` holds.

### Informal sketch
The proof proceeds by showing that the cardinality of the set of pairs `(x, y)` satisfying the given conditions is equal to the cardinality of the set of `x` satisfying `x IN s /\ p(x)`.
- First, the theorem `CARD_IMAGE_INJ_EQ` is applied after rewriting with symmetry, suggesting that we are trying to show an equivalence of cardinalities by demonstrating a bijection (injection) between the two sets whose cardinalities are compared.
- An existential witness `\(x:A,y:B). x` is provided, which means that we can construct a mapping by taking the first component of the pair.
- Simplification is performed using facts about finite sets `FINITE_SUBCROSS`, `FORALL_PAIR_THM`, and `EXISTS_UNIQUE_THM`, which suggests manipulation of quantifiers and finiteness conditions.
- Rewriting takes place with `EXISTS_PAIR_THM` and `IN_ELIM_PAIR_THM`, indicating rewriting rules regarding existential quantifiers over pairs and membership in a pair.
- Further simplification is achieved with `IN_ELIM_THM` and `PAIR_EQ`, suggesting rewriting rules for set membership and pair equality.
- Finally, `ASM_MESON_TAC` is invoked, implying that the proof is completed by automated first-order reasoning using assumptions in the context and the specified facts.

### Mathematical insight
This theorem essentially states that if you have a function `f` mapping elements of a set `s` (subject to a condition `p`) into a set `t`, then the number of pairs `(x, f(x))` in the set `s x t` where `x` satisfies `p` is the same as the number of `x` in `s` which satisfies `p`. Effectively, the function `f` induces a natural bijection between `{x | x IN s /\ p(x)}` and `{(x, y) | x IN s /\ y IN t /\ y = f x /\ p x}`. The condition `!x. x IN s /\ p(x) ==> f(x) IN t` guarantees that the range of `f` restricted to elements in `s` satisfying `p` is included in `t`.

### Dependencies
- Theorems: `CARD_IMAGE_INJ_EQ`, `FORALL_PAIR_THM`, `EXISTS_UNIQUE_THM`, `EXISTS_PAIR_THM`, `IN_ELIM_PAIR_THM`
- Definitions: `FINITE_SUBCROSS`, `IN_ELIM_THM`, `PAIR_EQ`

### Porting notes (optional)
The main challenge in porting this theorem is likely to be the automation provided by `ASM_MESON_TAC`. You may need to manually prove the last step by unfolding definitions and applying introduction/elimination rules for quantifiers and logical connectives. The handling of finiteness may also require special attention, depending on how finiteness is defined in the target proof assistant.


---

## CARD_SUBCROSS_SWAP

### Name of formal statement
CARD_SUBCROSS_SWAP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CARD_SUBCROSS_SWAP = prove
 (`CARD {y,x | y IN 1..m /\ x IN 1..n /\ P x y} =
   CARD {x,y | x IN 1..n /\ y IN 1..m /\ P x y}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ_EQ THEN
  EXISTS_TAC `\(x:num,y:num). (y,x)` THEN
  ASM_SIMP_TAC[FINITE_SUBCROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN
  SIMP_TAC[IN_ELIM_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;
```
### Informal statement
For any natural numbers `m` and `n`, and any predicate `P` on natural numbers, the cardinality of the set of pairs `(y, x)` such that `y` is in the range `1` to `m`, `x` is in the range `1` to `n`, and `P x y` holds, is equal to the cardinality of the set of pairs `(x, y)` such that `x` is in the range `1` to `n`, `y` is in the range `1` to `m`, and `P x y` holds.

### Informal sketch
The proof shows that swapping the order of the variables in the predicate does not change the cardinality of the resulting set.
- Start by stripping the goal.
- Then, apply `CARD_IMAGE_INJ_EQ`. This requires finding an injective mapping from one set to the other.
- Provide the swapping function `(x, y) |-> (y, x)` as the witness for the existence of such an injective mapping.
- Simplify using assumptions that the subcrosses are finite (`FINITE_SUBCROSS`, `FINITE_NUMSEG`).
- Rewrite the goal involving existence and universal quantifiers within pairs using theorems `EXISTS_UNIQUE_THM`, `FORALL_PAIR_THM`, `EXISTS_PAIR_THM`.
- Simplify pairs using `IN_ELIM_PAIR_THM` and `PAIR_EQ`.
- Finally, apply `MESON_TAC` to complete the proof.

### Mathematical insight
This theorem demonstrates that when computing the cardinality of a set defined by a predicate over a cross-product of finite sets, the order in which the variables are considered does not affect the final cardinality, as long as the predicate itself is adjusted accordingly. This highlights the symmetry inherent in counting elements satisfying a relation, regardless of the order in which the elements are presented.

### Dependencies
- `CARD_IMAGE_INJ_EQ`
- `FINITE_SUBCROSS`
- `FINITE_NUMSEG`
- `EXISTS_UNIQUE_THM`
- `FORALL_PAIR_THM`
- `EXISTS_PAIR_THM`
- `IN_ELIM_PAIR_THM`
- `PAIR_EQ`

### Porting notes (optional)
- The use of `MESON_TAC` suggests that the final steps of the proof involve first-order reasoning and could potentially be automated in other proof assistants with similar automated reasoning capabilities.
- The key idea is the swapping function `(x, y) |-> (y, x)`, which might need to be explicitly defined and proven injective in other proof assistants if such a result is not already available.


---

## IS_QUADRATIC_RESIDUE

### Name of formal statement
IS_QUADRATIC_RESIDUE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IS_QUADRATIC_RESIDUE = prove
 (`!a p. ~(p = 0) /\ ~(p divides a)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_quadratic_residue; EXP_2] THEN
  DISCH_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN EXISTS_TAC `x MOD p` THEN
  ASM_SIMP_TAC[DIVISION] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LT_NZ; GSYM DIVIDES_MOD; CONG_DIVIDES; DIVIDES_LMUL];
    UNDISCH_TAC `(x * x == a) (mod p)` THEN
    ASM_SIMP_TAC[CONG; MOD_MULT_MOD2]]);;
```

### Informal statement
For all numbers `a` and `p`, if `p` is not equal to 0 and `p` does not divide `a`, then `a` is a quadratic residue modulo `p` if and only if there exists a number `x` such that `0 < x`, `x < p`, and `x` squared is congruent to `a` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- Generalize the goal over `a` and `p`.
- Rewrite using the definition of `is_quadratic_residue` and `EXP_2`.
- Discharge the assumptions.
- Split the equivalence goal into two implications.
- The first direction is proved using basic assumption handling. Choose `x:num` from the existential by discharging the assumption (the left-hand side of the equivalence). Instantiate the existential quantifier on the right-hand side with `x MOD p`. Simplify the goal using the properties of integer division (`DIVISION`). Prove the two resulting subgoals:
  - The first subgoal `0 < x MOD p /\ x MOD p < p` is proved by discharging the assumption `~(p = 0) /\ ~(p divides a)` and then using theorems like `LT_NZ`, `DIVIDES_MOD`, `CONG_DIVIDES`, and `DIVIDES_LMUL`.
  - The second subgoal `(x MOD p) EXP 2 == a (mod p)` is proved by rewriting with congruence properties (`CONG`, `MOD_MULT_MOD2`) to reach the hypothesis `(x * x == a) (mod p)`.

### Mathematical insight
This theorem provides a concrete way to check if a number `a` is a quadratic residue modulo `p`. It states that `a` is a quadratic residue modulo `p` if there exists an `x` within the range `(0, p)` such that `x^2` is congruent to `a` modulo `p`. The additional condition that `p` should not divide `a`, rules out the degenerate case of `0` being a quadratic residue. Note that `is_quadratic_residue` is defined in terms of the existence of a number `x` without any restriction on its range and then the theorem gives an equivalent condition which constrains `x` to the interval `(0,p)`.

### Dependencies
- Definitions: `is_quadratic_residue`, `EXP_2`
- Theorems: `LT_NZ`, `DIVIDES_MOD`, `CONG_DIVIDES`, `DIVIDES_LMUL`, `CONG`, `MOD_MULT_MOD2`, `DIVISION`


---

## IS_QUADRATIC_RESIDUE_COMMON

### Name of formal statement
IS_QUADRATIC_RESIDUE_COMMON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IS_QUADRATIC_RESIDUE_COMMON = prove
 (`!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IS_QUADRATIC_RESIDUE THEN
  ASM_MESON_TAC[COPRIME_PRIME; DIVIDES_REFL; PRIME_0]);;
```

### Informal statement
For all `a` and `p`, if `p` is prime and `a` is coprime to `p`, then `a` is a quadratic residue modulo `p` if and only if there exists an `x` such that `0 < x`, `x < p`, and `x^2 == a (mod p)`.

### Informal sketch
The proof proceeds as follows:
- The main goal is to prove the equivalence between `a is_quadratic_residue (mod p)` and the existence of an `x` in the range `0 < x < p` such that `x^2 == a (mod p)`.
- We begin with stripping the quantifiers and implication using `REPEAT STRIP_TAC`.
- `MATCH_MP_TAC IS_QUADRATIC_RESIDUE` applies the definition of `is_quadratic_residue`. The statement `IS_QUADRATIC_RESIDUE` likely defines `a is_quadratic_residue (mod p)` as the existence of some `x` such that `(x EXP 2 == a) (mod p)` and `coprime (x, p)`.
- `ASM_MESON_TAC[COPRIME_PRIME; DIVIDES_REFL; PRIME_0]` then uses an automated theorem prover (`ASM_MESON_TAC`) to discharge the remaining goals. This part of the proof likely deals with showing that if such an `x` exists with `(x EXP 2 == a) (mod p)`, we can always find one in the range `0 < x < p`, and with `coprime (x,p)`. `COPRIME_PRIME` likely states that if `p` is prime, then any number less than `p` is coprime to `p`. `DIVIDES_REFL` is probably reflexivity of divides. `PRIME_0` probably that 0 is not a prime. This suggests the step handles edge cases appropriately and establishes any necessary properties using the provided lemmas or theorems.

### Mathematical insight
This theorem provides the standard definition of a quadratic residue. Given a prime number `p` and an integer `a` coprime to `p`, `a` is a quadratic residue modulo `p` if there exists an integer `x` whose square is congruent to `a` modulo `p`. This theorem provides a constructive way to check quadratic residuosity by checking for the existence of such an `x` within the range `0 < x < p`.

### Dependencies
- Definitions:
  - `IS_QUADRATIC_RESIDUE`
- Theorems:
  - `COPRIME_PRIME`
  - `DIVIDES_REFL`
  - `PRIME_0`


---

## QUADRATIC_RESIDUE_PAIR_ADD

### Name of formal statement
QUADRATIC_RESIDUE_PAIR_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_PAIR_ADD = prove
 (`!p x y. prime p
           ==> (((x + y) EXP 2 == x EXP 2) (mod p) <=>
                 p divides y \/ p divides (2 * x + y))`,
  REWRITE_TAC[NUM_RING `(x + y) EXP 2 = y * (y + 2 * x) + x EXP 2`] THEN
  SIMP_TAC[CONG_ADD_RCANCEL_EQ_0; CONG_0; PRIME_DIVPROD_EQ; ADD_SYM]);;
```
### Informal statement
For all primes `p` and all numbers `x` and `y`, if `p` is prime, then `(x + y)^2` is congruent to `x^2` modulo `p` if and only if `p` divides `y` or `p` divides `2 * x + y`.

### Informal sketch
The proof proceeds as follows:
- Expand `(x + y)^2` using `NUM_RING `(x + y) EXP 2 = y * (y + 2 * x) + x EXP 2`` and rewrite the congruence. Specifically, rewrite `(x + y)^2 == x^2 (mod p)` as `y * (y + 2 * x) + x^2 == x^2 (mod p)`.
- Use `CONG_ADD_RCANCEL_EQ_0` to subtract `x^2` from both sides of the congruence, resulting in `y * (y + 2 * x) == 0 (mod p)`.
- Rewrite the congruence `y * (y + 2 * x) == 0 (mod p)` to `p divides (y * (y + 2 * x))` using `CONG_0`.
- Apply the fact that if a prime `p` divides a product, it must divide one of the factors, using `PRIME_DIVPROD_EQ`. This transforms `p divides (y * (y + 2 * x))` into `p divides y \/ p divides (2 * x + y)`.
- Use `ADD_SYM` to reorder `2 * x + y` as `y + 2 * x` consistently.

### Mathematical insight
This theorem connects the arithmetic notion of quadratic residues with divisibility by a prime. It states a condition to determine when squaring `x + y` results in a number congruent to `x^2` modulo a prime `p`. This provides insight into modular arithmetic and related algebraic structures. The condition `p divides y \/ p divides (2 * x + y)` essentially characterizes pairs `(x, y)` such that `x + y` and `x` are congruent up to a square.

### Dependencies
- Theorems: `PRIME_DIVPROD_EQ`
- Tactic: `NUM_RING `(x + y) EXP 2 = y * (y + 2 * x) + x EXP 2``, `CONG_ADD_RCANCEL_EQ_0`, `CONG_0`, `ADD_SYM`


---

## QUADRATIC_RESIDUE_PAIR

### Name of formal statement
QUADRATIC_RESIDUE_PAIR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_PAIR = prove
 (`!p x y. prime p
           ==> ((x EXP 2 == y EXP 2) (mod p) <=>
                 p divides (x + y) \/ p divides (dist(x,y)))`,
  GEN_TAC THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [MESON_TAC[DIST_SYM; CONG_SYM; ADD_SYM]; ALL_TAC] THEN
  REWRITE_TAC[LE_EXISTS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN ASM_SIMP_TAC[QUADRATIC_RESIDUE_PAIR_ADD] THEN
  REWRITE_TAC[DIST_RADD_0; ARITH_RULE `x + x + d = 2 * x + d`; DISJ_ACI]);;
```

### Informal statement
For all primes `p` and for all `x` and `y`, `x` squared is congruent to `y` squared modulo `p` if and only if `p` divides `x + y` or `p` divides the absolute difference between `x` and `y`.

### Informal sketch
The proof proceeds as follows:
- Assume `p` is prime.
- Prove both directions of the equivalence.
  - First, assume `x^2 == y^2 (mod p)`.  Without loss of generality, assume `x <= y`. This allows us to rewrite the congruence as `p` divides `y^2 - x^2`, which factors to `p` divides `(y-x)(y+x)`. Since `p` is prime, `p` divides `y-x` or `p` divides `y+x`.
  - Second, assume `p` divides `x + y` or `p` divides `dist(x, y)`. For the case where `p` divides `x+y`, we prove `x^2 == y^2 (mod p)` via `QUADRATIC_RESIDUE_PAIR_ADD` which is based on the assumption that if `p` divides `x+y`, then `x == -y (mod p)`. For the case where `p` divides `dist(x, y)`, we prove `x^2 == y^2 (mod p)` easily.
- Use arithmetic simplification and properties of divisibility and congruence to complete the proof.

### Mathematical insight
This theorem relates quadratic residues modulo a prime `p` to the linear factors of the difference of squares. It provides a useful criterion for determining when two squares are congruent modulo a prime and is a fundamental result in number theory.

### Dependencies
- `DIST_SYM`
- `CONG_SYM`
- `ADD_SYM`
- `LE_EXISTS`
- `QUADRATIC_RESIDUE_PAIR_ADD`
- `DIST_RADD_0`
- `ARITH_RULE`
- `DISJ_ACI`


---

## IS_QUADRATIC_RESIDUE_PAIR

### Name of formal statement
IS_QUADRATIC_RESIDUE_PAIR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IS_QUADRATIC_RESIDUE_PAIR = prove
 (`!a p. prime p /\ coprime(a,p)
         ==> (a is_quadratic_residue (mod p) <=>
                 ?x y. 0 < x /\ x < p /\ 0 < y /\ y < p /\ x + y = p /\
                       (x EXP 2 == a) (mod p) /\ (y EXP 2 == a) (mod p) /\
                       !z. 0 < z /\ z < p /\ (z EXP 2 == a) (mod p)
                           ==> z = x \/ z = y)`,
  SIMP_TAC[IS_QUADRATIC_RESIDUE_COMMON] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`x:num`; `p - x:num`] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `0 < x /\ x < p ==> 0 < p - x /\ p - x < p /\ x + (p - x) = p`] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP QUADRATIC_RESIDUE_PAIR) THENL
   [DISCH_THEN(MP_TAC o SPECL [`x:num`; `p - x:num`]) THEN
    ASM_SIMP_TAC[ARITH_RULE `x < p ==> x + (p - x) = p`; DIVIDES_REFL] THEN
    ASM_MESON_TAC[CONG_TRANS; CONG_SYM];
    DISCH_THEN(MP_TAC o SPECL [`x:num`; `z:num`]) THEN
    SUBGOAL_THEN `(x EXP 2 == z EXP 2) (mod p)` (fun th -> SIMP_TAC[th]) THENL
     [ASM_MESON_TAC[CONG_TRANS; CONG_SYM]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN (MP_TAC o MATCH_MP DIVIDES_CASES)) THEN
    REWRITE_TAC[ADD_EQ_0; DIST_EQ_0] THEN REWRITE_TAC[dist] THEN
    ASM_ARITH_TAC]);;
```
### Informal statement
For all `a` and `p`, if `p` is a prime number and `a` and `p` are coprime, then `a` is a quadratic residue modulo `p` if and only if there exist natural numbers `x` and `y` such that `0 < x`, `x < p`, `0 < y`, `y < p`, `x + y = p`, `x^2` is congruent to `a` modulo `p`, `y^2` is congruent to `a` modulo `p`, and for all `z`, if `0 < z`, `z < p`, and `z^2` is congruent to `a` modulo `p`, then `z = x` or `z = y`.

### Informal sketch
The proof proceeds as follows:
- Starts by simplifying using `IS_QUADRATIC_RESIDUE_COMMON`.
- The main proof is an equivalence, so it is broken into two directions.
- The forward direction (=>) is treated by assuming `a` is a quadratic residue modulo `p` and choosing an `x` such that `x^2` is congruent to `a` modulo `p`, where `0 < x` and `x < p`. Then `y` is instantiated as `p - x`. We verify `y` satisfies `0 < y`, `y < p`, `x + y = p`, and `y^2` is congruent to `a` modulo `p`. Then using the `QUADRATIC_RESIDUE_PAIR` theorem, we show that all `z` satisfying `0 < z`, `z < p` and `z^2` congruent to `a` modulo `p` are either `x` or `y`.
- The backward direction (<=) is proven by showing that if there exist such `x` and `y`, then `a` is a `quadratic_residue`.

### Mathematical insight
This theorem establishes a key property of quadratic residues modulo a prime `p`. Namely, if `a` is a quadratic residue modulo `p`, then the congruence `x^2 == a mod p` has exactly two solutions in the range `0 < x < p`, which are `x` and `p - x`. The existence of exactly two roots is a crucial element in developing the theory of quadratic residues, and this result can be used in algorithms or proofs involving quadratic residues.

### Dependencies
- `IS_QUADRATIC_RESIDUE_COMMON`
- `QUADRATIC_RESIDUE_PAIR`
- `DIVIDES_REFL`
- `CONG_TRANS`
- `CONG_SYM`
- `DIVIDES_CASES`
- `ADD_EQ_0`
- `DIST_EQ_0`


---

## QUADRATIC_RESIDUE_PAIR_PRODUCT

### Name of formal statement
QUADRATIC_RESIDUE_PAIR_PRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_PAIR_PRODUCT = prove
 (`!p x. 0 < x /\ x < p /\ (x EXP 2 == a) (mod p)
         ==> (x * (p - x) == (p - 1) * a) (mod p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MP (ARITH_RULE `x < p ==> 1 <= p`)) THEN
  SUBGOAL_THEN `(x * (p - x) + x EXP 2 == a * (p - 1) + a * 1) (mod p)`
  MP_TAC THENL
   [ASM_SIMP_TAC[LEFT_SUB_DISTRIB; EXP_2; SUB_ADD;
                 LE_MULT_LCANCEL; LT_IMP_LE] THEN
    REWRITE_TAC[cong; nat_mod] THEN ASM_MESON_TAC[ADD_SYM; MULT_SYM];
    REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_MESON_TAC[CONG_ADD; CONG_TRANS; CONG_SYM; CONG_REFL; MULT_SYM;
                  CONG_ADD_RCANCEL]]);;
```

### Informal statement
For all natural numbers `p` and `x`, if `0 < x` and `x < p` and `x^2` is congruent to `a` modulo `p`, then `x * (p - x)` is congruent to `(p - 1) * a` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- Assume `0 < x`, `x < p`, and `x^2 == a (mod p)`.
- Show that `x * (p - x) + x^2 == a * (p - 1) + a * 1 (mod p)`. This is the `SUBGOAL_THEN` tactic in the original proof.
- Show that `x * (p - x) + x^2 == a * (p - 1) + a * 1 (mod p)` using arithmetic simplification and the assumed congruence `x^2 == a (mod p)`.
- Rewrite `x * (p - x)` as `x * p - x^2` and `a * (p - 1)` as `a * p - a`, which simplifies the congruence to `x * p - x^2 + x^2 == a * p - a + a (mod p)`.  This further simplifies to `x * p == a * p (mod p)`.
- Use modular arithmetic to show that `x * p == 0 (mod p)` and `a * p == 0 (mod p)`.  Therefore, `x * p == a * p (mod p)`.

### Mathematical insight
The theorem demonstrates a property of quadratic residues modulo `p`. If `x` is a solution to the congruence `x^2 == a (mod p)`, then `p - x` is also a solution.  The theorem relates the product of these two solutions, `x * (p - x)`, to `(p - 1) * a` modulo `p`. This identity might be useful in analyzing the structure of quadratic residues and their relationships.

### Dependencies
- `LEFT_SUB_DISTRIB`
- `EXP_2`
- `SUB_ADD`
- `LE_MULT_LCANCEL`
- `LT_IMP_LE`
- `cong`
- `nat_mod`
- `ADD_SYM`
- `MULT_SYM`
- `MULT_CLAUSES`
- `CONG_ADD`
- `CONG_TRANS`
- `CONG_SYM`
- `CONG_REFL`
- `ARITH_RULE`

### Porting notes (optional)
The proof relies heavily on rewriting and simplification with respect to modular arithmetic.  A challenge for porting might be ensuring that the target proof assistant has similar automation for arithmetic operations and congruence manipulation. The `ASM_MESON_TAC` calls suggest that some first-order reasoning about equality and arithmetic properties is also involved.


---

## legendre

### Name of formal statement
- legendre

### Type of the formal statement
- new_definition

### Formal Content
- The full HOL Light statement will be inserted here **after generation**.
```ocaml
let legendre = new_definition
 `(legendre:num#num->int)(a,p) =
        if ~(coprime(a,p)) then &0
        else if a is_quadratic_residue (mod p) then &1
        else --(&1)`;;
```

### Informal statement
- Define the Legendre symbol, denoted as `legendre(a, p)`, where `a` and `p` are natural numbers. The value of `legendre(a, p)` is an integer. If `a` and `p` are not coprime, `legendre(a, p)` is 0. Otherwise, if `a` is a quadratic residue modulo `p`, then `legendre(a, p)` is 1; if `a` is not a quadratic residue modulo `p`, then `legendre(a, p)` is -1.

### Informal sketch
- The definition is a direct formalization of the standard mathematical definition of the Legendre symbol, discriminating between cases based on coprimality and quadratic residuosity.
- First check if `a` and `p` are coprime using `coprime(a, p)`.
- If they are not comprime, then `legendre(a, p)` is defined to be 0.
- Otherwise, check if `a` is a quadratic residue modulo `p` using `is_quadratic_residue (mod p)`.
- If it is, then `legendre(a, p)` is 1.
- Otherwise, it is -1.

### Mathematical insight
- The Legendre symbol is a fundamental construction in number theory, indicating whether an integer `a` is a quadratic residue modulo a prime number `p`. It encapsulates the quadratic reciprocity law and related theorems around prime numbers. This symbol is a building block for defining other number-theoretic functions and stating more elaborate theorems.

### Dependencies
- Definitions:
    - `coprime`
    - `is_quadratic_residue`


---

## nproduct

### Name of formal statement
nproduct

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let nproduct = new_definition `nproduct = iterate ( * )`;;
```

### Informal statement
The function `nproduct` is defined to be the result of iterating the multiplication operator `(*)` (i.e., the function that maps `x` and `y` to their product `x * y`).

### Informal sketch
The definition introduces `nproduct` as an iterated application of multiplication. Thus, `nproduct n f` computes the product of `f(0) * f(1) * ... * f(n-1)`. There is no proof sketch to provide, since this is a definition.

### Mathematical insight
The function `nproduct` generalizes the mathematical concept of computing a product of a sequence of numbers. Note that the iteration starts at `0` and goes up to `n-1`.

### Dependencies
- `iterate`
- `*`

### Porting notes (optional)
Most proof assistants have similar constructs for function iteration; the primary challenge might be ensuring that the correct range (0 to n-1) is used for the iterated product. Note also potential differences in how multiplication is represented (e.g., as an infix operator or a function), and ensuring that the iteration is correctly applied in that context.


---

## CONG_NPRODUCT

### Name of formal statement
CONG_NPRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONG_NPRODUCT = prove
 (`!f g s. FINITE s /\ (!x. x IN s ==> (f x == g x) (mod n))
           ==> (nproduct s f == nproduct s g) (mod n)`,
  REWRITE_TAC[nproduct] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_RELATED MONOIDAL_MUL) THEN
  SIMP_TAC[CONG_REFL; CONG_MULT]);;
```

### Informal statement
For all functions `f` and `g`, and for all finite sets `s`, if `f(x)` is congruent to `g(x)` modulo `n` for every `x` in `s`, then the product of `f(x)` over `s` is congruent to the product of `g(x)` over `s` modulo `n`.

### Informal sketch
- The proof begins by rewriting the `nproduct` term using its definition.
- It then applies an iterated form of the `MONOIDAL_MUL` theorem which is an instance of `ITERATE_RELATED`. Specifically, it performs a Match-MP operation.
- Finally, it simplifies the resulting expression using `CONG_REFL`  (congruence is reflexive) and `CONG_MULT` (congruence is preserved under multiplication).

### Mathematical insight
This theorem establishes that congruence modulo `n` is preserved by the `nproduct` function, which computes the product of a function over a finite set modulo `n`. This is fundamental for modular arithmetic and demonstrates that if two functions agree modulo `n` on a finite set, their products over that set will also agree modulo `n`.

### Dependencies
- Definitions: `nproduct`
- Theorems: `CONG_REFL`, `CONG_MULT`, `MONOIDAL_MUL`, `ITERATE_RELATED`


---

## NPRODUCT_DELTA_CONST

### Name of formal statement
NPRODUCT_DELTA_CONST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_DELTA_CONST = prove
 (`!c s. FINITE s
         ==> nproduct s (\x. if p(x) then c else 1) =
             c EXP (CARD {x | x IN s /\ p(x)})`,
  let lemma1 = prove
   (`{x | x IN a INSERT s /\ p(x)} =
     if p(a) then a INSERT {x | x IN s /\ p(x)}
     else {x | x IN s /\ p(x)}`,
    COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[])
  and lemma2 = prove
   (`FINITE s ==> FINITE {x | x IN s /\ p(x)}`,
    MATCH_MP_TAC(ONCE_REWRITE_RULE[TAUT `a /\ b ==> c <=> b ==> a ==> c`]
                FINITE_SUBSET) THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM]) in
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; CARD_CLAUSES; EXP; NOT_IN_EMPTY;
           SET_RULE `{x | F} = {}`; lemma1] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; IN_ELIM_THM; lemma2; EXP; MULT_CLAUSES]);;
```
### Informal statement
For any constant `c` and any set `s`, if `s` is finite, then the product of the values defined by the function that maps `x` to `c` if `p(x)` holds and to 1 otherwise, is equal to `c` raised to the power of the cardinality of the set of elements `x` in `s` for which `p(x)` holds.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `s`.
- Base case: `s` is empty. The product is 1, and the cardinality of the empty set is 0, so `c` to the power of 0 is 1, which is the desired result.
- Inductive step: Assume the theorem holds for all subsets of `s`. We consider an arbitrary element `a` and the set `INSERT a s`.
  - Decompose the product over `INSERT a s` into the product over `s` multiplied by the factor for `a`, which is `c` if `p(a)` holds and 1 otherwise.
  - Consider two cases: `p(a)` holds and `p(a)` does not hold.
    - If `p(a)` holds, then the product becomes `c * (c EXP CARD {x | x IN s /\ p(x)})`. We then use the lemma `CARD (a INSERT {x | x IN s /\ p(x)}) = CARD {x | x IN s /\ p(x)} + 1` and `EXP` to show that this equals `c EXP CARD {x | x IN INSERT a s /\ p(x)}`.
    - if `p(a)` does not hold, the product reduces to `c EXP CARD {x | x IN s /\ p(x)}`. In this case, the set `{x | x IN INSERT a s /\ p(x)}` is equal to `{x | x IN s /\ p(x)}`, which ensures that we have the desired result.
Two helper lemmas are proved.
- Lemma 1: `{x | x IN a INSERT s /\ p(x)} = if p(a) then a INSERT {x | x IN s /\ p(x)} else {x | x IN s /\ p(x)}`. This rewrites the filtering of the insertion of 'a' into 's' based on predicate 'p'.
- Lemma 2: `FINITE s ==> FINITE {x | x IN s /\ p(x)}`. This asserts that a subset of a finite set is also finite.

### Mathematical insight
This theorem generalizes the fact that the product of a constant `c` over a set is `c` raised to the power of the cardinality of the set. This version only considers the elements for which predicate `p` is true, and the rest of the elements are considered to be 1. Thus, if `p` is always true, this equation simplifies to the product over the constant 'c'. Otherwise, it only raises `c` to the power of the cardinality of subset where `p` holds.

### Dependencies
- Theorems/Definitions:
  - `FINITE`
  - `nproduct`
  - `CARD`
  - `EXP`
  - `INSERT`
  - `IN`
  - `NPRODUCT_CLAUSES`
  - `CARD_CLAUSES`
  - `NOT_IN_EMPTY`
  - `SET_RULE`
  - `EXTENSION`
  - `IN_INSERT`
  - `IN_ELIM_THM`
  - `FINITE_INDUCT_STRONG`
  - `SUBSET`
  - `MULT_CLAUSES`

### Porting notes (optional)
- The proof uses `FINITE_INDUCT_STRONG`. Be sure to create equivalent induction tactic.
- The proof depends on rewriting with various set equalities. Be sure to verify corresponding theory.


---

## COPRIME_NPRODUCT

### Name of formal statement
COPRIME_NPRODUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COPRIME_NPRODUCT = prove
 (`!f p s. FINITE s /\ (!x. x IN s ==> coprime(p,f x))
           ==> coprime(p,nproduct s f)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; COPRIME_1; IN_INSERT; COPRIME_MUL]);;
```
### Informal statement
For any function `f`, any prime number `p`, and any finite set `s`, if for all `x` in `s`, `p` is coprime to `f x`, then `p` is coprime to the product of `f x` over the set `s`.

### Informal sketch
The proof proceeds by strong induction on the finiteness of the set `s`.

- The base case, when the set `s` is empty, follows because `nproduct s f` equals 1, and `coprime(p, 1)` holds for any `p`.
- In the inductive step, assuming the theorem holds for all subsets of a set `s`, we wish to show `!f p. (!x. x IN s ==> coprime(p,f x)) ==> coprime(p,nproduct s f)`.
    - We decompose `s` into `INSERT x s'` where `x` is an element of `s` and `s'` is the remainder of the set `s` i.e. s = {x} U s'.
    - The hypothesis `!x. x IN s ==> coprime(p, f x)` implies `coprime(p, f x)` and `!x. x IN s' ==> coprime(p, f x)`.
    - By the inductive hypothesis, `coprime(p, nproduct s' f)`.
    - Since `nproduct (INSERT x s') f = f x * nproduct s' f`, and we have `coprime(p, f x)` and `coprime(p, nproduct s' f)`, we can conclude `coprime(p, nproduct (INSERT x s') f)` by the theorem that if `coprime(p, a)` and `coprime(p, b)` then `coprime(p, a * b)`.

### Mathematical insight
The theorem provides a way to deduce coprimality of a prime number `p` with a product based on the coprimality of `p` with each factor in the product. This is a fundamental result used to establish unique factorization and other properties in number theory.

### Dependencies
- `FINITE_INDUCT_STRONG`
- `NPRODUCT_CLAUSES`
- `COPRIME_1`
- `IN_INSERT`
- `COPRIME_MUL`
- `IMP_CONJ`


---

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
For all natural numbers `n`, the factorial of `n` (denoted `FACT(n)`) is equal to the product of the numbers from `1` to `n`, where the product is denoted `nproduct(1..n) (\i. i)`.

### Informal sketch
The proof proceeds by mathematical induction on `n`.
- Base Case: For `n = 0`, we show that `FACT(0) = nproduct(1..0) (\i. i)`. The left-hand side is `1` by the definition of `FACT`. The right-hand side is `1` because the product over an empty range is `1`.
- Inductive Step: Assume `FACT(n) = nproduct(1..n) (\i. i)`. We must prove `FACT(SUC n) = nproduct(1..SUC n) (\i. i)`.
  - By definition of `FACT`, `FACT(SUC n) = (SUC n) * FACT(n)`.
  - By the inductive hypothesis, `FACT(SUC n) = (SUC n) * nproduct(1..n) (\i. i)`.
  - By properties of `nproduct`, `nproduct(1..SUC n) (\i. i) = nproduct(1..n) (\i. i) * (SUC n)`.
  - Therefore, `FACT(SUC n) = nproduct(1..SUC n) (\i. i)`.

### Mathematical insight
This theorem provides an alternative characterization of the factorial function using the `nproduct` function, which represents the product of a function over a numerical segment. This connection is useful because it relates the factorial to more general product operations.

### Dependencies
- `FACT`
- `NUMSEG_CLAUSES`
- `ARITH`
- `NPRODUCT_CLAUSES`
- `ARITH_RULE`
- `FINITE_NUMSEG`
- `IN_NUMSEG`


---

## NPRODUCT_PAIRUP_INDUCT

### Name of formal statement
NPRODUCT_PAIRUP_INDUCT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NPRODUCT_PAIRUP_INDUCT = prove
 (`!f r n s k. s HAS_SIZE (2 * n) /\
               (!x:A. x IN s ==> ?!y. y IN s /\ ~(y = x) /\
                                      (f(x) * f(y) == k) (mod r))
               ==> (nproduct s f == k EXP n) (mod r)`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[MULT_CLAUSES; HAS_SIZE_0; NPRODUCT_CLAUSES; EXP; CONG_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
   [ASM_MESON_TAC[HAS_SIZE_0; ARITH_RULE `2 * n = 0 <=> n = 0`; HAS_SIZE];
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - 1 < n`] THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[ASSUME `(a:A) IN s`] THEN
  REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`(s DELETE a) DELETE (b:A)`; `k:num`]) THEN
  SUBGOAL_THEN `s = (a:A) INSERT (b INSERT (s DELETE a DELETE b))`
   (ASSUME_TAC o SYM) THENL [ASM SET_TAC[]; ALL_TAC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(s:A->bool) HAS_SIZE 2 * n` THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
        [SYM th]) THEN
      SIMP_TAC[HAS_SIZE; FINITE_INSERT; CARD_CLAUSES; FINITE_DELETE;
               IMP_CONJ; IN_DELETE; IN_INSERT] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN ASM_REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
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
  DISCH_TAC THEN EXPAND_TAC "s" THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[HAS_SIZE]) THEN
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_INSERT; FINITE_DELETE] THEN
  REWRITE_TAC[IN_INSERT; IN_DELETE; MULT_CLAUSES] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP
   (ARITH_RULE `~(n = 0) ==> n = SUC(n - 1)`)) THEN
  ASM_REWRITE_TAC[MULT_ASSOC; EXP] THEN DISCH_TAC THEN
  MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For all functions `f` from elements of type `A` to numbers, all numbers `r`, `n`, `k`, and all sets `s` of type `A`, if `s` has size `2 * n` and for all `x` in `s`, there exists a unique `y` in `s` such that `x` is not equal to `y` and `f(x) * f(y)` is congruent to `k` modulo `r`, then the product of `f` over `s` is congruent to `k` raised to the power of `n` modulo `r`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case 1: `n = 0`. If `n` is 0, then the size of `s` is `2 * 0 = 0`, so `s` is the empty set. The product of `f` over the empty set is 1, and `k EXP 0` is also 1. The congruence holds because `1 == 1 (mod r)`.
- Base case 2: `s` is the empty set {}. If `s` is empty, then it has size `0`, so `2 * n = 0`, thus `n = 0`. The rest of the proof is analogous to Base case 1.
- Inductive step: Assume the theorem holds for `n - 1`. Given a set `s` of size `2 * n` satisfying the pairing condition, pick an element `a` from `s`. By the pairing condition, there exists a unique element `b` in `s` such that `f(a) * f(b) == k (mod r)`. Remove `a` and `b` from `s` to form a new set `s' = (s DELETE a) DELETE b`. Then `s'` has size `2 * (n - 1)`, and we show that `s'` satisfies the pairing condition for `n - 1`. By the inductive hypothesis, `nproduct s' f == k EXP (n - 1) (mod r)`. We can express `s` as `(a:A) INSERT (b INSERT (s DELETE a DELETE b)`. Finally, `nproduct s f == f(a) * f(b) * nproduct s' f == k * (k EXP (n - 1)) == k EXP n (mod r)`.

### Mathematical insight
This theorem provides a way to compute the product of a function over a set, given that the elements of the set can be paired up in such a way that the product of the function applied to each pair is congruent to a constant `k` modulo `r`. This is useful when directly computing the product is difficult, but finding such a pairing is easier.

### Dependencies
- `HAS_SIZE`
- `NPRODUCT_CLAUSES`
- `EXP`
- `CONG_REFL`
- `HAS_SIZE_0`
- `MEMBER_NOT_EMPTY`,
- `FINITE_INSERT`
- `FINITE_DELETE`
- `CARD_CLAUSES`
- `IMP_CONJ`
- `IN_DELETE`
- `IN_INSERT`
- `EXISTS_UNIQUE_THM`
- `MULT_SYM`
- `MULT_ASSOC`

### Porting notes (optional)
The proof relies on rewriting with set operations (`INSERT`, `DELETE`), cardinality and arithmetic reasoning. The handling of `EXISTS_UNIQUE` might need specific attention depending on the target proof assistant.


---

## QUADRATIC_NONRESIDUE_FACT

### Name of formal statement
QUADRATIC_NONRESIDUE_FACT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUADRATIC_NONRESIDUE_FACT = prove
 (`!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ ~(a is_quadratic_residue (mod p))
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 1)) (mod p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_NPRODUCT] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN MATCH_MP_TAC NPRODUCT_PAIRUP_INDUCT THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o
      GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    SIMP_TAC[SUC_SUB1; DIV_MULT; ARITH] THEN
    REWRITE_TAC[HAS_SIZE; FINITE_NUMSEG; CARD_NUMSEG; ADD_SUB];
    ALL_TAC] THEN
  ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; ARITH_RULE `1 <= x <=> 0 < x`;
               ARITH_RULE `~(p = 0) ==> (x <= p - 1 <=> x < p)`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `p:num`; `x:num`] CONG_SOLVE_UNIQUE_NONTRIVIAL) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[is_quadratic_residue; EXP_2]);;
```
### Informal statement
For all numbers `a` and `p`, if `p` is prime and `p` is odd and `a` is coprime to `p` and `a` is not a quadratic residue modulo `p`, then `a` raised to the power of `(p - 1) / 2` is congruent to `FACT(p - 1)` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- The goal is to prove that if `p` is prime, odd, `a` is coprime to `p`, and `a` is not a quadratic residue modulo `p`, then `a ^ ((p - 1) / 2)` is congruent to `FACT(p - 1)` modulo `p`.
- Start by rewriting `FACT(p - 1)` using `FACT_NPRODUCT` (Wilson's theorem which relates the factorial of (p-1) with p).
- Apply induction using `NPRODUCT_PAIRUP_INDUCT`, pairing elements of the set `{1, ..., p-1}`
- Show that the set `{1, ..., p-1}` has size `(p - 1) / 2`.
- Consider the case `p = 0`. This quickly leads to a contradiction since `p` is prime.
- Use `CONG_SOLVE_UNIQUE_NONTRIVIAL` and `is_quadratic_residue` to prove the main result.

### Mathematical insight
This theorem connects the concept of quadratic non-residues with modular arithmetic and factorials. It essentially states a criterion for determining if a number is a quadratic non-residue modulo a prime `p`. It stems from Euler's criterion for quadratic residues.

### Dependencies
- `prime`
- `ODD`
- `coprime`
- `is_quadratic_residue`
- `FACT`
- `FACT_NPRODUCT`
- `NPRODUCT_PAIRUP_INDUCT`
- `ODD_EXISTS`
- `SUC_SUB1`
- `DIV_MULT`
- `HAS_SIZE`
- `FINITE_NUMSEG`
- `CARD_NUMSEG`
- `ADD_SUB`
- `PRIME_0`
- `IN_NUMSEG`
- `ARITH_RULE` (several instances)
- `CONG_SOLVE_UNIQUE_NONTRIVIAL`
- `COPRIME_SYM`
- `EQ_IMP`
- `FUN_EQ_THM`
- `EXP_2`


---

## QUADRATIC_RESIDUE_FACT

### Name of formal statement
QUADRATIC_RESIDUE_FACT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let QUADRATIC_RESIDUE_FACT = prove
 (`!a p. prime p /\ ODD(p) /\
         coprime(a,p) /\ a is_quadratic_residue (mod p)
         ==> (a EXP ((p - 1) DIV 2) == FACT(p - 2)) (mod p)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  SUBGOAL_THEN `3 <= p /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN UNDISCH_TAC `ODD(p)` THEN
    ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[ARITH] THEN
    UNDISCH_TAC `~(p = 2)` THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `a is_quadratic_residue (mod p)` THEN
  ASM_SIMP_TAC[EXP_2; IS_QUADRATIC_RESIDUE_PAIR; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:num = y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ODD_ADD]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\i:num. i`; `p:num`; `(p - 3) DIV 2`;
   `(1..p-1) DELETE x DELETE y`; `a:num`] NPRODUCT_PAIRUP_INDUCT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; FINITE_NUMSEG; IN_NUMSEG_1;
                 CARD_DELETE; IN_DELETE; CARD_NUMSEG_1] THEN
    SIMP_TAC[ARITH_RULE `p - 1 - 1 - 1 = p - 3`] THEN
    ASM_SIMP_TAC[GSYM EVEN_DIV; EVEN_SUB; ARITH; NOT_EVEN] THEN
    X_GEN_TAC `u:num` THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`a:num`; `p:num`; `u:num`] CONG_SOLVE_UNIQUE_NONTRIVIAL) THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THEN
    ASM_MESON_TAC[CONG_SOLVE_UNIQUE; PRIME_0; PRIME_COPRIME_LT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `x:num`] QUADRATIC_RESIDUE_PAIR_PRODUCT) THEN
  ASM_SIMP_TAC[EXP_2; IMP_IMP; ARITH_RULE `x + y = p ==> p - x = y`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_MULT) THEN
  ASM_SIMP_TAC[NPRODUCT_DELETE; GSYM MULT_ASSOC; IN_DELETE;
               FINITE_DELETE; IN_NUMSEG_1; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); GSYM FACT_NPRODUCT; ARITH_RULE
   `3 <= p ==> SUC((p - 3) DIV 2) = (p - 1) DIV 2`] THEN
  ASM_SIMP_TAC[FACT; ARITH_RULE `3 <= p ==> p - 1 = SUC(p - 2)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `3 <= p ==> SUC(p - 2) = p - 1`] THEN
  ASM_MESON_TAC[COPRIME_MINUS1; CONG_MULT_LCANCEL; CONG_SYM]);;
```

### Informal statement
For all natural numbers `a` and `p`, if `p` is a prime number, `p` is odd, `a` and `p` are coprime, and `a` is a quadratic residue modulo `p`, then `a` raised to the power of `(p - 1) / 2` is congruent to the factorial of `p - 2` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- First, establish the subgoal `3 <= p /\ ~(p = 0)` from the assumptions using `PRIME_GE_2`, `ODD`, and arithmetic reasoning.
- Assume that `a` is a quadratic residue modulo `p`. Then, rewrite using `EXP_2`, `IS_QUADRATIC_RESIDUE_PAIR`, and `LEFT_IMP_EXISTS_THM` to introduce existential variables `x` and `y` such that `a = x * x mod p` and also `a = y * y mod p`
- Show that `x` and `y` are distinct using `ASM_MESON_TAC[ODD_ADD]`.
- Apply `NPRODUCT_PAIRUP_INDUCT` to the set `(1..p-1) DELETE x DELETE y`.
- Simplify cardinality and finiteness properties using `HAS_SIZE`, `FINITE_DELETE`, `FINITE_NUMSEG`, `IN_NUMSEG_1`, `CARD_DELETE`, `IN_DELETE`, `CARD_NUMSEG_1`, and arithmetic reasoning. Show that the product of congruent elements remains congruent element. For this, use `CONG_SOLVE_UNIQUE_NONTRIVIAL`, `COPRIME_SYM`, primality and coprimality criteria (`PRIME_0`, `PRIME_COPRIME_LT`).
- Next, utilize `QUADRATIC_RESIDUE_PAIR_PRODUCT`, along with exponentiation properties and arithmetic equivalences to update the goal.
- Finally, use `COPRIME_MINUS1`, `CONG_MULT_LCANCEL`, and `CONG_SYM` to complete the proof, establishing the congruence `a EXP ((p - 1) DIV 2) == FACT(p - 2) (mod p)`.

### Mathematical insight
This theorem connects the concept of quadratic residues to factorials and modular arithmetic. It essentially states that if `a` is a quadratic residue modulo an odd prime `p`, then raising `a` to the power of `(p-1)/2` is congruent to `(p-2)!` modulo `p`. This provides a specific relationship between quadratic residues and factorials within modular arithmetic.

### Dependencies
- Arithmetic: `ARITH`
- Congruence: `CONG_SYM`, `CONG_MULT`, `CONG_MULT_LCANCEL`, `CONG_SOLVE_UNIQUE_NONTRIVIAL`, `CONG_SOLVE_UNIQUE`
- Coprimality: `coprime`, `COPRIME_SYM`, `COPRIME_MINUS1`
- Divisibility: `EVEN_DIV`, `EVEN_SUB`, `NOT_EVEN`
- Exponentiation: `EXP`, `EXP_2`
- Factorial: `FACT`
- Finite Sets: `HAS_SIZE`, `FINITE_DELETE`, `FINITE_NUMSEG`, `IN_NUMSEG_1`, `CARD_DELETE`, `IN_DELETE`, `CARD_NUMSEG_1`
- Functions: `DELETE`, `GSYM`
- Implications and Exists: `LEFT_IMP_EXISTS_THM`, `IMP_IMP`, `EQ_IMP`
- Modular Arithmetic: `x mod y`
- Natural Numbers: `num`, `ODD`, `ODD_ADD`, `PRIME_GE_2`
- Number Theory: `IS_QUADRATIC_RESIDUE_PAIR`, `QUADRATIC_RESIDUE_PAIR_PRODUCT`
- Products: `NPRODUCT_PAIRUP_INDUCT`, `NPRODUCT_DELETE`, `FACT_NPRODUCT`
- Primes: `prime`, `PRIME_0`, `PRIME_COPRIME_LT`


---

## WILSON_LEMMA

### Name of formal statement
WILSON_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WILSON_LEMMA = prove
 (`!p. prime(p) ==> (FACT(p - 2) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o MATCH_MP PRIME_ODD)
  THENL [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC CONG_CONV; ALL_TAC] THEN
  MP_TAC(SPECL [`1`; `p:num`] QUADRATIC_RESIDUE_FACT) THEN
  ASM_MESON_TAC[is_quadratic_residue; COPRIME_SYM; COPRIME_1; CONG_REFL;
                EXP_ONE; CONG_SYM]);;
```
### Informal statement
For all `p`, if `p` is prime, then `FACT(p - 2)` is congruent to `1` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- Assume `p` is prime.
- Perform case analysis based on whether `p` is odd. The theorem holds trivially for `p=2` by computation.
- Thus, assume that `p` is odd.
- Apply the theorem `QUADRATIC_RESIDUE_FACT` with `n = 1` (instantiating the theorem for `1` and `p`).
- Use an automated theorem prover (`ASM_MESON_TAC`) to complete the proof using relevant properties like `is_quadratic_residue`, `COPRIME_SYM`, `COPRIME_1`, `CONG_REFL`, `EXP_ONE`, and `CONG_SYM`.

### Mathematical insight
This theorem gives a modular arithmetic property of prime numbers. It provides a partial result toward Wilson's theorem, which states that `p` is prime if and only if `(p - 1)!` is congruent to `-1` modulo `p`. Here, we prove that if `p` is prime, then `(p-2)!` is congruent to `1` modulo `p`.

### Dependencies
- `prime`
- `FACT`
- `CONG_SYM`
- `PRIME_ODD`
- `QUADRATIC_RESIDUE_FACT`
- `is_quadratic_residue`
- `COPRIME_SYM`
- `COPRIME_1`
- `CONG_REFL`
- `EXP_ONE`


---

## WILSON_IMP

### Name of formal statement
WILSON_IMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WILSON_IMP = prove
 (`!p. prime(p) ==> (FACT(p - 1) == p - 1) (mod p)`,
  SIMP_TAC[FACT; PRIME_GE_2; ARITH_RULE `2 <= p ==> p - 1 = SUC(p - 2)`] THEN
  MESON_TAC[CONG_MULT; MULT_CLAUSES; WILSON_LEMMA; CONG_REFL]);;
```
### Informal statement
For all `p`, if `p` is prime, then `FACT(p - 1)` is congruent to `p - 1` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- Simplification is first performed using `FACT`, `PRIME_GE_2`, and an arithmetic rule to rewrite `p - 1` as `SUC(p - 2)` given that `2 <= p`.
- The main part of proof is performed by applying `MESON_TAC` tactic with `CONG_MULT`, `MULT_CLAUSES`, `WILSON_LEMMA`, and `CONG_REFL`.
- `WILSON_LEMMA` is a critical component, and states that for prime `p`, `FACT(p - 1)` is congruent to `-1` modulo `p`. The system then rewrites `-1` as `p - 1` modulo `p`. The transitivity of congruence is then implicitly handled by the `MESON_TAC` to complete the proof.

### Mathematical insight
This theorem is an implication of Wilson's Lemma. It's a standard result in number theory that connects the factorial function with prime numbers via modular arithmetic. It provides a necessary (but not sufficient) condition for primality.

### Dependencies
- Definitions: `FACT`, `prime`
- Theorems: `PRIME_GE_2`, `WILSON_LEMMA`, `CONG_MULT`, `MULT_CLAUSES`, `CONG_REFL`

### Porting notes (optional)
- Ensure that the target system has a definition of the factorial function (`FACT`) and a predicate for primality (`prime`).
- Recreating the `MESON_TAC` step may require some ingenuity depending on the automation available in the target system. Pay close attention to how congruence relations are handled.
- The explicit arithmetic rewriting `2 <= p ==> p - 1 = SUC(p - 2)` might be automatically handled by some systems, or may require an explicit tactic.


---

## WILSON

### Name of formal statement
WILSON

### Type of the formal statement
theorem

### Formal Content
```ocaml
let WILSON = prove
 (`!p. ~(p = 1) ==> (prime p <=> (FACT(p - 1) == p - 1) (mod p))`,
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN EQ_TAC THEN SIMP_TAC[WILSON_IMP] THEN
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
For all natural numbers `p`, if `p` is not equal to 1, then `p` is prime if and only if the factorial of `p - 1` is congruent to `p - 1` modulo `p`.

### Informal sketch
The proof demonstrates Wilson's Theorem: a number `p` (not equal to 1) is prime if and only if `FACT(p - 1) == p - 1 (mod p)`.
- Assume `n` is a numeral and `~(n = 1)`. From this assumption, we aim to prove `prime n <=> (FACT(n - 1) == n - 1) (mod n)`.
- We use a simplification tactic with `WILSON_IMP`, which likely introduces the implication in both directions for Wilson's Theorem.
- One direction is handled by using `PRIME_FACTOR` to introduce a prime factor `p` of `n`.
- We proceed by assuming such a `p` exists, choosing that `p` using `X_CHOOSE_TAC`.
- We want to show `n = p` by contradiction.
- Next, a case split is performed to check if `n = 0`.
- If `n` is equal to `p`, we use arithmetic reasoning.
- If not, we use the fact that a prime can divide `FACT(n-1)` if and only if the prime divides one of the terms in the factorial.
- We establish `p divides FACT(n - 1) <=> p divides (n - 1)`.
- Next, we demonstrate that if `p` divides `1`, which allows concluding `prime p` must be false, through leveraging the fact that if a prime number `p` divides `a + b`, then `p` divides `a` if and only if `p` divides `b`.
- Finally, we check that the only number divisible by one is `1` and since we assume that `p` is prime, `p` cannot be equal to 1.

### Mathematical insight
Wilson's theorem provides a necessary and sufficient condition for primality. It connects number theory concepts - primality, factorial, and modular arithmetic. Though not practical for primality testing due to the factorial's rapid growth, it's a cornerstone result in elementary number theory.

### Dependencies
- Theorems: `WILSON_IMP`, `PRIME_FACTOR`, `DIVIDES_LE`, `CONG_MOD_0`, `LE_LT`, `ARITH_RULE x < y ==> x <= y - 1`, `DIVIDES_FACT_PRIME`, `CONG_DIVIDES`, `CONG_DIVIDES_MODULUS`, `DIVIDES_ADD_REVR`, `DIVIDES_ONE`, `PRIME_1`


---

## EULER_CRITERION

### Name of formal statement
EULER_CRITERION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULER_CRITERION = prove
 (`!a p. prime p /\ coprime(a,p)
         ==> (a EXP ((p - 1) DIV 2) ==
              (if a is_quadratic_residue (mod p) then 1 else p - 1)) (mod p)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o
    MATCH_MP PRIME_ODD) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COND_ID; EXP; CONG_REFL] THEN
  ASM_MESON_TAC[WILSON_LEMMA; WILSON_IMP; CONG_TRANS; CONG_SYM;
                QUADRATIC_RESIDUE_FACT; QUADRATIC_NONRESIDUE_FACT]);;
```
### Informal statement
For all `a` and `p`, if `p` is prime and `a` and `p` are coprime, then `a` raised to the power of `(p - 1) / 2` is congruent modulo `p` to 1 if `a` is a quadratic residue modulo `p`, and to `p - 1` if `a` is not a quadratic residue modulo `p`.

### Informal sketch
The proof proceeds by cases based on whether `a` is a quadratic residue modulo `p`.

- Case 1: Assume that `a` is a quadratic residue modulo `p`. Then, using the definition of quadratic residue, `a` is congruent to `x^2` modulo `p` for some `x`. Therefore, `a^((p-1)/2)` is congruent to `x^(p-1)` modulo `p`. Fermat's Little Theorem (since `p` is odd and coprime to `x`) shows that `x^(p-1)` is congruent to 1 modulo `p`, thus we get `a^((p-1)/2)` is congruent to 1 modulo `p`.

- Case 2: Assume that `a` is not a quadratic residue modulo `p`. This case uses `WILSON_LEMMA` which states that `(p-1)!` is congruent to `p-1` modulo `p`. The assumptions `prime p` and `coprime(a,p)` are used along with `QUADRATIC_NONRESIDUE_FACT`, `QUADRATIC_RESIDUE_FACT`, `EXP`, `COND_ID` to rewrite the expression. Then use `WILSON_IMP`, `CONG_TRANS`, and `CONG_SYM`.

### Mathematical insight
Euler's criterion provides a way to determine whether an integer `a` is a quadratic residue modulo a prime `p` by computing `a^((p-1)/2) mod p`. The result will be 1 if `a` is a quadratic residue, and `p - 1` (or `-1`) if it is not. This theorem is a cornerstone in number theory and modular arithmetic, and it links quadratic residues to exponentiation.

### Dependencies
- `prime`
- `coprime`
- `EXP`
- `is_quadratic_residue`
- `WILSON_LEMMA`
- `WILSON_IMP`
- `QUADRATIC_RESIDUE_FACT`
- `QUADRATIC_NONRESIDUE_FACT`
- `COND_ID`
- `CONG_TRANS`
- `CONG_SYM`

### Porting notes (optional)
Ensure that the target proof assistant has support for modular arithmetic, prime numbers, quadratic residues, and Wilson's Lemma. The tactic `ASM_MESON_TAC` relies on the MESON prover that may need to be replicated by another automated prover or by hand-guided proofs.


---

## GAUSS_LEMMA_1

### Name of formal statement
GAUSS_LEMMA_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_1 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> nproduct(1..r) (\x. let b = (a * x) MOD p in
                           if b <= r then b else p - b) =
       nproduct(1..r) (\x. x)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM(CONJUNCT1(SPEC_ALL I_O_ID))] THEN
  REWRITE_TAC[I_DEF] THEN MATCH_MP_TAC NPRODUCT_INJECTION THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  ABBREV_TAC `f = \x. let b = (a * x) MOD p in
                      if b <= r then b else p - b` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[IN_NUMSEG] THEN
    LET_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN REPEAT STRIP_TAC THENL
     [ALL_TAC; EXPAND_TAC "p" THEN ARITH_TAC] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN COND_CASES_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[DIVISION; NOT_LE; SUB_EQ_0; PRIME_0]] THEN
    EXPAND_TAC "b" THEN ASM_SIMP_TAC[GSYM DIVIDES_MOD; PRIME_IMP_NZ] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[coprime; DIVIDES_REFL; PRIME_1];
      ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(1 <= 0)`;
                    ARITH_RULE `~(2 * r + 1 <= i /\ i <= r)`]];
    REWRITE_TAC[LET_DEF; LET_END_DEF] THEN DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REWRITE_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `p:num` THEN
  REPEAT(CONJ_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `i <= r ==> i < 2 * r + 1`] ; ALL_TAC]) THEN
  MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `a:num` THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `(if a then x else p - x) = (if b then y else p - y) ==> x < p /\ y < p
    ==> x = y \/ x + y = p`)) THEN ASM_SIMP_TAC[DIVISION] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [ASM_MESON_TAC[CONG]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C AP_THM `p:num` o AP_TERM `(MOD)`) THEN
  ASM_SIMP_TAC[MOD_ADD_MOD] THEN ASM_SIMP_TAC[GSYM CONG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CONG_DIVIDES) THEN
  ASM_SIMP_TAC[GSYM LEFT_ADD_DISTRIB; PRIME_DIVPROD_EQ; DIVIDES_REFL] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[coprime; DIVIDES_REFL; PRIME_1]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i + j = 0)`] THEN
  MAP_EVERY UNDISCH_TAC [`i <= r`; `j <= r`; `2 * r + 1 = p`] THEN ARITH_TAC);;
```
### Informal statement
If `p` is a prime number, `a` is coprime to `p`, and `2 * r + 1 = p`, then the product of the numbers obtained by, for each `x` in the range `1` to `r`, computing `(a * x) MOD p`, and if the result `b` is less than or equal to `r` taking `b` otherwise taking `p - b`, equals the product of the numbers in the range `1` to `r`.

### Informal sketch
The proof proceeds as follows:
- Assume that `p` is prime, `a` is coprime to `p`, and `2 * r + 1 = p`.
- Simplify the `nproduct` expression using the definition of `I_DEF` and injectivity of `nproduct`.
- Introduce a function `f` such that `f x = (a * x) MOD p in if b <= r then b else p - b`.
- Prove that `f` is a mapping from `1..r` to `1..r` by showing that for `1 <= x <= r` we have `1 <= f x <= r`. Case split on if `b <= r` or not.
- Show that for any `i` and `j` in the range `1` to `r`, if `f i = f j`, then `i = j`.
  - Assume `f i = f j` for some `i` and `j` in the range `1` to `r`.
  - This implies that either `(a * i) MOD p = (a * j) MOD p` or `(a * i) MOD p + (a * j) MOD p = p`.
  - If `(a * i) MOD p = (a * j) MOD p` then `i = j` by congruence and the fact that `a` is coprime to `p`.
  - If `(a * i) MOD p + (a * j) MOD p = p`, then `a * (i + j)` is divisible by `p`. Since `a` is coprime to `p`, it must be that `i + j` is divisible by `p`. Since `1 <= i <= r` and `1 <= j <= r`, we have `2 <= i + j <= 2r < 2r + 1 = p`, which means `i + j` cannot be divisible by `p` unless `i + j = 0`. But `i` and `j` are positive, so this is impossible.

### Mathematical insight
This theorem is the core of Gauss's Lemma, which is used to determine the Legendre symbol (quadratic residue symbol) of a number modulo an odd prime. The Legendre symbol is 1 if the number is a quadratic residue modulo the prime, and -1 if it is a quadratic non-residue. Gauss's Lemma states that the Legendre symbol `(a/p)` is equal to `(-1)^n`, where `n` is the number of integers in the set `{a mod p, 2a mod p, ..., ((p-1)/2)a mod p}` that are greater than `p/2`. The theorem formalizes that the product is the same if we take `p-b` when `b` is greater than `r`.

### Dependencies
- `prime`
- `coprime`
- `nproduct`
- `PRIME_IMP_NZ`
- `I_DEF`
- `NPRODUCT_INJECTION`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `DIVISION`
- `NOT_LE`
- `SUB_EQ_0`
- `PRIME_0`
- `DIVIDES_MOD`
- `PRIME_IMP_NZ`
- `PRIME_DIVPROD_EQ`
- `DIVIDES_REFL`
- `PRIME_1`
- `DIVIDES_LE`
- `ARITH_RULE `~(1 <= 0)``
- `ARITH_RULE `~(2 * r + 1 <= i /\ i <= r)``
- `CONG_IMP_EQ`
- `CONG_MULT_LCANCEL`
- `CONG`
- `MOD_ADD_MOD`
- `CONG_DIVIDES`
- `LEFT_ADD_DISTRIB`

### Porting notes (optional)
The proof involves heavy rewriting and arithmetic reasoning, so automation support for these aspects would be helpful in other proof assistants.
The main challenge will likely be reconstructing the arithmetic reasoning steps, especially those involving `MOD` and divisibility. Careful attention should be paid to the assumptions used in each step, particularly those related to the primality of `p` and the coprimality of `a` and `p`.


---

## GAUSS_LEMMA_2

### Name of formal statement
GAUSS_LEMMA_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_2 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> (nproduct(1..r) (\x. let b = (a * x) MOD p in
                            if b <= r then b else p - b) ==
        (p - 1) EXP (CARD {x | x IN 1..r /\ r < (a * x) MOD p}) *
        a EXP r * nproduct(1..r) (\x. x)) (mod p)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {x | x IN 1..r /\ (a * x) MOD p <= r}` THEN
  MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC
   `nproduct(1..r) (\x. (if x IN s then 1 else p - 1) * (a * x) MOD p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONG_NPRODUCT THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN LET_TAC THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; CONG_REFL] THEN
    REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN MATCH_MP_TAC CONG_SUB THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL; MULT_CLAUSES; CONG_REFL] THEN
    REWRITE_TAC[ARITH_RULE `b <= p /\ (1 <= p \/ b = 0) <=> b <= p`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    DISCH_THEN(MP_TAC o SPEC `a * i:num` o MATCH_MP DIVISION o
     MATCH_MP (ARITH_RULE `2 <= p ==> ~(p = 0)`)) THEN
    ASM_SIMP_TAC[LT_IMP_LE; cong; nat_mod] THEN DISCH_THEN(K ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`b:num`; `1`] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC CONG_MULT THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
    SIMP_TAC[NPRODUCT_DELTA_CONST; FINITE_NUMSEG] THEN
    MATCH_MP_TAC EQ_IMP_CONG THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "s" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[NOT_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `nproduct(1..r) (\x. a * x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CONG_MOD; PRIME_IMP_NZ; CONG_NPRODUCT; FINITE_NUMSEG];
    SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG; NPRODUCT_CONST; CARD_NUMSEG_1] THEN
    REWRITE_TAC[CONG_REFL]]);;
```

### Informal statement
If `p` is a prime number, `a` is coprime to `p`, and `2 * r + 1` equals `p`, then the product of terms obtained by mapping the integers from 1 to `r` (inclusive) to `(a * x) MOD p` if `(a * x) MOD p` is less than or equal to `r`, and to `p - (a * x) MOD p` otherwise, is congruent modulo `p` to `(p - 1)` raised to the power of the cardinality of the set of `x` such that `x` is in the range `1..r` and `r < (a * x) MOD p`, times `a` raised to the power of `r`, times the product of the integers from 1 to `r`.

### Informal sketch
The proof aims to establish the congruence relation described in the informal statement.
- First, define the set `s = {x | x IN 1..r /\ (a * x) MOD p <= r}`.
- Transform the original `nproduct` by multiplying each term by `1` if `x` is in `s`, and by `p - 1` otherwise, and then taking the result modulo `p`.
- Decompose the product of `(if x IN s then 1 else p - 1) * (a * x) MOD p` into a product based on whether `x` belongs to `s` or not. This split involves using `NPRODUCT_MUL` and `NPRODUCT_DELTA_CONST`. We aim to show that the product of `(if x IN s then 1 else p - 1)` is congruent to `(p - 1)` raised to the power of the size of `s`'s complement within `1..r`.
- Show that the product of `(a * x) MOD p` over the range from 1 to `r` is congruent to the product of `a * x` over the same range.
- The final step simplifies the product of `a * x` using the properties of `coprime` and modular arithmetic.

### Mathematical insight
This theorem is a step towards Gauss's Lemma, a result in number theory used to prove quadratic reciprocity. It relates the product of a specific sequence of numbers (derived from multiples of `a` modulo `p`) to a power of `a` and the factorial of `r`, where `r = (p-1)/2`. The set `s` essentially counts the number of negative remainders when multiples of `a` are reduced modulo `p`.

### Dependencies
- `prime`
- `coprime`
- `nproduct`
- `MOD`
- `EXP`
- `CARD`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `IN_ELIM_THM`
- `MULT_CLAUSES`
- `RIGHT_SUB_DISTRIB`
- `LE_MULT_RCANCEL`
- `ARITH_RULE`
- `PRIME_GE_2`
- `DIVISION`
- `LT_IMP_LE`
- `cong`
- `nat_mod`
- `NPRODUCT_MUL`
- `COND_SWAP`
- `NPRODUCT_DELTA_CONST`
- `EQ_IMP_CONG`
- `EXTENSION`
- `NOT_LT`
- `CONG_MOD`
- `PRIME_IMP_NZ`
- `CONG_NPRODUCT`
- `NPRODUCT_CONST`
- `CARD_NUMSEG_1`


---

## GAUSS_LEMMA_3

### Name of formal statement
GAUSS_LEMMA_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_3 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC
   `(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} * a EXP r` THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
    SUBGOAL_THEN `r = (p - 1) DIV 2`
     (fun th -> ASM_SIMP_TAC[th; EULER_CRITERION]) THEN
    EXPAND_TAC "p" THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CONG_MULT_RCANCEL THEN
  EXISTS_TAC `nproduct (1..r) (\x. x)` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; GSYM MULT_ASSOC;
               SIMP_RULE[GAUSS_LEMMA_1] GAUSS_LEMMA_2] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_NPRODUCT THEN
  REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC PRIME_COPRIME_LT THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
```

### Informal statement
If `p` is a prime number, `a` and `p` are coprime, and `2 * r + 1 = p`, then `((p - 1) ^ (cardinality {x | x is in the set 1..r and r < (a * x) mod p}) * (if a is a quadratic residue modulo p then 1 else p - 1)) mod p = 1`.

### Informal sketch
The proof proceeds as follows:
- Start with the goal: `(p - 1) ^ (cardinality {x | x IN 1..r /\ r < (a * x) MOD p}) * (if a is_quadratic_residue mod p then 1 else p - 1) == 1 (mod p)`.
- Introduce `(p - 1) ^ (cardinality {x | x IN 1..r /\ r < (a * x) MOD p}) * a ^ r` using `EXISTS_TAC`.
- Rewrite using congruence properties.
- Split the goal into two subgoals using `CONJ_TAC`.
- The first subgoal requires showing that `(if a is_quadratic_residue mod p then 1 else p - 1) == a ^ r (mod p)`. This is proven by using `EULER_CRITERION` and the fact that `r = (p - 1) DIV 2`.
- The second subgoal involves showing that `a ^ r == 1 (mod p)`.
- Cancel a common factor using `CONG_MULT_RCANCEL`.
- Introduce `nproduct (1..r) (\x. x)` using `EXISTS_TAC`.
- Simplify the expression using lemmas `GAUSS_LEMMA_1` and `GAUSS_LEMMA_2`, along with properties of coprimality and multiplication. `MULT_CLAUSES`, `GSYM MULT_ASSOC`, and `SIMP_RULE` are used.
- Apply coprimality properties by rewriting with `COPRIME_SYM`, `COPRIME_NPRODUCT`, `IN_NUMSEG`, and `FINITE_NUMSEG`.
- Use `PRIME_COPRIME_LT` and arithmetic reasoning to complete the proof.

### Mathematical insight
This theorem, related to Gauss's Lemma, provides a condition for determining whether an integer `a` is a quadratic residue modulo a prime `p`. It relates the Legendre symbol (implicitly via `is_quadratic_residue`) to the cardinality of a set derived from modular arithmetic. The heart of the proof relies on Euler's Criterion, which directly connects quadratic residues with modular exponentiation.

### Dependencies
- `prime`
- `coprime`
- `is_quadratic_residue`
- `GAUSS_LEMMA_1`
- `GAUSS_LEMMA_2`
- `EULER_CRITERION`
- `MULT_CLAUSES`
- `MULT_ASSOC`
- `COPRIME_SYM`
- `COPRIME_NPRODUCT`
- `IN_NUMSEG`
- `FINITE_NUMSEG`
- `PRIME_COPRIME_LT`

### Porting notes (optional)
- The `is_quadratic_residue` predicate may need to be defined separately based on the capabilities of other proof assistants.
- The handling of modular arithmetic and Legendre symbols (if applicable) varies between systems, and an appropriate library or definition should be used.
- The tactics used (e.g., `ASM_SIMP_TAC`, `REWRITE_TAC`) suggest that the theorem benefits from strong automation in rewriting and simplification. Look for similar features in the target proof assistant.


---

## GAUSS_LEMMA_4

### Name of formal statement
GAUSS_LEMMA_4

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_4 = prove
 (`prime p /\ coprime(a,p) /\ 2 * r + 1 = p
   ==> ((if EVEN(CARD{x | x IN 1..r /\ r < (a * x) MOD p}) then 1 else p - 1) *
        (if a is_quadratic_residue mod p then 1 else p - 1) == 1) (mod p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC `(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} *
              (if a is_quadratic_residue mod p then 1 else p - 1)` THEN
  ASM_SIMP_TAC[GAUSS_LEMMA_3] THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
  ASM_SIMP_TAC[CONG_EXP_MINUS1; CONG_MULT; CONG_REFL; PRIME_GE_2]);;
```

### Informal statement
If `p` is a prime number, `a` is coprime to `p`, and `2 * r + 1 = p`, then the following congruence holds modulo `p`: the product of (if the cardinality of the set of `x` such that `x` is in the range `1` to `r` inclusive and `r` is less than `(a * x) MOD p`, then `1`, else `p - 1`) and (if `a` is a quadratic residue modulo `p` then `1` else `p - 1`) is congruent to `1` modulo `p`.

### Informal sketch
The proof proceeds as follows:
- First, strip the assumptions.
- Then, use `MATCH_MP_TAC CONG_TRANS`. This suggests transitivity of congruence is used along with another theorem to rewrite the goal. An intermediate term `(p - 1) EXP CARD {x | x IN 1..r /\ r < (a * x) MOD p} * (if a is_quadratic_residue mod p then 1 else p - 1)` is introduced using the `EXISTS_TAC` tactic, suggesting the use of congruence properties related to exponentiation.
- Apply `GAUSS_LEMMA_3` using `ASM_SIMP_TAC`. This lemma likely relates to the Gauss Lemma concerning the Legendre symbol.
- Rewrite using the symmetry of congruence with `ONCE_REWRITE_TAC[CONG_SYM]`.
- Simplify using `ASM_SIMP_TAC` and the theorems `CONG_EXP_MINUS1`, `CONG_MULT`, `CONG_REFL`, and `PRIME_GE_2`. These theorems probably concern (-1)^n mod p and the fact that p >= 2 when p is prime.

### Mathematical insight
This theorem represents Gauss's Lemma, which relates the Legendre symbol (quadratic residuosity) to the number of residues greater than p/2. It provides a practical way to compute the Legendre symbol by counting the number of residues in a specific range, thus linking quadratic residuosity to simpler counting arguments.

### Dependencies
- `prime`
- `coprime`
- `CARD`
- `MOD`
- `EVEN`
- `is_quadratic_residue`
- `GAUSS_LEMMA_3`
- `CONG_SYM`
- `CONG_EXP_MINUS1`
- `CONG_MULT`
- `CONG_REFL`
- `PRIME_GE_2`


---

## GAUSS_LEMMA

### Name of formal statement
GAUSS_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GAUSS_LEMMA = prove
 (`!a p r. prime p /\ coprime(a,p) /\ 2 * r + 1 = p
           ==> (a is_quadratic_residue (mod p) <=>
                EVEN(CARD {x | x IN 1..r /\ r < (a * x) MOD p}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC CONG_COND_LEMMA THEN EXISTS_TAC `p:num` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "p" THEN ASM_CASES_TAC `r = 0` THENL
     [REWRITE_TAC[ASSUME `r = 0`; ARITH; PRIME_1];
      UNDISCH_TAC `~(r = 0)` THEN ARITH_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP GAUSS_LEMMA_4) THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[CONG_REFL]) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN MESON_TAC[CONG_SYM]]);;
```
### Informal statement
For all natural numbers `a`, `p`, and `r`, if `p` is a prime number, `a` and `p` are coprime, and `2 * r + 1 = p`, then `a` is a quadratic residue modulo `p` if and only if the cardinality of the set of natural numbers `x` such that `x` is in the range `1` to `r` inclusive and `r` is less than `(a * x) MOD p` is even.

### Informal sketch
The proof proceeds as follows:
- Assume `p` is prime, `a` and `p` are coprime, and `2 * r + 1 = p`.
- Apply `CONG_COND_LEMMA`, then introduce the specific prime `p` through an existential instantiation. Apply also the conjuncts of the assumption.
- Handle the edge case where `r = 0`.  Since `2 * r + 1 = p`, if `r = 0`, then `p = 1`, which contradicts the assumption that `p` is prime. In the case where `r` is not zero, apply arithmetic.
- Apply `GAUSS_LEMMA_4` and split into cases repeatedly, using congruence reflexive tactic, then rewrite using `MULT_CLAUSES` and use MESON. The overall idea involves using congruences and case splitting to establish the equivalence between the quadratic residuosity of `a` modulo `p` and the parity of the specified set's cardinality, leveraging number-theoretic properties and the relationship between `a`, `p`, and `r`.

### Mathematical insight
This theorem states Gauss's Lemma.  Gauss's Lemma is a fundamental result in number theory that provides a criterion for determining whether an integer `a` is a quadratic residue modulo an odd prime `p`. The lemma relates this to the parity of the number of elements in the set `{1, 2, ..., r}` whose product with `a` modulo `p` exceeds `r`, where `r = (p-1)/2`. It is an important stepping stone to proving the law of quadratic reciprocity.

### Dependencies
- `prime`
- `coprime`
- `is_quadratic_residue`
- `MOD`
- `EVEN`
- `CARD`
- `GAUSS_LEMMA_4`
- `CONG_COND_LEMMA`
- `CONG_REFL`
- `CONG_SYM`
- `MULT_CLAUSES`


---

## GAUSS_LEMMA_SYM

### Name of formal statement
GAUSS_LEMMA_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_SYM = prove
 (`!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (q is_quadratic_residue (mod p) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   q * x < p * y /\ p * y <= q * x + r}))`,
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `p:num`; `r:num`] GAUSS_LEMMA) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `CARD {x,y | x IN 1..r /\ y IN 1..s /\
                y = (q * x) DIV p + 1 /\ r < (q * x) MOD p}` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBCROSS_DETERMINATE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; ARITH_RULE `1 <= x + 1`] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p * (q * x) DIV p + r < q * r` MP_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `q * x` THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
      ASM_MESON_TAC[PRIME_IMP_NZ; LT_ADD_LCANCEL; DIVISION];
      MAP_EVERY EXPAND_TAC ["p"; "q"] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (ARITH_RULE `(2 * r + 1) * d + r < (2 * s + 1) * r
                    ==> (2 * r) * d < (2 * r) * s`)) THEN
      SIMP_TAC[LT_MULT_LCANCEL; ARITH_RULE `x < y ==> x + 1 <= y`]];
    AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [MP_TAC(MATCH_MP PRIME_IMP_NZ (ASSUME `prime p`)) THEN
      DISCH_THEN(MP_TAC o SPEC `q * x` o MATCH_MP DIVISION) THEN
      FIRST_ASSUM(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
      UNDISCH_TAC `2 * r + 1 = p` THEN ARITH_TAC;
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [ALL_TAC;
        DISCH_THEN SUBST_ALL_TAC THEN
        MATCH_MP_TAC(ARITH_RULE
         `!p d. 2 * r + 1 = p /\ p * (d + 1) <= (d * p + m) + r ==> r < m`) THEN
        MAP_EVERY EXISTS_TAC [`p:num`; `(q * x) DIV p`] THEN
        ASM_MESON_TAC[DIVISION; PRIME_IMP_NZ]] THEN
      MATCH_MP_TAC(ARITH_RULE `~(x <= y) /\ ~(y + 2 <= x) ==> x = y + 1`) THEN
      REPEAT STRIP_TAC THENL
       [SUBGOAL_THEN `y * p <= ((q * x) DIV p) * p` MP_TAC THENL
         [ASM_SIMP_TAC[LE_MULT_RCANCEL; PRIME_IMP_NZ]; ALL_TAC];
        SUBGOAL_THEN `((q * x) DIV p + 2) * p <= y * p` MP_TAC THENL
         [ASM_SIMP_TAC[LE_MULT_RCANCEL; PRIME_IMP_NZ]; ALL_TAC]] THEN
      MP_TAC(MATCH_MP PRIME_IMP_NZ (ASSUME `prime p`)) THEN
      DISCH_THEN(MP_TAC o SPEC `q * x` o MATCH_MP DIVISION) THEN
      ASM_ARITH_TAC]]);;
```

### Informal statement
For all numbers `p`, `q`, `r`, and `s`, if `p` and `q` are prime numbers, `p` and `q` are coprime, `2 * r + 1 = p`, and `2 * s + 1 = q`, then `q` is a quadratic residue modulo `p` if and only if the cardinality of the set of pairs `(x, y)` such that `x` is in the range `1` to `r`, `y` is in the range `1` to `s`, `q * x < p * y`, and `p * y <= q * x + r` is even.

### Informal sketch
The proof proceeds as follows:
- Rewrite using `COPRIME_SYM`.
- Strip the quantifiers and implications.
- Apply `GAUSS_LEMMA` with specific values for `q`, `p`, and `r`.
- Simplify using assumptions.
- Discharge the assumptions and introduce universal quantifiers.
- Apply an equational term tactic.
- Use transitivity of equality.
- Exhibit a specific set to match the cardinality expression, namely the set of pairs `(x, y)` such that `y = (q * x) DIV p + 1` and `r < (q * x) MOD p`, where `x` and `y` are in the ranges `1..r` and `1..s` respectively.
- Split into two subgoals relating to set equality.
- In one subgoal, use the determinate cardinality of a subcross. Use several arithmetic steps and simplification to prove that `p * (q * x) DIV p + r < q * r`.
- In the other subgoal, prove set extensionality of pairs by showing the equivalence of their characteristic predicates.
- Split the second subgoal and make several arithmetic reductions. Use the division properties to reduce to the goal.

### Mathematical insight
This is a symmetrical version of Gauss's lemma on quadratic residues. Gauss's lemma provides a criterion for determining whether an integer `q` is a quadratic residue modulo a prime `p` based on the parity of the number of integers in the set `{1, 2, ..., (p-1)/2}` whose least positive residues modulo `p` lie in the interval `(p/2, p)`. This symmetric form involves counting pairs of integers within specified ranges related by inequalities involving `p` and `q`.

### Dependencies
#### Theorems
- `GAUSS_LEMMA`
- `CARD_SUBCROSS_DETERMINATE`
- `EXTENSION`
- `IN_ELIM_PAIR_THM`
- `FORALL_PAIR_THM`
#### Definitions
- `prime`
- `coprime`
- `is_quadratic_residue`
- `EVEN`
- `CARD`
- `DIV`
- `MOD`
#### Rules
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- Arithmetic tautologies like `1 <= x + 1` and `x < y ==> x + 1 <= y`
- `COPRIME_SYM`
- `PRIME_IMP_NZ`
- `LT_ADD_LCANCEL`
- `DIVISION`
- `LE_MULT_LCANCEL`

### Porting notes (optional)
- The definition of `is_quadratic_residue` might differ across proof assistants, so ensure it is compatible.
- The handling of integer division (`DIV`) and modulo (`MOD`) operations may require careful attention to ensure consistency.
- The proof relies heavily on arithmetic reasoning, so a proof assistant with strong arithmetic automation will be beneficial.
- The use of HOL Light's `MESON` prover suggests that some level of automated reasoning is expected.


---

## GAUSS_LEMMA_SYM'

### Name of formal statement
GAUSS_LEMMA_SYM'

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GAUSS_LEMMA_SYM' = prove
 (`!p q r s. prime p /\ prime q /\ coprime(p,q) /\
             2 * r + 1 = p /\ 2 * s + 1 = q
             ==> (p is_quadratic_residue (mod q) <=>
                  EVEN(CARD {x,y | x IN 1..r /\ y IN 1..s /\
                                   p * y < q * x /\ q * x <= p * y + s}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`q:num`; `p:num`; `s:num`; `r:num`] GAUSS_LEMMA_SYM) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [CARD_SUBCROSS_SWAP] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; CONJ_ACI]);;
```
### Informal statement
For all natural numbers `p`, `q`, `r`, and `s`, if `p` and `q` are prime numbers, `p` and `q` are coprime, `2 * r + 1 = p`, and `2 * s + 1 = q`, then `p` is a quadratic residue modulo `q` if and only if the cardinality of the set of pairs `(x, y)` such that `x` is in the range `1` to `r`, `y` is in the range `1` to `s`, `p * y < q * x`, and `q * x <= p * y + s` is even.

### Informal sketch
The proof proceeds as follows:
- Apply the theorem `GAUSS_LEMMA_SYM` with specific instantiations for `q`, `p`, `s`, and `r`.
- Rewrite using `COPRIME_SYM` to reflect the symmetry of the coprime relation.
- Perform automatic rewriting using assumptions.
- Substitute using a discharged hypothesis.
- Apply a term congruence tactic.
- Rewrite using `CARD_SUBCROSS_SWAP` within a general rewriting tactic controlled by a left-to-right (LAND) strategy.
- Apply a term congruence tactic again.
- Rewrite using the definitions of set extension (`EXTENSION`), and the theorem `FORALL_PAIR_THM`.
- Rewrite using theorems that eliminate the `IN` relation for pairs (`IN_ELIM_PAIR_THM`) and associativity, commutativity, and idempotence for conjunction (`CONJ_ACI`).

### Mathematical insight
This theorem provides a criterion for determining whether a prime number `p` is a quadratic residue modulo another prime number `q`, based on the parity of the number of integer pairs satisfying certain inequalities involving `p`, `q`, and related variables. It leverages Gauss's Lemma and properties of coprime numbers and quadratic residues to connect number-theoretic concepts with combinatorial ones through the cardinality of a specific set.

### Dependencies
- Theorems: `GAUSS_LEMMA_SYM`, `FORALL_PAIR_THM`
- Definitions: `prime`, `coprime`, `is_quadratic_residue`, `EVEN`, `CARD`, `IN`, `mod`
- Rewriting rules: `COPRIME_SYM`, `CARD_SUBCROSS_SWAP`, `EXTENSION`, `IN_ELIM_PAIR_THM`, `CONJ_ACI`


---

## RECIPROCITY_SET_LEMMA

### Name of formal statement
RECIPROCITY_SET_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RECIPROCITY_SET_LEMMA = prove
 (`!a b c d r s.
        a UNION b UNION c UNION d = (1..r) CROSS (1..s) /\
        PAIRWISE DISJOINT [a;b;c;d] /\ CARD b = CARD c
        ==> ((EVEN(CARD a) <=> EVEN(CARD d)) <=> ~(ODD r /\ ODD s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(a:num#num->bool) + CARD(b:num#num->bool) +
                CARD(c:num#num->bool) + CARD(d:num#num->bool) = r * s`
   (fun th -> MP_TAC(AP_TERM `EVEN` th) THEN
              ASM_REWRITE_TAC[EVEN_ADD; GSYM NOT_EVEN; EVEN_MULT] THEN
              CONV_TAC TAUT) THEN
  SUBGOAL_THEN
   `FINITE(a:num#num->bool) /\ FINITE(b:num#num->bool) /\
    FINITE(c:num#num->bool) /\ FINITE(d:num#num->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(1..r) CROSS (1..s)` THEN
    SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `CARD:(num#num->bool)->num`) THEN
  SIMP_TAC[CARD_CROSS; CARD_NUMSEG_1; FINITE_NUMSEG] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PAIRWISE]) THEN
  REWRITE_TAC[PAIRWISE; DISJOINT; ALL] THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_UNION; SET_RULE
    `a INTER (b UNION c) = {} <=> a INTER b = {} /\ a INTER c = {}`]);;
```
### Informal statement
For all sets `a`, `b`, `c`, and `d` of pairs of natural numbers, and all natural numbers `r` and `s`, if the union of `a`, `b`, `c`, and `d` equals the Cartesian product of the ranges from 1 to `r` and 1 to `s` respectively, and `a`, `b`, `c`, and `d` are pairwise disjoint, and the cardinality of `b` equals the cardinality of `c`, then the equivalence of `a` having even cardinality with `d` having even cardinality is equivalent to the negation of both `r` and `s` being odd.

### Informal sketch
The proof proceeds as follows:
- We start with the assumption that `a UNION b UNION c UNION d = (1..r) CROSS (1..s)`, `PAIRWISE DISJOINT [a;b;c;d]`, and `CARD b = CARD c`.  The goal is to prove `((EVEN(CARD a) <=> EVEN(CARD d)) <=> ~(ODD r /\ ODD s))`.
- First, we introduce the subgoal `CARD a + CARD b + CARD c + CARD d = r * s`, which follows from the disjointness assumption and the given equality concerning the union and Cartesian product. This subgoal is then proven using the fact that `EVEN n` is equivalent to `!(n MOD 2 = 0)`, and using rewriting with rules for even numbers, especially `EVEN_ADD` and `EVEN_MULT`.
- Next, we establish the finiteness of sets `a`, `b`, `c`, and `d` using the premise that they are subsets of the finite set `(1..r) CROSS (1..s)`.
- We apply the cardinality operator `CARD` to the equation `a UNION b UNION c UNION d = (1..r) CROSS (1..s)` to obtain an equation relating the cardinalities of the sets.
- We simplify using facts about the cardinality of Cartesian products `CARD_CROSS` and number ranges `CARD_NUMSEG_1`.
- Using the pairwise disjointness assumption, the cardinality of the union is the sums of the cardinalities `CARD_UNION`.
- Finally, simplification and tautological reasoning lead to the desired result.

### Mathematical insight
The lemma relates the parity of cardinalities of disjoint sets whose union is a rectangle to the parity of the sides of that rectangle. This can be interpreted geometrically.

### Dependencies
- `EVEN_ADD`
- `GSYM NOT_EVEN`
- `EVEN_MULT`
- `FINITE_SUBSET`
- `FINITE_CROSS`
- `FINITE_NUMSEG`
- `CARD_CROSS`
- `CARD_NUMSEG_1`
- `PAIRWISE`
- `DISJOINT`
- `ALL`
- `CARD_UNION`
- `FINITE_UNION`
- `SET_RULE a INTER (b UNION c) = {} <=> a INTER b = {} /\ a INTER c = {}`


---

## RECIPROCITY_SIMPLE

### Name of formal statement
RECIPROCITY_SIMPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RECIPROCITY_SIMPLE = prove
 (`!p q r s.
        prime p /\
        prime q /\
        coprime (p,q) /\
        2 * r + 1 = p /\
        2 * s + 1 = q
        ==> ((q is_quadratic_residue (mod p) <=>
              p is_quadratic_residue (mod q)) <=>
             ~(ODD r /\ ODD s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] GAUSS_LEMMA_SYM) THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] GAUSS_LEMMA_SYM') THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN MATCH_MP_TAC RECIPROCITY_SET_LEMMA THEN
  EXISTS_TAC `{x,y | x IN 1..r /\ y IN 1..s /\ q * x + r < p * y}` THEN
  EXISTS_TAC `{x,y | x IN 1..r /\ y IN 1..s /\ p * y + s < q * x}` THEN
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[PAIRWISE; DISJOINT; EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM;
              ALL; IN_UNION; IN_CROSS; IN_ELIM_PAIR_THM; IN_INTER]
  THENL
   [MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    MAP_EVERY ASM_CASES_TAC [`x IN 1..r`; `y IN 1..s`] THEN ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `~(q * x = p * y)` (fun th -> MP_TAC th THEN ARITH_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `(divides) p`) THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_REFL] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[DIVIDES_REFL; PRIME_1; coprime]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    UNDISCH_TAC `x IN 1..r` THEN REWRITE_TAC[IN_NUMSEG] THEN
    EXPAND_TAC "p" THEN ARITH_TAC;
    ARITH_TAC;
    MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
    REPEAT(EXISTS_TAC `\(x,y). (r + 1) - x,(s + 1) - y`) THEN
    SIMP_TAC[FINITE_SUBCROSS; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG; PAIR_EQ] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    SIMP_TAC[ARITH_RULE `x <= y ==> (y + 1) - ((y + 1) - x) = x`] THEN
    SIMP_TAC[ARITH_RULE
     `1 <= x /\ x <= y ==> 1 <= (y + 1) - x /\ (y + 1) - x <= y`] THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ARITH_RULE
     `x <= y /\ v + y + z < x + u ==> (y - x) + z < u - v`) THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; ARITH_RULE `x <= r ==> x <= r + 1`] THEN
    REWRITE_TAC[ARITH_RULE `a + x < y + a <=> x < y`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    ASM_ARITH_TAC]);;
```

### Informal statement
For all numbers `p`, `q`, `r`, and `s`, if `p` and `q` are prime numbers, `p` and `q` are coprime, `2 * r + 1 = p`, and `2 * s + 1 = q`, then the following equivalence holds: `q` is a quadratic residue modulo `p` if and only if `p` is a quadratic residue modulo `q` if and only if it is not the case that both `r` and `s` are odd.

### Informal sketch
The proof proceeds as follows:
- Apply `GAUSS_LEMMA_SYM` and `GAUSS_LEMMA_SYM'` to introduce Gauss's lemma for `p` and `q` respectively.
- Simplify using assumptions and `COPRIME_SYM`.
- Apply `RECIPROCITY_SET_LEMMA`. This lemma relates the quadratic residuosity to the cardinalities of certain sets.
- Prove the existence of elements in specific sets defined by inequalities.
    - Split the goal into proving existence for the two sets.
    - Fully expand and simplify set membership conditions by rewriting with set theory lemmas.
    - Prove the sets are disjoint
- Define a bijection between specific sets and use it for cardinality manipulation to relate the cardinalities involved in the original `RECIPROCITY_SET_LEMMA`.
- Apply arithmetic simplification to complete the proof.

### Mathematical insight
This theorem expresses a standard formulation of the Law of Quadratic Reciprocity for the Legendre symbol in number theory. It relates the quadratic residuosity of two distinct prime numbers to each other. This is a fundamental result in number theory, simplifying the computation of Legendre symbols and having numerous applications in higher arithmetic.

### Dependencies
- `GAUSS_LEMMA_SYM`
- `GAUSS_LEMMA_SYM'`
- `COPRIME_SYM`
- `RECIPROCITY_SET_LEMMA`
- `PAIRWISE`
- `DISJOINT`
- `EXTENSION`
- `NOT_IN_EMPTY`
- `FORALL_PAIR_THM`
- `ALL`
- `IN_UNION`
- `IN_CROSS`
- `IN_ELIM_PAIR_THM`
- `IN_INTER`
- `PRIME_DIVPROD_EQ`
- `DIVIDES_REFL`
- `PRIME_1`
- `coprime`
- `DIVIDES_LE`
- `IN_NUMSEG`
- `BIJECTIONS_CARD_EQ`
- `FINITE_SUBCROSS`
- `FINITE_NUMSEG`
- `PAIR_EQ`
- `LEFT_SUB_DISTRIB`
- `LE_MULT_LCANCEL`

### Porting notes (optional)
- The proof relies heavily on arithmetic reasoning, so a proof assistant with strong arithmetic automation is recommended.
- The use of sets and cardinalities might require specifying appropriate libraries or definitions.
- The `GAUSS_LEMMA_SYM` and `RECIPROCITY_SET_LEMMA` may need to be ported or proven separately, depending on the available libraries.


---

## RECIPROCITY_LEGENDRE

### Name of formal statement
RECIPROCITY_LEGENDRE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RECIPROCITY_LEGENDRE = prove
 (`!p q. prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q)
         ==> legendre(p,q) * legendre(q,p) =
             --(&1) pow ((p - 1) DIV 2 * (q - 1) DIV 2)`,
  REPEAT STRIP_TAC THEN MAP_EVERY UNDISCH_TAC [`ODD q`; `ODD p`] THEN
  REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN REWRITE_TAC[ADD1] THEN
  REPEAT(DISCH_THEN (fun th -> SUBST1_TAC th THEN ASSUME_TAC(SYM th))) THEN
  REWRITE_TAC[ARITH_RULE `((2 * s + 1) - 1) DIV 2 = s`] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`] RECIPROCITY_SIMPLE) THEN
  ASM_SIMP_TAC[DISTINCT_PRIME_COPRIME; INT_POW_NEG; EVEN_MULT; legendre] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_ODD; INT_POW_ONE] THEN
  MAP_EVERY ASM_CASES_TAC [`EVEN r`; `EVEN s`] THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[TAUT `~(a <=> b) <=> (a <=> ~b)`] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `p is_quadratic_residue (mod q)` THEN
  ASM_REWRITE_TAC[INT_MUL_LNEG; INT_MUL_RNEG; INT_NEG_NEG; INT_MUL_LID]);;
```

### Informal statement
For all `p` and `q`, if `p` is prime and `q` is prime and `p` is odd and `q` is odd and `p` is not equal to `q`, then `legendre(p,q)` multiplied by `legendre(q,p)` is equal to -1 raised to the power of `((p - 1) / 2) * ((q - 1) / 2)`.

### Informal sketch
The proof proceeds as follows:
- Strip the quantifiers and assumptions.
- Eliminate the assumptions `ODD q` and `ODD p` by introducing existentially quantified variables `r` and `s` such that `p = 2 * r + 1` and `q = 2 * s + 1`.
- Rewrite `2 * r + 1` as `SUC (2 * r)`.
- Introduce the assumptions `p = 2 * r + 1` and `q = 2 * s + 1` into the assumptions.
- Simplify the arithmetic expression `((2 * s + 1) - 1) DIV 2` to `s`.
- Specialize the theorem `RECIPROCITY_SIMPLE` to `p`, `q`, `r`, and `s`.
- Simplify using `DISTINCT_PRIME_COPRIME`, `INT_POW_NEG`, `EVEN_MULT`, and the definition of `legendre`.
- Rewrite using De Morgan's law, the definition of `NOT_ODD`, and `INT_POW_ONE`.
- Perform case splits on whether `r` is even and whether `s` is even.
- Perform automatic rewriting within the assumptions.
- Simplify using a tautology.
- Universally quantify the result.
- Perform a case split on whether `p` is a quadratic residue modulo `q`.
- Simplify using laws of integer multiplication.

### Mathematical insight
This theorem is the Law of Quadratic Reciprocity, specifically stated in terms of the Legendre symbol. It relates the Legendre symbol of two distinct odd primes `p` and `q` to the Legendre symbol of `q` and `p`. The Legendre symbol `legendre(p,q)` is 1 if `p` is a quadratic residue modulo `q`, -1 if `p` is a quadratic non-residue modulo `q`, and 0 if `p` is divisible by `q`.

### Dependencies
- `prime`
- `ODD`
- `legendre`
- `ODD_EXISTS`
- `LEFT_IMP_EXISTS_THM`
- `RIGHT_IMP_FORALL_THM`
- `ADD1`
- `RECIPROCITY_SIMPLE`
- `DISTINCT_PRIME_COPRIME`
- `INT_POW_NEG`
- `EVEN_MULT`
- `DE_MORGAN_THM`
- `NOT_ODD`
- `INT_POW_ONE`
- `INT_MUL_LNEG`
- `INT_MUL_RNEG`
- `INT_NEG_NEG`
- `INT_MUL_LID`


---

