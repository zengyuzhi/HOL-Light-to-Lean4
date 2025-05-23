# div3.ml

## Overview

Number of statements: 3

The `div3.ml` file formalizes the divisibility by 3 rule, providing a set of definitions and theorems related to this concept. It imports necessary modules from `prime.ml` and `pocklington.ml`, indicating a connection to primality and potentially Pocklington's theorem. The file's content is likely focused on proving properties and rules for determining divisibility by 3, contributing to the library's number theory foundations. Its purpose is to establish a formal basis for reasoning about divisibility by 3 within the HOL Light system.

## EXP_10_CONG_3

### Name of formal statement
EXP_10_CONG_3

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EXP_10_CONG_3 = prove
 (`!n. (10 EXP n == 1) (mod 3)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; CONG_REFL] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `10 * 1` THEN CONJ_TAC THEN
  ASM_SIMP_TAC[CONG_MULT; CONG_REFL] THEN
  SIMP_TAC[CONG; ARITH] THEN CONV_TAC NUM_REDUCE_CONV);;
```

### Informal statement
For all natural numbers n, 10 raised to the power of n is congruent to 1 modulo 3.

### Informal sketch
* The proof starts by applying `INDUCT_TAC`, indicating a proof by induction on n.
* It then uses `REWRITE_TAC` with `EXP` and `CONG_REFL` to set up the congruence relation.
* The `MATCH_MP_TAC CONG_TRANS` tactic is applied to introduce a transitive congruence, with `EXISTS_TAC `10 * 1`` providing a witness for this transitivity.
* The proof then splits into two parts with `CONJ_TAC`, and `ASM_SIMP_TAC` is used with `CONG_MULT` and `CONG_REFL` to simplify the congruences.
* Finally, `SIMP_TAC` with `CONG` and `ARITH` simplifies further, and `CONV_TAC NUM_REDUCE_CONV` is applied for numerical reduction.

### Mathematical insight
This statement is important because it establishes a periodicity property of powers of 10 modulo 3, which can be useful in various number theoretic arguments. The proof illustrates how induction and properties of congruences can be used to establish such results.

### Dependencies
* Theorems:
  + `CONG_TRANS`
  + `CONG_REFL`
  + `CONG_MULT`
* Definitions:
  + `EXP`
  + `CONG`
* Inductive rules:
  + `INDUCT_TAC`

### Porting notes
When translating this into another proof assistant, pay attention to how induction and congruence properties are handled. Specifically, the use of `INDUCT_TAC`, `MATCH_MP_TAC`, and `EXISTS_TAC` may need to be adapted based on the target system's support for these tactics. Additionally, the representation of `CONG` and `EXP` may vary, requiring adjustments to the `REWRITE_TAC` and `SIMP_TAC` steps.

---

## SUM_CONG_3

### Name of formal statement
SUM_CONG_3

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUM_CONG_3 = prove
 (`!d n. (nsum(0..n) (\i. 10 EXP i * d(i)) == nsum(0..n) (\i. d i)) (mod 3)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THENL
   [REWRITE_TAC[EXP; MULT_CLAUSES; CONG_REFL]; ALL_TAC] THEN
  REWRITE_TAC[LE_0] THEN MATCH_MP_TAC CONG_ADD THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV) [ARITH_RULE `d = 1 * d`] THEN
  MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL; EXP_10_CONG_3])
```

### Informal statement
For all functions `d` and all natural numbers `n`, the following congruence holds modulo 3: the sum from 0 to `n` of `10` raised to the power of `i` times `d(i)` is congruent to the sum from 0 to `n` of `d(i)`.

### Informal sketch
* The proof starts by generalizing the statement for all `d` and `n` using `GEN_TAC`.
* It then proceeds by induction on `n` using `INDUCT_TAC`.
* The base case involves rewriting using `NSUM_CLAUSES_NUMSEG` to expand the sum, and then simplifying using `EXP`, `MULT_CLAUSES`, and `CONG_REFL`.
* The inductive step involves using `CONG_ADD` to reduce the problem to a simpler case, and then applying `ASM_REWRITE_TAC` to simplify further.
* The proof also involves recognizing that `d` is equivalent to `1 * d` using `ARITH_RULE`, and applying `CONG_MULT` to simplify the multiplication.
* Finally, the proof uses `EXP_10_CONG_3` to simplify the expression involving `10` raised to a power.

### Mathematical insight
This theorem is important because it establishes a congruence relation between two sums involving a function `d` and powers of 10, modulo 3. The key idea is to use properties of modular arithmetic and induction to simplify the expression and prove the congruence.

### Dependencies
* Theorems:
	+ `CONG_ADD`
	+ `CONG_MULT`
	+ `CONG_REFL`
	+ `EXP_10_CONG_3`
* Definitions:
	+ `NSUM_CLAUSES_NUMSEG`
	+ `EXP`
	+ `MULT_CLAUSES`
	+ `ARITH_RULE`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of modular arithmetic and the `nsum` function, as these may be represented differently in other systems. Additionally, the use of `GEN_TAC` and `INDUCT_TAC` may need to be translated into the corresponding constructs in the target system.

---

## DIVISIBILITY_BY_3

### Name of formal statement
DIVISIBILITY_BY_3

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DIVISIBILITY_BY_3 = prove
 (`3 divides (nsum(0..n) (\i. 10 EXP i * d(i))) <=>
   3 divides (nsum(0..n) (\i. d i))`,
  MATCH_MP_TAC CONG_DIVIDES THEN REWRITE_TAC[SUM_CONG_3])
```

### Informal statement
The statement `DIVISIBILITY_BY_3` asserts that for all natural numbers `n` and a function `d`, the following equivalence holds: 3 divides the sum from 0 to `n` of `10` raised to the power of `i` times `d(i)` if and only if 3 divides the sum from 0 to `n` of `d(i)`.

### Informal sketch
* The proof involves using the `MATCH_MP_TAC` tactic to apply the `CONG_DIVIDES` theorem, which likely establishes a congruence relation that helps in simplifying the divisibility condition.
* The `REWRITE_TAC` tactic is then applied with the `SUM_CONG_3` theorem to rewrite the summation in a form that facilitates the proof of the equivalence.
* The key idea is to manipulate the expression involving the sum and the exponential term to show that the divisibility by 3 of one sum is equivalent to the divisibility by 3 of the other sum.

### Mathematical insight
This theorem seems to provide insight into how the divisibility properties of sums relate to the divisibility properties of their components, particularly in the context of geometric series or sequences involving exponential terms. It highlights how certain properties can be preserved or transformed under specific operations, which is crucial in number theory and algebra.

### Dependencies
* Theorems:
  - `CONG_DIVIDES`
  - `SUM_CONG_3`
* Definitions:
  - None explicitly mentioned, but the use of `nsum`, `EXP`, and `divides` suggests dependencies on basic arithmetic and possibly sequence or series definitions.

### Porting notes
When translating this theorem into another proof assistant like Lean, Coq, or Isabelle, special attention should be given to how these systems handle summations, exponential functions, and divisibility. The `MATCH_MP_TAC` and `REWRITE_TAC` tactics have counterparts in these systems (e.g., `apply` and `rewrite` in Isabelle), but the exact formulation and the underlying theorems like `CONG_DIVIDES` and `SUM_CONG_3` will need to be appropriately translated or proven within the target system.

---

