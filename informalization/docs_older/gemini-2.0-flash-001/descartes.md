# descartes.ml

## Overview

Number of statements: 24

The file `descartes.ml` formalizes Descartes's Rule of Signs. It provides a proof of the theorem relating the number of positive roots of a polynomial to the number of sign changes in its coefficients. The development, by Rob Arthan, uses results from real analysis in multivariate calculus, imported from `Multivariate/realanalysis.ml`.


## OPPOSITE_SIGNS

### Name of formal statement
OPPOSITE_SIGNS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OPPOSITE_SIGNS = prove
 (`!a b:real. a * b < &0 <=> &0 < a /\ b < &0 \/ a < &0 /\ &0 < b`,
  REWRITE_TAC[REAL_ARITH `a * b < &0 <=> &0 < a * --b`; REAL_MUL_POS_LT] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
For all real numbers `a` and `b`, the product `a * b` is less than 0 if and only if (`0 < a` and `b < 0`) or (`a < 0` and `0 < b`).

### Informal sketch
The proof proceeds as follows:
- First, rewrite the inequality `a * b < &0` to `&0 < a * --b` using `REAL_ARITH`.
- Next, rewrite `&0 < a * --b` with `REAL_MUL_POS_LT`, which states that `0 < a * b` if and only if `0 < a /\ 0 < b \/ a < 0 /\ b < 0`, to the equivalent form.
- Finally, apply `REAL_ARITH_TAC` to complete the proof.

### Mathematical insight
This theorem formalizes the familiar rule that the product of two real numbers is negative precisely when one number is positive and the other is negative. It's a fundamental property of ordered fields like the real numbers.

### Dependencies
- Theories: `Multivariate/realanalysis.ml`
- Theorems: `REAL_ARITH a * b < &0 <=> &0 < a * --b`, `REAL_MUL_POS_LT`

### Porting notes (optional)
- This theorem relies on the properties of ordered fields, specifically the real numbers as defined in HOL Light. Ensure that the target proof assistant has a well-developed theory of ordered fields and real numbers. The tactics `REAL_ARITH_TAC` and rewriting with `REAL_MUL_POS_LT` indicate a need for decision procedures or simplification rules related to real arithmetic.


---

## VARIATION_SET_FINITE

### Name of formal statement
VARIATION_SET_FINITE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_SET_FINITE = prove
 (`FINITE s ==> FINITE {p,q | p IN s /\ q IN s /\ P p q}`,
  REWRITE_TAC[SET_RULE
   `{p,q | p IN s /\ q IN t /\ R p q} =
    {p,q | p IN s /\ q IN {q | q IN t /\ R p q}}`] THEN
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_RESTRICT]);;
```
### Informal statement
If the set `s` is finite, then the set of pairs `{p, q}` such that `p` is in `s`, `q` is in `s`, and `P p q` holds, is also finite.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the set comprehension `{p,q | p IN s /\ q IN s /\ P p q}` using the theorem `SET_RULE` to `{p,q | p IN s /\ q IN {q | q IN s /\ P p q}}`.  This transforms the set comprehension into a form suitable for further manipulation with theorems about finiteness.
- Then, use `SIMP_TAC` with the theorems `FINITE_PRODUCT_DEPENDENT` and `FINITE_RESTRICT`. The theorem `FINITE_PRODUCT_DEPENDENT` states that if `s` is finite, then the set of pairs `{p, q | p IN s /\ q IN (f p)}` is finite, provided that for each `p` in `s`, the set `f p` is finite. The theorem `FINITE_RESTRICT` states that if a set `s` is finite, then the subset `{x | x IN s /\ P x}` is also finite. Applying these theorems discharges the goal.

### Mathematical insight
The theorem establishes that if a set `s` contains a finite number of elements, constructing related pairs from within that set, under the constraint of a predicate `P`, also leads to another finite set. This is a fundamental property when dealing with finiteness and set constructions.

### Dependencies
- `SET_RULE`
- `FINITE_PRODUCT_DEPENDENT`
- `FINITE_RESTRICT`


---

## variation

### Name of formal statement
variation

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let variation = new_definition
 `variation s (a:num->real) =
     CARD {(p,q) | p IN s /\ q IN s /\ p < q /\
                   a(p) * a(q) < &0 /\
                   !i. i IN s /\ p < i /\ i < q ==> a(i) = &0 }`;;
```

### Informal statement
The variation of a function `a` (from natural numbers to real numbers) on a set `s` is defined as the cardinality of the set of pairs `(p, q)` such that:
1. `p` is in `s` and `q` is in `s`.
2. `p` is less than `q`.
3. `a(p)` multiplied by `a(q)` is less than 0.
4. For all `i` in `s` such that `p` is less than `i` and `i` is less than `q`, `a(i)` equals 0.

### Informal sketch
- The definition `variation s a` counts the number of sign changes in the sequence `a` when restricted to the indices in the set `s`, where intervening values between the sign changes must be zero.
- The condition `p < q` ensures that we are looking at ordered pairs.
- The condition `a(p) * a(q) < &0` ensures that `a(p)` and `a(q)` have opposite signs.
- The condition `!i. i IN s /\ p < i /\ i < q ==> a(i) = &0` ensures that between indices `p` and `q`, all values of `a(i)` for `i` in `s` are zero.
- The outer `CARD` operation computes the cardinality (number of elements) of the constructed set of pairs.

### Mathematical insight
This definition formalizes the notion of "variation" or "sign changes" in a sequence of numbers, specifically focusing on counting instances where the sign changes and any intermediate values are zero. This is useful in the context of bounding the number of real roots of a polynomial, as it relates the sign changes of coefficients to the number of roots.

### Dependencies
- `CARD`
- `IN`


---

## VARIATION_EQ

### Name of formal statement
VARIATION_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_EQ = prove
 (`!a b s. (!i. i IN s ==> a i = b i) ==> variation s a = variation s b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[variation] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  ASM_MESON_TAC[]);;
```

### Informal statement
For all `a`, `b`, and `s`, if for all `i`, `i` being in `s` implies `a i` equals `b i`, then `variation s a` equals `variation s b`.

### Informal sketch
- The goal is to prove that if two functions `a` and `b` agree on a set `s`, then their variations on that set are equal.
- First, the outermost quantifiers and the implication are eliminated using `REPEAT STRIP_TAC`.
- Then, the definition of `variation` is unfolded using `REWRITE_TAC[variation]`.
- Next, `AP_TERM_TAC` is used to apply the assumption `!i. i IN s ==> a i = b i` to the abstraction (`%i. if i IN s then a i else 0`) and (`%i. if i IN s then b i else 0`).
- We then rewrite using `EXTENSION`, `FORALL_PAIR_THM`, and `IN_ELIM_PAIR_THM`. These theorems relate to the extensionality of functions (`EXTENSION`), the equivalence of universal quantification over pairs and conjunction (`FORALL_PAIR_THM`), and the elimination of the `IN` predicate when applied to pairs (`IN_ELIM_PAIR_THM`).
- Finally, `ASM_MESON_TAC[]` is used to complete the proof by discharging any remaining assumptions.

### Mathematical insight
This theorem states that the `variation` function depends only on the function's values on the specified set. If two functions have the same values on a given set, their variations with respect to that set will be the same. This result is important because it allows one to reason about the `variation` function without needing to consider the function's behavior outside of the set in question.

### Dependencies
- `variation`
- `EXTENSION`
- `FORALL_PAIR_THM`
- `IN_ELIM_PAIR_THM`


---

## VARIATION_SUBSET

### Name of formal statement
VARIATION_SUBSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_SUBSET = prove
 (`!a s t. t SUBSET s /\ (!i. i IN (s DIFF t) ==> a i = &0)
           ==> variation s a = variation t a`,
  REWRITE_TAC[IN_DIFF; SUBSET] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[variation] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  ASM_MESON_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL]);;
```
### Informal statement
For all functions `a` from the natural numbers to the reals, and all sets of natural numbers `s` and `t`, if `t` is a subset of `s`, and for all `i` in the set difference of `s` and `t`, `a i` is equal to 0, then the variation of `s` with respect to `a` is equal to the variation of `t` with respect to `a`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using `IN_DIFF` and `SUBSET` to expand the hypothesis `t SUBSET s /\ (!i. i IN (s DIFF t) ==> a i = &0)`.
- Then, rewrite using the definition of `variation`.
- Apply `AP_TERM_TAC` to equate the terms being summed over.
- Then, rewrite using `EXTENSION`, `FORALL_PAIR_THM`, and `IN_ELIM_PAIR_THM`. This unpacks the set membership conditions and equalities arising from the definition of variation.
- Finally, use `ASM_MESON_TAC` with `REAL_MUL_LZERO`, `REAL_MUL_RZERO`, and `REAL_LT_REFL` to prove the final result using the assumption that for elements in `s` but not in `t`, the function `a` returns 0.

### Mathematical insight
This theorem states that if we have two sets `s` and `t` where `t` is a subset of `s`, and a function `a` is zero for elements in `s` that are not in `t`, then the variation of `a` over `s` is the same as the variation of `a` over `t`. This is because the additional elements in `s` contribute nothing to the sum defining the variation, as they are multiplied by zero.

### Dependencies
#### Constants
- `SUBSET`
- `DIFF`
- `IN`
- `variation`

#### Theorems
- `IN_DIFF`
- `SUBSET`
- `EXTENSION`
- `FORALL_PAIR_THM`
- `IN_ELIM_PAIR_THM`
- `REAL_MUL_LZERO`
- `REAL_MUL_RZERO`
- `REAL_LT_REFL`


---

## VARIATION_SPLIT

### Name of formal statement
VARIATION_SPLIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_SPLIT = prove
 (`!a s n.
        FINITE s /\ n IN s /\ ~(a n = &0)
        ==> variation s a = variation {i | i IN s /\ i <= n} a +
                            variation {i | i IN s /\ n <= i} a`,
  REWRITE_TAC[variation] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_SIMP_TAC[VARIATION_SET_FINITE; FINITE_RESTRICT] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC;
    REWRITE_TAC[IN_UNION; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC;
      STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
        MP_TAC(SPEC `n:num` th) THEN ASM_REWRITE_TAC[] THEN ASSUME_TAC th) THEN
      SIMP_TAC[TAUT `~(a /\ b) <=> ~b \/ ~a`] THEN MATCH_MP_TAC MONO_OR] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    TRY(FIRST_ASSUM MATCH_MP_TAC) THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `n:num` th) THEN ASM_REWRITE_TAC[]) THEN
    ASM_ARITH_TAC]);;
```

### Informal statement
For all `a`, `s`, and `n`, if `s` is a finite set, `n` is an element of `s`, and `a(n)` is not equal to 0, then the `variation` of `s` with respect to `a` is equal to the sum of the `variation` of the set of elements `i` in `s` such that `i` is less than or equal to `n` with respect to `a`, and the `variation` of the set of elements `i` in `s` such that `n` is less than or equal to `i` with respect to `a`.

### Informal sketch
The proof proceeds by:
- Rewriting with the definition of `variation`.
- Simplifying the goal and rewriting `CARD_UNION_EQ`.
- Applying simplification using lemmas about finiteness of sets (`VARIATION_SET_FINITE` and `FINITE_RESTRICT`).
- Expanding set extensions and universal quantification over pairs.
- Splitting the conjunction into two subgoals.
- Simplifying the first subgoal using set theory rules.
- For the second subgoal, simplifying using set theory rules and then generalizing over `n`.
- Applying equality tactics and simplifying using tautologies and monotonicity.
- Applying rule assumptions and rewriting.
- Repeatedly stripping quantifiers and assumptions.
- Applying matching tactics, specializing with `n:num`, and applying arithmetic tactics.

### Mathematical insight
This theorem provides a way to split the `variation` of a finite set `s` at a point `n` within the set. The `variation` function likely represents a weighted sum or product over the set, and this theorem allows partitioning the set into two subsets based on their relation to `n` (less than or equal, greater than or equal), thus splitting the overall `variation` accordingly. This can be useful for inductive proofs or for simplifying calculations of `variation` when dealing with large sets.

### Dependencies
- `variation`
- `VARIATION_SET_FINITE`
- `FINITE_RESTRICT`
- `EXTENSION`
- `FORALL_PAIR_THM`
- `IN_INTER`
- `NOT_IN_EMPTY`
- `IN_ELIM_PAIR_THM`
- `IN_NUMSEG`
- `IN_ELIM_THM`
- `IN_UNION`
- `CARD_UNION_EQ`

### Porting notes (optional)
- This theorem relies on properties of finite sets and set operations (`IN_INTER`, `IN_UNION`, etc.). Ensure the target proof assistant's set theory library aligns with HOL Light's.
- The proof uses a combination of rewriting, simplification, and arithmetic tactics. The corresponding tactics or methods in other proof assistants might require some adaptation.


---

## VARIATION_SPLIT_NUMSEG

### Name of formal statement
VARIATION_SPLIT_NUMSEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_SPLIT_NUMSEG = prove
 (`!a m n p. n IN m..p /\ ~(a n = &0)
             ==> variation(m..p) a = variation(m..n) a + variation(n..p) a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP
   (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> b /\ c ==> a ==> d`]
     VARIATION_SPLIT)) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC);;
```

### Informal statement
For any function `a` mapping natural numbers to real numbers, and any natural numbers `m`, `n`, and `p`, if `n` is in the interval `m..p` and `a(n)` is not equal to 0, then the `variation` of `a` on the interval `m..p` is equal to the `variation` of `a` on the interval `m..n` plus the `variation` of `a` on the interval `n..p`.

### Informal sketch
The proof proceeds as follows:
- Generalize and discharge assumptions.
- Apply `VARIATION_SPLIT` after rewriting the tautology `a /\ b /\ c ==> d <=> b /\ c ==> a ==> d`. This separates the interval summation at the point `n`.
- Rewrite with `FINITE_NUMSEG` to show that `m..p` is finite.
- Perform a substitution using `SUBST1_TAC` after discharging the assumption.
- Apply the binary operator theorem (`BINOP_TAC`).
- Apply theorems to the argument and term.
- Rewrite using `EXTENSION`, `IN_ELIM_THM`, and `IN_NUMSEG`.
- Apply `IN_NUMSEG` to the assumptions.
- Use arithmetic tactics (`ASM_ARITH_TAC`).

### Mathematical insight
This theorem describes how the total variation of a function over an interval can be split into the sum of the variations over sub-intervals, provided that the splitting point is within the original interval and the function is non-zero at the splitting point. This is a crucial property for analyzing the variation of functions, especially in contexts like real analysis or signal processing.

### Dependencies
- `VARIATION_SPLIT`
- `FINITE_NUMSEG`
- `EXTENSION`
- `IN_ELIM_THM`
- `IN_NUMSEG`


---

## VARIATION_1

### Name of formal statement
VARIATION_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_1 = prove
 (`!a n. variation {n} a = 0`,
  REWRITE_TAC[variation; IN_SING] THEN
  REWRITE_TAC[ARITH_RULE `p:num = n /\ q = n /\ p < q /\ X <=> F`] THEN
  MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; NOT_IN_EMPTY]);;
```
### Informal statement
For all `a` and `n`, the variation over the set `{n}` of the function `a` is equal to 0.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definitions of `variation` and `IN_SING` (membership in a singleton set). This transforms the goal `variation {n} a = 0` to `!p q. p IN {n} /\ q IN {n} ==> a p <= a q`.
- Then rewrite using arithmetic simplification and a conditional equivalence rule.
- Apply the theorem that the cardinality of the empty set is 0. Apply the MESON tactic with `CARD_CLAUSES` to automatically prove `s = {} ==> CARD s = 0`.
- Finally, rewrite using the definitions of `EXTENSION`, `FORALL_PAIR_THM`, `IN_ELIM_PAIR_THM`, and `NOT_IN_EMPTY`.

### Mathematical insight
The variation of a function over a singleton set is always zero. This is because the range is minimized to a single value, and the difference between the greatest and least values is thus zero.

### Dependencies
- Definitions: `variation`, `IN_SING`, `EXTENSION`
- Theorems: `ARITH_RULE`, `CARD_CLAUSES`, `FORALL_PAIR_THM`, `IN_ELIM_PAIR_THM`, `NOT_IN_EMPTY`


---

## VARIATION_2

### Name of formal statement
VARIATION_2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_2 = prove
 (`!a m n. variation {m,n} a = if a(m) * a(n) < &0 then 1 else 0`,
  GEN_TAC THEN MATCH_MP_TAC WLOG_LT THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSERT_AC; VARIATION_1; GSYM REAL_NOT_LE; REAL_LE_SQUARE];
    REWRITE_TAC[INSERT_AC; REAL_MUL_SYM];
    REPEAT STRIP_TAC THEN REWRITE_TAC[variation; IN_INSERT; NOT_IN_EMPTY] THEN
    ONCE_REWRITE_TAC[TAUT
     `a /\ b /\ c /\ d /\ e <=> (a /\ b /\ c) /\ d /\ e`] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `m:num < n
      ==> ((p = m \/ p = n) /\ (q = m \/ q = n) /\ p < q <=>
           p = m /\ q = n)`] THEN
    REWRITE_TAC[MESON[] `(p = m /\ q = n) /\ X p q <=>
                         (p = m /\ q = n) /\ X m n`] THEN
    REWRITE_TAC[ARITH_RULE `(i:num = m \/ i = n) /\ m < i /\ i < n <=> F`] THEN
    ASM_CASES_TAC `a m * a(n:num) < &0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[SET_RULE `{p,q | p = a /\ q = b} = {(a,b)}`] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH];
      MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
      SIMP_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; NOT_IN_EMPTY]]]);;
```
### Informal statement
For all functions `a` from numbers to reals, and for all numbers `m` and `n`, `variation {m, n} a` is equal to 1 if `a(m) * a(n)` is less than 0, and 0 otherwise.

### Informal sketch
The proof proceeds as follows:
- Assume without loss of generality that `m < n`.
- Expand the definition of `variation {m, n} a`. This involves considering the set of pairs `(p, q)` where `p` and `q` are in `{m, n}` and `p < q`.
- Simplify the conditions `p = m \/ p = n` and `q = m \/ q = n` and `p < q` to derive `p = m /\ q = n`.
- The condition `(i = m \/ i = n) /\  m < i /\ i < n` simplifies to false.
- Perform case analysis on `a m * a n < 0`.
- Apply the rule for singleton sets `{p,q | p = a /\ q = b} = {(a,b)}`.
- Simplify using cardinality rules, finiteness rules, and arithmetic.
- Apply a theorem stating that the cardinality of the empty set is 0.
- Simplify using set extension, the theorem forall pair, the in elim pair theorem, and the fact that something is not in the empty set.

### Mathematical insight
The theorem `VARIATION_2` provides a simplified expression for the `variation` of a function `a` over a set containing two elements `{m, n}`. It states that the variation is 1 if the product of the function values at `m` and `n` is negative, and 0 otherwise. This essentially captures the idea of a sign change occurring between the points `m` and `n`.

### Dependencies
- Definitions: `variation`
- Theorems: `VARIATION_1`, `REAL_NOT_LE`, `REAL_LE_SQUARE`, `REAL_MUL_SYM`, `INSERT_AC`, `IN_INSERT`, `NOT_IN_EMPTY`, `TAUT \`a /\ b /\ c /\ d /\ e <=> (a /\ b /\ c) /\ d /\ e\``, `ARITH_RULE \`m:num < n ==> ((p = m \\/ p = n) /\ (q = m \\/ q = n) /\ p < q <=> p = m /\ q = n)\``, `MESON[] \`(p = m /\ q = n) /\ X p q <=> (p = m /\ q = n) /\ X m n\``, `ARITH_RULE \`(i:num = m \/ i = n) /\ m < i /\ i < n <=> F\``, `SET_RULE \`{p,q | p = a /\ q = b} = {(a,b)}\``, `CARD_CLAUSES`, `FINITE_RULES`, `ARITH`, `MESON[CARD_CLAUSES] \`s = {} ==> CARD s = 0\``, `EXTENSION`, `FORALL_PAIR_THM`, `IN_ELIM_PAIR_THM`


---

## VARIATION_3

### Name of formal statement
VARIATION_3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_3 = prove
 (`!a m n p.
        m < n /\ n < p
        ==> variation {m,n,p} a = if a(n) = &0 then variation{m,p} a
                                  else variation {m,n} a + variation{n,p} a`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC VARIATION_SUBSET THEN ASM SET_TAC[];
    MP_TAC(ISPECL [`a:num->real`; `{m:num,n,p}`; `n:num`] VARIATION_SPLIT) THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC]);;
```
### Informal statement
For all functions `a` from numbers to reals, and for all numbers `m`, `n`, and `p`, if `m < n` and `n < p`, then the variation of `a` over the set `{m, n, p}` is equal to `if a(n) = 0 then variation {m, p} a else variation {m, n} a + variation {n, p} a`.

### Informal sketch
The proof proceeds by:
- Stripping the quantifiers and the implication.
- Performing case analysis based on the condition `a(n) = 0`.
- In the first case, where `a(n) = 0`, we use `VARIATION_SUBSET` to reduce `variation {m, n, p} a` to `variation {m, p} a`. The set `{m, n, p}` becomes the set `{m, p}` which is proven using the subset property with the help of the assumption `a(n) = 0`.
- In the second case, where `a(n) != 0`, we apply `VARIATION_SPLIT` instantiated with `a`, `{m,n,p}`, and `n` and then simplify using basic set properties, definitions, and arithmetic. Then we rewrite using definitions related to sets. The final step consists of applying arithmetic reasoning.

### Mathematical insight
This theorem provides a recursive or inductive-style characterization of the `variation` over a set of three elements. The key idea is that when `a(n)` is non-zero then the variation of `a` on `{m,n,p}` is the sum of the variation of `a` on `{m,n}` and `{n,p}`. When `a(n)` is equal to zero, the `variation` of `a` on `{m,n,p}` reduces to the `variation` of `a` on `{m,p}`, thus eliminating `n`.

### Dependencies
- `VARIATION_SUBSET`
- `VARIATION_SPLIT`
- `FINITE_INSERT`
- `FINITE_EMPTY`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `EXTENSION`
- `IN_ELIM_THM`


---

## VARIATION_OFFSET

### Name of formal statement
VARIATION_OFFSET

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_OFFSET = prove
 (`!p m n a. variation(m+p..n+p) a = variation(m..n) (\i. a(i + p))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[variation] THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN MAP_EVERY EXISTS_TAC
   [`\(i:num,j). i - p,j - p`; `\(i:num,j). i + p,j + p`] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
  SIMP_TAC[VARIATION_SET_FINITE; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_NUMSEG; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN TRY ASM_ARITH_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `y < &0 ==> x = y ==> x < &0`)) THEN
    BINOP_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `i - p:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; MATCH_MP_TAC EQ_IMP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;
```

### Informal statement
For all `p`, `m`, `n`, and `a`, the variation of `a` over the shifted interval `m+p` to `n+p` is equal to the variation over the interval `m` to `n` of the function that maps `i` to `a(i + p)`.

### Informal sketch
The proof proceeds as follows:
- Expand the definition of `variation` on both sides using the definition `variation`.
- Apply `BIJECTIONS_CARD_EQ` to reduce the goal to showing a bijection between the cardinalities of the sets.
- Introduce explicit bijections using `EXISTS_TAC` for both directions:
  - Mapping `(i, j)` to `(i - p, j - p)`.
  - Mapping `(i, j)` to `(i + p, j + p)`.
- Simplify the definitions of the bijections using `FORALL_IN_GSPEC` and `IN_ELIM_PAIR_THM`.
- Prove that the sets are finite using `VARIATION_SET_FINITE` and `FINITE_NUMSEG`.
- Simplify the set membership conditions using `IN_NUMSEG` and `PAIR_EQ`.
- Perform automatic arithmetic reasoning using `ASM_ARITH_TAC` to discharge the remaining assumptions. Several cases arise, requiring different arithmetic tactics to complete the proof. These cases involve showing inequalities and establishing relationships between variables based on assumptions in the context.

### Mathematical insight
This theorem establishes that the `variation` function is invariant under index shifting. Shifting the indices of the interval over which the variation is computed is equivalent to applying an inverse-shifted argument to the function whose variation is being calculated.

### Dependencies
- Definition: `variation`
- Theorem: `BIJECTIONS_CARD_EQ`
- Theorem: `FORALL_IN_GSPEC`
- Theorem: `IN_ELIM_PAIR_THM`
- Theorem: `VARIATION_SET_FINITE`
- Theorem: `FINITE_NUMSEG`
- Theorem: `IN_NUMSEG`
- Theorem: `PAIR_EQ`
- Theorem: `EQ_IMP`


---

## ARTHAN_LEMMA

### Name of formal statement
ARTHAN_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ARTHAN_LEMMA = prove
 (`!n a b.
        ~(a n = &0) /\ (b n = &0) /\ (!m. sum(0..m) a = b m)
        ==> ?d. ODD d /\ variation (0..n) a = variation (0..n) b + d`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "*") THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    ASM_REWRITE_TAC[SUM_SING_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> n = 1 \/ 2 <= n`))
  THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `1` THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    REWRITE_TAC[VARIATION_2; OPPOSITE_SIGNS] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
    SIMP_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
    CONV_TAC NUM_REDUCE_CONV THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p. 1 < p /\ p <= n /\ ~(a p = &0)` MP_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `2 <= n ==> 1 < n`; LE_REFL];
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ c /\ ~d) <=> a /\ b /\ c ==> d`] THEN
    STRIP_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN(MP_TAC o SPECL
   [`(\i. if i + 1 = 1 then a 0 + a 1 else a(i + 1)):num->real`;
    `(\i. b(i + 1)):num->real`]) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1) /\ n - 1 + 1 = n`] THEN
  REWRITE_TAC[GSYM(SPEC `1` VARIATION_OFFSET)] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(0..m+1) a` THEN CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH_RULE `0 + 1 <= n + 1`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_ASSOC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; SUM_OFFSET] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN ARITH_TAC;
      ASM_REWRITE_TAC[]];
    ABBREV_TAC `a':num->real = \m. if m = 1 then a 0 + a 1 else a m` THEN
    ASM_SIMP_TAC[ARITH_RULE
     `2 <= n ==> n - 1 + 1 = n /\ n - 1 - 1 + 1 = n - 1`] THEN
    CONV_TAC NUM_REDUCE_CONV] THEN
  SUBGOAL_THEN
   `variation (1..n) a' = variation {1,p} a' + variation (p..n) a /\
    variation (0..n) a = variation {0,1,p} a + variation (p..n) a`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
     [EXISTS_TAC `variation(1..p) a' + variation(p..n) a'`;
      EXISTS_TAC `variation(0..p) a + variation(p..n) a`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN EXPAND_TAC "a'" THEN
       REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
       BINOP_TAC THENL
        [MATCH_MP_TAC VARIATION_SUBSET; MATCH_MP_TAC VARIATION_EQ] THEN
       EXPAND_TAC "a'" THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
       REWRITE_TAC[IN_NUMSEG] THEN TRY(GEN_TAC THEN ASM_ARITH_TAC) THEN
       (CONJ_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[IN_DIFF]]) THEN
       REWRITE_TAC[IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
       REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
       TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC]);
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP (INT_ARITH
   `a + b:int = c + d ==> c = (a + b) - d`)) THEN
  REWRITE_TAC[INT_ARITH `a + b:int = c + d <=> d = (a + b) - c`] THEN
  ASM_CASES_TAC `a 0 + a 1 = &0` THENL
   [SUBGOAL_THEN `!i. 0 < i /\ i < p ==> b i = &0` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `i:num`) THEN
      ASM_SIMP_TAC[SUM_CLAUSES_LEFT; LE_0;
                   ARITH_RULE `0 < i ==> 0 + 1 <= i`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[REAL_ADD_ASSOC; REAL_ADD_LID] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(b:num->real) p = a p` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
      SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 < p`;
                 ARITH_RULE `1 < p ==> 0 < p /\ 0 <= p`] THEN
      ASM_REWRITE_TAC[REAL_EQ_ADD_RCANCEL_0] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `variation(0..n) b = variation {0,p} b + variation(1..n) b`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..p) b + variation(p..n) b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC[IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `p:num`) THEN
        SIMP_TAC[SUM_CLAUSES_RIGHT; ASSUME `1 < p`;
                 ARITH_RULE `1 < p ==> 0 < p /\ 0 <= p`] THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `~(ap = &0) ==> s = &0 ==> ~(s + ap = &0)`)) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        BINOP_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
        MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
        (CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC];
    SUBGOAL_THEN `variation(0..n) b = variation {0,1} b + variation(1..n) b`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..1) b + variation(1..n) b` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN REWRITE_TAC[IN_NUMSEG] THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `1`) THEN
        SIMP_TAC[SUM_CLAUSES_NUMSEG; num_CONV `1`] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
        AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_DIFF; IN_NUMSEG; IN_INSERT; NOT_IN_EMPTY] THEN
        ARITH_TAC];
      SUBGOAL_THEN `(b:num->real) 1 = a 0 + a 1` ASSUME_TAC THENL
       [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
        SIMP_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
        CONV_TAC NUM_REDUCE_CONV;
        ALL_TAC]]] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `0`)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  ASM_SIMP_TAC[VARIATION_3; ARITH; OPPOSITE_SIGNS] THEN COND_CASES_TAC THEN
  REWRITE_TAC[VARIATION_2; OPPOSITE_SIGNS; REAL_LT_REFL] THEN
  EXPAND_TAC "a'" THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < p ==> ~(p = 1)`; REAL_LT_REFL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(BINDER_CONV(RAND_CONV(RAND_CONV INT_POLY_CONV))) THEN
  REWRITE_TAC[INT_ARITH `x:int = y + --z <=> x + z = y`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN ASM_REWRITE_TAC[UNWIND_THM2] THEN
  ASM_REWRITE_TAC[ODD_ADD; ARITH_ODD; ARITH_EVEN] THEN ASM_REAL_ARITH_TAC);;
```

### Informal statement
For any natural number `n` and real-valued functions `a` and `b` on natural numbers, if `a n` is not equal to 0, `b n` is equal to 0, and the sum of `a i` from `i = 0` to `m` is equal to `b m` for all natural numbers `m`, then there exists an odd natural number `d` such that the variation of `a` from `0` to `n` is equal to the variation of `b` from `0` to `n` plus `d`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: `n = 0`.  Using the assumption that the sum of `a` from `0` to `0` is equal to `b 0` and `b 0 = 0`, and further that `a 0` is not equal to `0`, derive a contradiction.
- Inductive step: Assume the theorem holds for `n`. We need to show it holds for `n+1`. Consider two cases for `n`:
  - Case `n=1`: Let d = 1. Compute `variation (0..n) a` and `variation (0..n) b` for `n = 1` and show that `variation (0..n) a = variation (0..n) b + 1`. This relies on `VARIATION_2` to reduce the variation over two elements and `OPPOSITE_SIGNS` to deal with the different signs.
  - Case `2 <= n`: Show that there exists `p` such that `1 < p <= n` and `a p` is not equal to `0`. Using this `p`, rewrite `variation (0..n) a` as `variation {0, 1, p} a + variation (p..n) a`. Define `a' m = if m = 1 then a 0 + a 1 else a m` and use the inductive hypothesis on `a'` and `b`, where the summation property `sum(0..m) a = b m` holds and the offset `1`. Specifically, show `variation (1..n) a' = variation {1, p} a' + variation (p..n) a` and `variation (0..n) a = variation {0, 1, p} a + variation (p..n) a`, and then use the inductive statement to construct the odd integer `d`. Then consider the case `a 0 + a 1 = 0` and `a 0 + a 1 != 0` to compute `variation (0..n) a - variation (0..n) b = d` where `d` is an odd constant. This part relies on `VARIATION_3` to reduce variation over a set of three elements.

### Mathematical insight
This lemma is a crucial step in a larger proof regarding sign changes and variations of real functions. It establishes a relationship between the variations of two related functions `a` and `b`, where `b` represents the cumulative sum of `a` and `a` is never zero at `n` while `b` is zero at `n`, showing there exists an odd number difference between their variations over the segment `0..n `.

### Dependencies
- `SUM_SING_NUMSEG`
- `VARIATION_2`
- `OPPOSITE_SIGNS`
- `num_CONV`
- `SUM_CLAUSES_NUMSEG`
- `ARITH_RULE`
- `LE_REFL`
- `num_WOP`
- `SUM_CLAUSES_LEFT`
- `LE_0`
- `REAL_ADD_ASSOC`
- `SUM_OFFSET`
- `SUM_EQ_NUMSEG`
- `VARIATION_OFFSET`
- `VARIATION_SPLIT_NUMSEG`
- `IN_NUMSEG`
- `VARIATION_SUBSET`
- `VARIATION_EQ`
- `INSERT_SUBSET`
- `EMPTY_SUBSET`
- `IN_DIFF`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `INT_OF_NUM_EQ`
- `INT_OF_NUM_ADD`
- `INT_ARITH`
- `SUM_CLAUSES_RIGHT`
- `REAL_EQ_ADD_RCANCEL_0`
- `VARIATION_3`
- `UNWIND_THM2`
- `ODD_ADD`
- `ARITH_ODD`
- `ARITH_EVEN`

### Porting notes (optional)
- The multiple uses of `ARITH_TAC` and `ASM_ARITH_TAC` suggest a reliance on the arithmetic decision procedures built into HOL Light.  When porting, ensure the target system has comparable automation for linear arithmetic, particularly related to inequalities over natural numbers.
- The frequent conversions with `NUM_REDUCE_CONV` suggest that simplification of arithmetic expressions is important.
- The heavy manipulation of sets and number segments relies on rewriting theorems involving `IN_NUMSEG`, `IN_INSERT`, etc. Ensure these are ported faithfully and that set-theoretic reasoning is efficient.


---

## VARIATION_OPPOSITE_ENDS

### Name of formal statement
VARIATION_OPPOSITE_ENDS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_OPPOSITE_ENDS = prove
 (`!a m n.
    m <= n /\ ~(a m = &0) /\ ~(a n = &0)
    ==> (ODD(variation(m..n) a) <=> a m * a n < &0)`,
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `n - m:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!i:num. m < i /\ i < n ==> a i = &0` THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `ODD(variation {m,n} a)` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SUBSET THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; IN_NUMSEG; IN_DIFF; EMPTY_SUBSET] THEN
      REWRITE_TAC[LE_REFL; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[VARIATION_2] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[ARITH]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(fun th ->
        MP_TAC(SPECL [`n:num`; `p:num`] th) THEN
        MP_TAC(SPECL [`p:num`; `m:num`] th)) THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN
    REPEAT(ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `ODD(variation(m..p) a + variation(p..n) a)` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN MATCH_MP_TAC VARIATION_SPLIT_NUMSEG THEN
      ASM_SIMP_TAC[LT_IMP_LE; IN_NUMSEG];
      ASM_REWRITE_TAC[ODD_ADD; OPPOSITE_SIGNS] THEN ASM_REAL_ARITH_TAC]]);;
```

### Informal statement
For any function `a` from numbers to real numbers, and any numbers `m` and `n`, if `m` is less than or equal to `n`, `a(m)` is not zero and `a(n)` is not zero, then the variation of `a` on the interval from `m` to `n` is odd if and only if the product of `a(m)` and `a(n)` is less than zero.

### Informal sketch
- The proof proceeds by induction on `n - m`.
- The base case is handled by considering whether `a(i) = 0` for all `i` in the open interval `(m, n)`.
  - If `a(i) = 0` for all `i` in `(m, n)`, then `variation(m..n) a` is equal to `variation {m, n} a`. The `variation` of a two-element set `{m, n}` is 1 if `a m * a n < 0`, and 0 otherwise; this is expressed as `VARIATION_2`. We also use `INSERT_SUBSET`, `IN_NUMSEG`, `IN_DIFF`, `EMPTY_SUBSET`, `LE_REFL`, `IN_INSERT`, `NOT_IN_EMPTY` to simplify the subset calculations.
  - If there exists some `p` such that `m < p < n` and `a(p) != 0`, then we split the interval `(m..n)` into `(m..p)` and `(p..n)`, calculate `variation(m..n) a` as `variation(m..p) a + variation(p..n) a`. We then rewrite the condition `a m * a n < 0` using `ODD_ADD` and `OPPOSITE_SIGNS`, and apply real arithmetic reasoning.
- The inductive step uses `VARIATION_SPLIT_NUMSEG` to split the interval and performs arithmetic reasoning on real numbers using `ASM_REAL_ARITH_TAC`.

### Mathematical insight
The theorem relates the variation of a function on a numerical interval to the signs of its values at the endpoints. Specifically, it states that the variation is odd (i.e., there is an odd number of sign changes) if and only if the function values at the endpoints have opposite signs, given that neither endpoint is zero.

### Dependencies
- `VARIATION_SUBSET`
- `INSERT_SUBSET`
- `IN_NUMSEG`
- `IN_DIFF`
- `EMPTY_SUBSET`
- `LE_REFL`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `VARIATION_2`
- `LT_IMP_LE`
- `VARIATION_SPLIT_NUMSEG`
- `ODD_ADD`
- `OPPOSITE_SIGNS`
- `NOT_FORALL_THM`

### Porting notes (optional)
- The proof relies heavily on rewriting and arithmetic reasoning, which may require corresponding tactics or automation in other proof assistants.
- Handling of number intervals and subsets might differ across systems.


---

## REAL_POLYFUN_SGN_AT_INFINITY

### Name of formal statement
REAL_POLYFUN_SGN_AT_INFINITY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_POLYFUN_SGN_AT_INFINITY = prove
 (`!a n. ~(a n = &0)
         ==> ?B. &0 < B /\
                 !x. B <= abs x
                     ==> real_sgn(sum(0..n) (\i. a i * x pow i)) =
                         real_sgn(a n * x pow n)`,
  let lemma = prove
   (`abs(x) < abs(y) ==> real_sgn(x + y) = real_sgn y`,
    REWRITE_TAC[real_sgn] THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; SUM_SING_NUMSEG];
    ALL_TAC] THEN
  ABBREV_TAC `B = sum (0..n-1) (\i. abs(a i)) / abs(a n)` THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN SIMP_TAC[REAL_LE_DIV; REAL_ABS_POS; SUM_POS_LE_NUMSEG];
    ALL_TAC] THEN
  EXISTS_TAC `&1 + B` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; LE_1] THEN MATCH_MP_TAC lemma THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum(0..n-1) (\i. abs(a i)) * abs x pow (n - 1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_ABS_LE THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS; REAL_ABS_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(x:real) pow n = x * x pow (n - 1)` SUBST1_TAC THENL
     [SIMP_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; GSYM REAL_ABS_NZ] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]]]);;
```

### Informal statement
For all real-valued sequences `a` and natural numbers `n`, if it is not the case that `a i` equals 0 for all `i` from `0` to `n`, then there exists a real number `B` greater than 0 such that for all real numbers `x`, if `B` is less than or equal to the absolute value of `x`, then the sign of the polynomial `sum(0..n) (\i. a i * x pow i)` is equal to the sign of `a n * x pow n`.

### Informal sketch
The theorem states that the sign of a polynomial is determined by the sign of its highest-degree term when the absolute value of the variable is sufficiently large.

*   **Base Case (n=0):** If `n` is 0, it shows that there exists `B=1` satisfying the condition, using the fact that the sum from 0 to 0 is just the single term.
*   **Inductive Step (n > 0):**
    *   Define `B` as the sum of the absolute values of the coefficients from `0` to `n-1` divided by the absolute value of the leading coefficient `a n`. It's proven that `B` must be non-negative.
    *   Show the existence of a suitable `B'`, which is chosen as `1+B`, so `0 < B <= abs x`.
    *   Prove the main implication by showing the absolute value of the lower degree terms is less than the absolute value of the highest degree term, when  `abs x >= B`.  This uses the lemma `abs(x) < abs(y) ==> real_sgn(x + y) = real_sgn y`, which shows in that case `real_sgn(x+y)=real_sgn(y)`.
    *   Relate the absolute value of the sum of the lower-degree terms to `abs(a n) * abs(x pow n)` showing that `abs(sum(0..n-1) (\i. a i * x pow i)) < abs(a n * x pow n)` when `abs x >= B`. This is accomplished by bounding the sum of the absolute values of the lower degree terms with `sum(0..n-1) (abs(a i) * abs(x pow i))` and relating it with `B * abs a n * abs(x pow (n-1))`.
    *   Using the fact that `abs x >= B`, with some algebraic manipulations uses transitivity and division to relate `sum(0..n-1) (abs(a i)) / abs(a n) < abs x` assuming `abs x > 0`.

### Mathematical insight
This result is crucial for analyzing the behavior of polynomials at infinity. It formalizes the intuition that for large enough values of `x`, the highest-degree term dominates the polynomial's value and hence its sign. This is a fundamental property used in real analysis and numerical methods.

### Dependencies
*   `real_sgn`
*   `REAL_LT_01`
*   `SUM_SING_NUMSEG`
*   `REAL_LE_DIV`
*   `REAL_ABS_POS`
*   `SUM_POS_LE_NUMSEG`
*   `SUM_CLAUSES_RIGHT`
*   `LE_0`
*   `LE_1`
*   `SUM_RMUL`
*   `SUM_ABS_LE`
*   `FINITE_NUMSEG`
*   `IN_NUMSEG`
*   `REAL_ABS_MUL`
*   `REAL_LE_LMUL`
*   `REAL_ABS_POW`
*   `REAL_POW_MONO`
*   `CONJUNCT2 real_pow`
*   `REAL_MUL_ASSOC`
*   `REAL_LT_RMUL`
*   `REAL_MUL_SYM`
*   `REAL_LT_LDIV_EQ`
*   `REAL_ABS_NZ`
*   `REAL_POW_LT`

### Porting notes (optional)
*   The proof relies heavily on real arithmetic reasoning, so a proof assistant with strong automation in that area will be helpful.
*   The handling of summation over numerical ranges might require specific tactics or libraries depending on the target proof assistant.
*   The use of `ABBREV_TAC` can easily be translated into local definitions within the proof script in other systems like Lean or Coq.


---

## REAL_POLYFUN_HAS_POSITIVE_ROOT

### Name of formal statement
REAL_POLYFUN_HAS_POSITIVE_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_POLYFUN_HAS_POSITIVE_ROOT = prove
 (`!a n. a 0 < &0 /\ &0 < a n
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x. &0 < x /\ &0 <= sum(0..n) (\i. a i * x pow i)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:num->real`; `n:num`] REAL_POLYFUN_SGN_AT_INFINITY) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `x:real`)) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `real_sgn(a n * x pow n) = &1` SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_SGN_EQ; REAL_LT_MUL; REAL_POW_LT; real_gt] THEN
    REWRITE_TAC[REAL_LT_IMP_LE];
    MP_TAC(ISPECL [`\x. sum(0..n) (\i. a i * x pow i)`;
                   `&0`; `x:real`; `&0`] REAL_IVT_INCREASING) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; IN_REAL_INTERVAL;
                 REAL_POW_ZERO; COND_RAND] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; LE_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real` THEN
      SIMP_TAC[REAL_LT_LE] THEN ASM_CASES_TAC `y:real = &0` THEN
      ASM_SIMP_TAC[REAL_POW_ZERO; COND_RAND; REAL_MUL_RZERO; REAL_MUL_RID] THEN
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN ASM_REAL_ARITH_TAC]]);;
```
### Informal statement
For all real-valued functions `a` from natural numbers to real numbers, and for all natural numbers `n`, if `a 0` is less than 0 and 0 is less than `a n`, then there exists a real number `x` such that 0 is less than `x` and the sum from 0 to `n` of `a i` times `x` to the power of `i` is equal to 0.

### Informal sketch
This theorem proves that a polynomial with real coefficients, where the constant term is negative and the leading coefficient is positive, has a positive real root.

- The proof proceeds by first showing that there exists an `x` greater than 0 such that the polynomial `sum(0..n) (\i. a i * x pow i)` is greater than or equal to 0.
- It uses `REAL_POLYFUN_SGN_AT_INFINITY` to show that for a sufficiently large `x`, the sign of the polynomial is determined by the sign of the leading term `a n * x pow n`. Since `a n` is positive, we can find an `x` such that the polynomial becomes positive, using `REAL_LT_IMP_NZ` and `MONO_EXISTS`.
- Then, by the Intermediate Value Theorem (`REAL_IVT_INCREASING`), since the polynomial is negative at 0 (because a 0 < 0), and positive for some large x, there must exist a value between 0 and x where polynomial is equal to 0.`REAL_IVT_INCREASING` requires us to prove continuity, which is done using `REAL_CONTINUOUS_ON_SUM`, `REAL_CONTINUOUS_ON_LMUL`, and `REAL_CONTINUOUS_ON_POW`.

### Mathematical insight
This theorem is a specific case of the Intermediate Value Theorem applied to polynomials. It guarantees the existence of a positive root when a polynomial transitions from a negative value at 0 to a positive value as x approaches infinity. This result is useful in real analysis and algebraic geometry.

### Dependencies
- `REAL_POLYFUN_SGN_AT_INFINITY`
- `REAL_LT_IMP_NZ`
- `MONO_EXISTS`
- `REAL_IVT_INCREASING`
- `REAL_POW_ZERO`
- `REAL_MUL_RID`
- `REAL_MUL_RZERO`
- `SUM_DELTA`
- `IN_NUMSEG`
- `LE_0`
- `REAL_CONTINUOUS_ON_SUM`
- `FINITE_NUMSEG`
- `REAL_CONTINUOUS_ON_LMUL`
- `REAL_CONTINUOUS_ON_POW`
- `REAL_CONTINUOUS_ON_ID`
- `REAL_LT_LE`

### Porting notes (optional)
The main challenge in porting this theorem is likely to be finding suitable replacements for `REAL_POLYFUN_SGN_AT_INFINITY` and `REAL_IVT_INCREASING`. The tactic `ASM_CASES_TAC` might need translation into a case split. The automation tactics (`ASM_SIMP_TAC`, `ASM_REAL_ARITH_TAC`, etc.) will also need to be adapted to the target proof assistant’s automation capabilities.


---

## ODD_VARIATION_POSITIVE_ROOT

### Name of formal statement
ODD_VARIATION_POSITIVE_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_VARIATION_POSITIVE_ROOT = prove
 (`!a n. ODD(variation(0..n) a)
         ==> ?x. &0 < x /\ sum(0..n) (\i. a i * x pow i) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?M. !i. i IN 0..n /\ ~(a i = &0) ==> i <= M` MP_TAC THENL
   [EXISTS_TAC `n:num` THEN SIMP_TAC[IN_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `?i. i IN 0..n /\ ~(a i = &0)` MP_TAC THENL
   [MATCH_MP_TAC(MESON[] `((!i. P i ==> Q i) ==> F) ==> ?i. P i /\ ~Q i`) THEN
    DISCH_TAC THEN SUBGOAL_THEN `variation (0..n) a = variation {0} a`
     (fun th -> SUBST_ALL_TAC th THEN ASM_MESON_TAC[VARIATION_1; ODD]) THEN
    MATCH_MP_TAC VARIATION_SUBSET THEN
    ASM_SIMP_TAC[IN_DIFF] THEN REWRITE_TAC[IN_NUMSEG; SING_SUBSET; LE_0];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> a ==> a /\ b ==> c`] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN REWRITE_TAC[num_MAX] THEN
  REWRITE_TAC[TAUT `p ==> ~(q /\ r) <=> p /\ q ==> ~r`; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ ~q ==> r <=> p /\ ~r ==> q`] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p:num <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:num->real) p * a q < &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM VARIATION_OPPOSITE_ENDS] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `ODD p ==> p = q ==> ODD q`)) THEN
    MATCH_MP_TAC VARIATION_SUBSET THEN
    REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; IN_DIFF; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC] THEN
    FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i. (a:num->real)(p + i) / a q`; `q - p:num`]
        REAL_POLYFUN_HAS_POSITIVE_ROOT) THEN
  ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `p:num <= q ==> p + q - p = q`] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[real_div; OPPOSITE_SIGNS; REAL_MUL_POS_LT] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPPOSITE_SIGNS]) THEN
    REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`; GSYM REAL_INV_NEG] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_RING
   `!a. y = a * x ==> x = &0 ==> y = &0`) THEN
  EXISTS_TAC `(a:num->real) q * x pow p` THEN
  REWRITE_TAC[GSYM SUM_LMUL; REAL_ARITH
   `(aq * xp) * api / aq * xi:real = (aq / aq) * api * (xp * xi)`] THEN
  ASM_CASES_TAC `(a:num->real) q = &0` THENL
   [ASM_MESON_TAC[REAL_MUL_LZERO; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_ADD; REAL_DIV_REFL; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MP_TAC(SPEC `p:num` SUM_OFFSET) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  MATCH_MP_TAC SUM_SUPERSET THEN
  REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG; IN_DIFF; DE_MORGAN_THM] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; REPEAT STRIP_TAC] THEN
  REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN ASM_ARITH_TAC));;
```

### Informal statement
For all real-valued functions `a` of natural numbers and for all natural numbers `n`, if the variation of `a` over the interval from 0 to `n` is odd, then there exists a real number `x` greater than 0 such that the sum from 0 to `n` of `a` applied to `i` multiplied by `x` raised to the power of `i` is equal to 0.

### Informal sketch
The proof shows that if the variation of the sequence `a` on `0..n` is odd, there exists a positive root for the polynomial whose coefficients are given by the sequence `a`.
- First, it is shown that there exists a natural number `M` such that for all `i` in `0..n` such that `a i` is nonzero, `i <= M`. This is provable because the interval `0..n` contains only elements in the natural numbers and therefore is bounded, and by the well ordering principle of the natural numbers there exists a maximal such `i`.
- Next, it is shown that there exists `i` in `0..n` such that `a i` is non-zero. This uses properties of `variation` such as `VARIATION_1` and `VARIATION_SUBSET`.
- Choose `p` and `q` such that the subsequence `a` restricted to `0..n` changes sign at `p` and `q` and `p < q`.
- Show that `a p * a q < &0`. This uses `VARIATION_OPPOSITE_ENDS` to show that the terms must change sign.
- Show that the polynomial `\i. (a:num->real)(p + i) / a q` applied to `q - p` has a positive root using `REAL_POLYFUN_HAS_POSITIVE_ROOT`.
- Instantiate the existential quantifier and simplify by using the definitions related to sums and demonstrate that they are equal using `SUM_LMUL`, `SUM_OFFSET`, and `SUM_SUPERSET`.

### Mathematical insight
The theorem establishes a connection between the sign variations of a coefficient sequence and the existence of positive roots for the corresponding polynomial. Odd variation implies the polynomial changes sign, suggesting a root exists in the positive real numbers as a consequence of the intermediate value theorem.

### Dependencies
- `VARIATION_1`
- `VARIATION_SUBSET`
- `REAL_POLYFUN_HAS_POSITIVE_ROOT`
- `SUM_LMUL`
- `SUM_OFFSET`
- `SUM_SUPERSET`
- `num_WOP`
- `num_MAX`
- `REAL_RING`

### Porting notes (optional)
- The proof relies heavily on real analysis and polynomial properties. Ensure the target proof assistant has similar theories available.
- The proof uses tactics to manipulate real arithmetic expressions, such as dividing and multiplying. Porting the proof requires similar simplification capabilities.
- The proof also depends on `num_WOP`, the well-ordering principle of the natural numbers. If the target proof assistant has a different axiom, you may have to modify this proof.


---

## multiplicity

### Name of formal statement
multiplicity

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let multiplicity = new_definition
 `multiplicity f r =
        @k. ?a n. ~(sum(0..n) (\i. a i * r pow i) = &0) /\
                  !x. f(x) = (x - r) pow k * sum(0..n) (\i. a i * x pow i)`;;
```
### Informal statement
The multiplicity of a root `r` of a function `f` is defined to be the number `k` such that there exists a polynomial `sum(0..n) (\i. a i * x pow i)` with the property that `sum(0..n) (\i. a i * r pow i)` is not equal to zero and for all `x`, `f(x)` equals `(x - r)` raised to the power of `k` multiplied by `sum(0..n) (\i. a i * x pow i)`.

### Informal sketch
- The definition introduces the concept of the multiplicity of a root `r` of a function `f`.
- It asserts the existence of a natural number `k` that represents the multiplicity.
- It also asserts the existence of a polynomial `sum(0..n) (\i. a i * x pow i)` such that when evaluated at the root `r`, `sum(0..n) (\i. a i * r pow i)` is non-zero, and `f(x)` can be expressed as `(x - r)` raised to the power `k` multiplied by this polynomial, for every `x`.
- The definition relies on the existence of appropriate coefficients `a : num -> real` and `n : num` to define the polynomial.

### Mathematical insight
This definition formalizes the notion of the multiplicity of a root of a function, typically a polynomial. The multiplicity indicates how many times a particular root appears as a factor of the polynomial. The key idea is that `f(x)` should be divisible by `(x - r)^k` but not by `(x - r)^(k+1)`, which is implicitly ensured by requiring that the polynomial `sum(0..n) (\i. a i * x pow i)` does not vanish at `r`.

### Dependencies
- `sum`
- `pow`


---

## MULTIPLICITY_UNIQUE

### Name of formal statement
MULTIPLICITY_UNIQUE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULTIPLICITY_UNIQUE = prove
 (`!f a r b m k.
        (!x. f(x) = (x - r) pow k * sum(0..m) (\j. b j * x pow j)) /\
        ~(sum(0..m) (\j. b j * r pow j) = &0)
        ==> k = multiplicity f r`,
  let lemma = prove
   (`!i j f g. f real_continuous_on (:real) /\ g real_continuous_on (:real) /\
               ~(f r = &0) /\ ~(g r = &0)
               ==> (!x. (x - r) pow i * f(x) = (x - r) pow j * g(x))
                   ==> j = i`,
    MATCH_MP_TAC WLOG_LT THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPECL [`atreal r`; `f:real->real`;
                   `(f:real->real) r`; `&0`]
          REALLIM_UNIQUE) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_ATREAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
      ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV;
                    IN_UNIV];
      MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
      EXISTS_TAC `\x:real. (x - r) pow (j - i) * g x` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01; REAL_ARITH `&0 < abs(x - r) <=> ~(x = r)`] THEN
        X_GEN_TAC `x:real` THEN STRIP_TAC THEN MATCH_MP_TAC(REAL_RING
         `!a. a * x = a * y /\ ~(a = &0) ==> x = y`) THEN
        EXISTS_TAC `(x - r:real) pow i` THEN
        ASM_REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_ADD; REAL_POW_EQ_0] THEN
        ASM_SIMP_TAC[REAL_SUB_0; ARITH_RULE `i:num < j ==> i + j - i = j`];
        SUBST1_TAC(REAL_ARITH `&0 = &0 * (g:real->real) r`) THEN
        MATCH_MP_TAC REALLIM_MUL THEN CONJ_TAC THENL
         [REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_NULL_POW THEN
          REWRITE_TAC[GSYM REALLIM_NULL; REALLIM_ATREAL_ID] THEN ASM_ARITH_TAC;
          REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
          ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT;
                        REAL_OPEN_UNIV; IN_UNIV]]]]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[multiplicity] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `j:num` THEN EQ_TAC THEN ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`b:num->real`; `m:num`] THEN ASM_REWRITE_TAC[]]);;
```

### Informal statement
For any function `f` from reals to reals, any real number `a`, any real numbers `r` and `b`, any natural numbers `m` and `k`, if it is the case that (for all `x`, `f(x)` equals `(x - r)` raised to the power of `k` times the sum from 0 to `m` of (function applied as follows: for all `j`, `b j * x` raised to the power of `j`)), and it is not the case that (the sum from 0 to `m` of (function applied as follows: for all `j`, `b j * r` raised to the power of `j`) equals 0), then `k` is equal to the `multiplicity` of `f` at `r`.

### Informal sketch
The proof proceeds as follows:
- It starts with a lemma which states that if two real functions `f` and `g` are continuous on the real numbers, and neither `f(r)` nor `g(r)` is zero, then if `(x - r)^i * f(x) = (x - r)^j * g(x)` for all `x`, it follows that `j = i`. This lemma is proved by assuming `i < j`, and then using the uniqueness of limits to show that `i` must be equal to `j`. The proof involves manipulating the equation `(x - r)^i * f(x) = (x - r)^j * g(x)` and taking limits as `x` approaches `r`.
- The theorem itself starts by rewriting with definition of `multiplicity` and then uses `SELECT_UNIQUE`.
- The goal is to show `k = j` by showing that there exists a unique `j` satisfying the uniqueness condition. It then applies the lemma to show that indeed `k = j`.
- To apply the lemma, the proof shows the required continuity properties by using the continuity of sums, LMult, powers, and the identity function.

### Mathematical insight
The theorem `MULTIPLICITY_UNIQUE` establishes a crucial property of the `multiplicity` function, namely, that the `multiplicity` is uniquely determined by the given condition. This is important because it ensures that the `multiplicity` is a well-defined and consistent notion. The condition ensures that the function `f(x)` can be represented as `(x - r)^k` multiplied by a power series in `x`, where the power series does not evaluate to zero at `r`.

### Dependencies
- `multiplicity`
- `REAL_CONTINUOUS_ON_SUM`
- `REAL_CONTINUOUS_ON_LMUL`
- `REAL_CONTINUOUS_ON_POW`
- `REAL_CONTINUOUS_ON_ID`
- `REALLIM_UNIQUE`
- `TRIVIAL_LIMIT_ATREAL`
- `REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT`
- `REAL_OPEN_UNIV`
- `IN_UNIV`
- `REALLIM_TRANSFORM_EVENTUALLY`
- `EVENTUALLY_ATREAL`
- `REAL_LT_01`
- `REAL_ARITH`
- `REAL_MUL_ASSOC`
- `REAL_POW_ADD`
- `REAL_POW_EQ_0`
- `REAL_SUB_0`
- `REALLIM_MUL`
- `REALLIM_NULL_POW`
- `REALLIM_NULL`
- `REALLIM_ATREAL_ID`
- `FINITE_NUMSEG`
- `IN_NUMSEG`
- `LEFT_IMP_EXISTS_THM`


---

## MULTIPLICITY_WORKS

### Name of formal statement
MULTIPLICITY_WORKS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULTIPLICITY_WORKS = prove
 (`!r n a.
    (?i. i IN 0..n /\ ~(a i = &0))
    ==> ?b m.
        ~(sum(0..m) (\i. b i * r pow i) = &0) /\
        !x. sum(0..n) (\i. a i * x pow i) =
            (x - r) pow multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r *
            sum(0..m) (\i. b i * x pow i)`,
  REWRITE_TAC[multiplicity] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
  ASM_CASES_TAC `(a:num->real) n = &0` THENL
   [ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2]
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `a:num->real`) THEN
    ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; LE_1] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` MP_TAC) THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `i:num = n` THENL [ASM_MESON_TAC[]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `sum(0..n) (\i. a i * r pow i) = &0` THENL
   [ASM_CASES_TAC `n = 0` THENL
     [UNDISCH_TAC `sum (0..n) (\i. a i * r pow i) = &0` THEN
      ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2; SUM_SING] THEN
      REWRITE_TAC[real_pow; REAL_MUL_RID] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(GEN `x:real` (ISPECL [`a:num->real`; `x:real`; `r:real`; `n:num`]
        REAL_SUB_POLYFUN)) THEN ASM_SIMP_TAC[LE_1; REAL_SUB_RZERO] THEN
    ABBREV_TAC `b j = sum (j + 1..n) (\i. a i * r pow (i - j - 1))` THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `b:num->real`) THEN ANTS_TAC THENL
     [EXISTS_TAC `n - 1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL; LE_0] THEN
      EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[SUB_ADD; LE_1; SUM_SING_NUMSEG; real_pow; REAL_MUL_RID;
                   ARITH_RULE `n - (n - 1) - 1 = 0`];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (fun th ->
        EXISTS_TAC `SUC k` THEN MP_TAC th)) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC];
    MAP_EVERY EXISTS_TAC [`0`; `a:num->real`; `n:num`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID]]);;
```

### Informal statement
For any real number `r`, natural number `n`, and function `a` from natural numbers to real numbers, if there exists a natural number `i` in the range 0 to `n` such that `a i` is not equal to 0, then there exist a function `b` from natural numbers to real numbers, and a natural number `m`, such that the sum from 0 to `m` of `b i * r pow i` (where `r pow i` means `r` raised to the power `i`) is not equal to 0, and for all `x`, the sum from 0 to `n` of `a i * x pow i` is equal to `(x - r)` raised to the power of the multiplicity of the function that maps `x` to the sum from 0 to `n` of `a i * x pow i`, evaluated at `r`, multiplied by the sum from 0 to `m` of `b i * x pow i`.

### Informal sketch
The proof proceeds by induction on `n`. The base case `n = 0` is handled by cases on whether `a n = 0`. The cases where `sum(0..n) (\i. a i * r pow i) = 0` are also considered, involving several case splits and simplifications. The theorem `REAL_SUB_POLYFUN` is applied in one of these cases. An abbreviation `b j = sum (j + 1..n) (\i. a i * r pow (i - j - 1))` is introduced. Existential quantifiers are handled and the goal is simplified using arithmetic rules, properties of summation, and properties of real powers and multiplication.

- Induction on `n`.
- Case splits on `a n = 0` and `n = 0`.
- Assume `sum(0..n) (\i. a i * r pow i) = &0` and split on `n = 0`
- Apply `REAL_SUB_POLYFUN` and introduce abbreviation `b j = sum (j + 1..n) (\i. a i * r pow (i - j - 1))`
- Handle quantifiers and simplify using arithmetic and real number properties

### Mathematical insight
This theorem states that if a polynomial defined by coefficients `a` has a root `r` with some multiplicity, then we can factor out `(x - r)` raised to that multiplicity from the polynomial, and the remaining polynomial (defined by `b`) does not evaluate to zero when `x = r`. The initial condition `(?i. i IN 0..n /\ ~(a i = &0))` ensures that the polynomial defined by the coefficients `a` is not identically zero.

### Dependencies
- `multiplicity`
- `NUMSEG_SING`
- `IN_SING`
- `UNWIND_THM2`
- `num_WF`
- `SUM_CLAUSES_RIGHT`
- `LE_0`
- `LE_1`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`
- `IN_NUMSEG`
- `SUM_SING`
- `real_pow`
- `REAL_MUL_RID`
- `REAL_SUB_POLYFUN`
- `SUB_ADD`
- `SUM_SING_NUMSEG`
- `GSYM FUN_EQ_THM`
- `LE_REFL`
- `GSYM REAL_MUL_ASSOC`
- `REAL_MUL_LID`
- `MONO_EXISTS`


---

## MULTIPLICITY_OTHER_ROOT

### Name of formal statement
MULTIPLICITY_OTHER_ROOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MULTIPLICITY_OTHER_ROOT = prove
 (`!a n r s.
    ~(r = s) /\ (?i. i IN 0..n /\ ~(a i = &0))
     ==> multiplicity (\x. (x - r) pow m * sum(0..n) (\i. a i * x pow i)) s =
         multiplicity (\x.  sum(0..n) (\i. a i * x pow i)) s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real`; `n:num`; `a:num->real`]
        MULTIPLICITY_WORKS) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`; `p:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN
   `?b q. !x. sum(0..q) (\j. b j * x pow j) =
              (x - r) pow m * sum (0..p) (\i. c i * x pow i)`
  MP_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[REAL_RING `r * x = s * r * y <=> r = &0 \/ s * y = x`] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0]] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`c:num->real`; `p:num`; `m:num`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [MAP_EVERY EXISTS_TAC [`c:num->real`; `p:num`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `c:num->real`]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `n:num`] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  EXISTS_TAC `\i. (if 0 < i then a(i - 1) else &0) -
                  (if i <= n then r * a i else &0)` THEN
  EXISTS_TAC `n + 1` THEN
  REWRITE_TAC[REAL_SUB_RDISTRIB; SUM_SUB_NUMSEG] THEN X_GEN_TAC `x:real` THEN
  BINOP_TAC THENL
   [MP_TAC(ARITH_RULE `0 <= n + 1`) THEN SIMP_TAC[SUM_CLAUSES_LEFT] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[SUM_OFFSET; LT_REFL] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; ARITH_RULE `0 < i + 1`] THEN
    REWRITE_TAC[GSYM SUM_LMUL; ADD_SUB; REAL_POW_ADD; REAL_POW_1];
    SIMP_TAC[SUM_CLAUSES_RIGHT; LE_0; ARITH_RULE `0 < n + 1`] THEN
    REWRITE_TAC[ADD_SUB; ARITH_RULE `~(n + 1 <= n)`] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_RID; GSYM SUM_LMUL]] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
For all real numbers `a`, natural numbers `n`, and real numbers `r` and `s`, if `r` is not equal to `s` and there exists a natural number `i` in the range `0` to `n` such that `a i` is not equal to `0`, then the multiplicity of `s` as a root of the polynomial `(x - r)^m * sum(0..n) (\i. a i * x^i)` is equal to the multiplicity of `s` as a root of the polynomial `sum(0..n) (\i. a i * x^i)`.

### Informal sketch
The proof proceeds as follows:
- Assume `r` is not equal to `s` and there exists `i` in `0..n` such that `a i` is not zero.
- Apply `MULTIPLICITY_UNIQUE` to show that the multiplicities of `s` as roots of the polynomials `(x - r)^m` and `sum(0..n) (\i. a i * x^i)` are independent.
- Use `MULTIPLICITY_WORKS` to assert that if `s` is not a root of `(x - r)^m`, then the multiplicity of `s` as a root of `(x - r)^m * sum(0..n) (\i. a i * x^i)` is equal to the multiplicity of `s` as a root of `sum(0..n) (\i. a i * x^i)`.
- Show that `s` is not a root of `(x - r)^m` because `s` is not equal to `r`.
- Use polynomial induction to prove a lemma about polynomial factorization of the form `?b q. !x. sum(0..q) (\j. b j * x pow j) = (x - r) pow m * sum (0..p) (\i. c i * x pow i)`.

### Mathematical insight
This theorem states that if `r` and `s` are distinct, then the multiplicity of `s` as a root of the product of `(x - r)^m` and a polynomial `p(x)` is the same as the multiplicity of `s` as a root of `p(x)`. This is because `(x - r)^m` does not contribute any factor of `(x - s)` when `r` and `s` are distinct.  The condition that at least one coefficient `a i` is nonzero ensures that we are dealing with a non-zero polynomial.

### Dependencies
- Theorems: `MULTIPLICITY_UNIQUE`, `MULTIPLICITY_WORKS`, `LEFT_IMP_EXISTS_THM`, `REAL_RING r * x = s * r * y <=> r = &0 \/ s * y = x`, `REAL_ENTIRE`, `REAL_POW_EQ_0`, `REAL_SUB_0`, `real_pow`, `REAL_MUL_LID`, `GSYM REAL_MUL_ASSOC`, `REAL_SUB_RDISTRIB`, `SUM_SUB_NUMSEG`, `SUM_CLAUSES_LEFT`, `SUM_OFFSET`, `LT_REFL`, `REAL_MUL_LZERO`, `REAL_ADD_LID`, `ARITH_RULE 0 < i + 1`, `GSYM SUM_LMUL`, `ADD_SUB`, `REAL_POW_ADD`, `REAL_POW_1`, `SUM_CLAUSES_RIGHT`, `LE_0`, `ARITH_RULE 0 < n + 1`, `ARITH_RULE ~(n + 1 <= n)`, `REAL_ADD_RID`, `SUM_EQ_NUMSEG`, `REAL_MUL_AC`


---

## VARIATION_POSITIVE_ROOT_FACTOR

### Name of formal statement
VARIATION_POSITIVE_ROOT_FACTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_POSITIVE_ROOT_FACTOR = prove
 (`!a n r.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b. ~(b(n - 1) = &0) /\
            (!x. sum(0..n) (\i. a i * x pow i) =
                 (x - r) * sum(0..n-1) (\i. b i * x pow i)) /\
            ?d. ODD d /\ variation(0..n) a = variation(0..n-1) b + d`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; real_pow; REAL_MUL_RID] THEN MESON_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `b = \j. sum (j + 1..n) (\i. a i * r pow (i - j - 1))` THEN
  EXISTS_TAC `b:num->real` THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[SUM_SING_NUMSEG; ARITH_RULE `n - (n - 1) - 1 = 0`] THEN
    ASM_REWRITE_TAC[real_pow; REAL_MUL_RID];
    MP_TAC(GEN `x:real` (SPECL [`a:num->real`; `x:real`; `r:real`; `n:num`]
        REAL_SUB_POLYFUN)) THEN
    ASM_SIMP_TAC[LE_1; REAL_SUB_RZERO] THEN DISCH_THEN(K ALL_TAC) THEN
    EXPAND_TAC "b" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:num->real) n = &0` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`n:num`; `\i. if i <= n then a i * (r:real) pow i else &0`;
    `\i. if i <= n then --b i * (r:real) pow (i + 1) else &0`]
   ARTHAN_LEMMA) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_LT_IMP_NZ; REAL_NEG_0;
               LE_REFL] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN EXPAND_TAC "b" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `j:num <= n` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `!i:num. i <= j ==> i <= n` MP_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
      REWRITE_TAC[REAL_ARITH `a:real = --b * c <=> a + b * c = &0`] THEN
      REWRITE_TAC[GSYM SUM_RMUL; GSYM REAL_POW_ADD; GSYM REAL_MUL_ASSOC] THEN
      SIMP_TAC[ARITH_RULE `j + 1 <= k ==> k - j - 1 + j + 1 = k`] THEN
      ASM_SIMP_TAC[SUM_COMBINE_R; LE_0];
      REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
      ASM_SIMP_TAC[ARITH_RULE
      `~(j <= n) ==> ((0 <= i /\ i <= j) /\ i <= n <=> 0 <= i /\ i <= n)`] THEN
      ASM_REWRITE_TAC[GSYM numseg]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC(ARITH_RULE
     `x':num = x /\ y' = y ==> x' = y' + d ==> x = y + d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n) (\i. a i * r pow i)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC[IN_NUMSEG];
        ALL_TAC];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n) (\i. --b i * r pow (i + 1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_EQ THEN SIMP_TAC[IN_NUMSEG];
        ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `variation(0..n-1) (\i. --b i * r pow (i + 1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VARIATION_SUBSET THEN
        REWRITE_TAC[SUBSET_NUMSEG; IN_DIFF; IN_NUMSEG] THEN
        CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `i:num` THEN STRIP_TAC] THEN
        SUBGOAL_THEN `i:num = n` SUBST_ALL_TAC THENL
         [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
        ALL_TAC]] THEN
    REWRITE_TAC[variation] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
      `(a * x) * (b * x'):real = (x * x') * a * b`] THEN
    SIMP_TAC[NOT_IMP; GSYM CONJ_ASSOC; GSYM REAL_POW_ADD;
             REAL_ARITH `--x * --y:real = x * y`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x * y < &0 <=> &0 < x * --y`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_POW_LT] THEN
    ASM_SIMP_TAC[REAL_MUL_RNEG; REAL_ENTIRE; REAL_NEG_EQ_0; REAL_POW_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ]]);;
```
### Informal statement
For any function `a` from natural numbers to real numbers, any natural number `n`, and any real number `r`, if `a n` is not equal to 0, `r` is greater than 0, and the sum from 0 to `n` of `a i` times `r` to the power of `i` is equal to 0, then there exists a function `b` from natural numbers to real numbers such that `b (n - 1)` is not equal to 0, for all real numbers `x`, the sum from 0 to `n` of `a i` times `x` to the power of `i` is equal to `(x - r)` times the sum from 0 to `n-1` of `b i` times `x` to the power of `i`, and there exists a natural number `d` such that `d` is odd, and the variation of the sequence `a` from 0 to `n` is equal to the variation of the sequence `b` from 0 to `n-1` plus `d`.

### Informal sketch
The theorem states that if a polynomial, represented by coefficients `a`, has a positive root `r`, then we can factor out `(x - r)` and obtain a new polynomial with coefficients `b`. Furthermore, the variation in sign of the original sequence `a` is related to the variation in sign of the new sequence `b` by an odd number `d`.

- The proof proceeds by induction on `n`.
- The base case `n = 0` is handled directly using simplification and the `MESON_TAC`.
- In the inductive step, a function `b` is defined as `b(j) = sum (j + 1..n) (\i. a i * r pow (i - j - 1))`.
- It must be shown that the newly defined `b` satisfies the existential quantifier.
- The proof involves showing that `b(n-1)` is not zero and that the polynomial factorization holds.
- The identity `sum(0..n) (\i. a i * x pow i) = (x - r) * sum(0..n-1) (\i. b i * x pow i)` is proven using the lemma `REAL_SUB_POLYFUN`.
- Subsequently, it is shown that there exists an odd number `d` such that the difference between the `variation` of the sequence `a` from 0 to `n` and the `variation` of the sequence `b` from 0 to `n-1` is the odd number `d`. This part involves some simplification with `variation`, `REAL_POW_ADD`, and reasoning using the properties of the `variation` function based on the signs of consecutive terms, and simplification of sums.

### Mathematical insight
This theorem is a step in proving Descartes' Rule of Signs, which relates the number of positive real roots of a polynomial to the number of sign changes in its coefficients. Factoring out a positive root `r` reduces the degree of the polynomial and affects the number of sign changes in a predictable way. `variation` measures the number of sign changes in a sequence, so this is a necessary ingredient towards a proof of Descartes' Rule.

### Dependencies
- `SUM_CLAUSES_NUMSEG`
- `real_pow`
- `REAL_MUL_RID`
- `SUB_ADD`
- `LE_1`
- `SUM_SING_NUMSEG`
- `ARITH_RULE`
- `REAL_SUB_POLYFUN`
- `REAL_SUB_RZERO`
- `SUM_EQ_0_NUMSEG`
- `ARTHAN_LEMMA`
- `REAL_ENTIRE`
- `REAL_POW_EQ_0`
- `REAL_LT_IMP_NZ`
- `REAL_NEG_0`
- `LE_REFL`
- `IN_NUMSEG`
- `GSYM`
- `REAL_POW_ADD`
- `REAL_MUL_ASSOC`
- `SUM_COMBINE_R`
- `LE_0`
- `SUM_RESTRICT_SET`
- `numseg`
- `MONO_EXISTS`
- `MONO_AND`
- `EQ_TRANS`
- `VARIATION_EQ`
- `VARIATION_SUBSET`
- `SUBSET_NUMSEG`
- `IN_DIFF`
- `variation`
- `CONJ_ASSOC`
- `REAL_LT_MUL_EQ`
- `REAL_POW_LT`
- `REAL_MUL_RNEG`
- `REAL_NEG_EQ_0`

### Porting notes (optional)
- The `ARTHAN_LEMMA` is non-trivial and may require some effort to find or reprove in other systems. The lemma likely states properties about sum of sequences of real numbers under certain conditions.
- The frequent use of `ARITH_TAC` indicates a reliance on an arithmetic decision procedure, which may need to be replicated or matched in the target system.
- The handling of sums over natural number ranges (`0..n`) may differ in other proof assistants; ensure that the equivalent notation is used.


---

## VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR

### Name of formal statement
VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR = prove
 (`!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b k m. 0 < k /\ m < n /\ ~(b m = &0) /\
                (!x. sum(0..n) (\i. a i * x pow i) =
                     (x - r) pow k * sum(0..m) (\i. b i * x pow i)) /\
                ~(sum(0..m) (\j. b j * r pow j) = &0) /\
                ?d. EVEN d /\ variation(0..n) a = variation(0..m) b + k + d`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `a:num->real` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; real_pow; REAL_MUL_RID] THEN MESON_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`a:num->real`; `n:num`; `r:real`]
        VARIATION_POSITIVE_ROOT_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `c:num->real` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `sum(0..n-1) (\i. c i * r pow i) = &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `c:num->real`)] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real` THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_ASSOC] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[ADD1; ADD_ASSOC] THEN EXISTS_TAC `d - 1 + e`;
    MAP_EVERY EXISTS_TAC [`c:num->real`; `1`; `n - 1`] THEN
    ASM_REWRITE_TAC[REAL_POW_1] THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    EXISTS_TAC `d - 1`] THEN
  UNDISCH_TAC `ODD d` THEN GEN_REWRITE_TAC LAND_CONV [ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[SUC_SUB1; EVEN_ADD; EVEN_MULT; ARITH] THEN ARITH_TAC);;
```

### Informal statement
For all real numbers `r`, natural numbers `n`, and functions `a` from natural numbers to real numbers, if `a(n)` is not equal to 0, `0 < r`, and the sum from `i = 0` to `n` of `a(i) * r^i` is equal to 0, then there exist a function `b` from natural numbers to real numbers, natural numbers `k` and `m` such that `0 < k`, `m < n`, `b(m)` is not equal to 0, for all `x`, the sum from `i = 0` to `n` of `a(i) * x^i` equals `(x - r)^k` times the sum from `i = 0` to `m` of `b(i) * x^i`, the sum from `j = 0` to `m` of `b(j) * r^j` is not equal to 0, and there exists a natural number `d` such that `d` is even and the variation of `a` from `0` to `n` equals the variation of `b` from `0` to `m` plus `k` plus `d`.

### Informal sketch
The proof proceeds by induction on `n`.

- **Base Case:** When `n = 0`, the antecedent `sum(0..n) (\i. a i * r pow i) = &0` simplifies to `a 0 = &0`, which contradicts `~(a n = &0)`.
- **Inductive Step:** Assume the theorem holds for `n`.
  - Apply the theorem `VARIATION_POSITIVE_ROOT_FACTOR` to obtain a function `c` and a natural number `d` such that the polynomial `sum(0..n) (\i. a i * x pow i)` can be factored as `(x - r) * sum(0..n-1) (\i. c i * x pow i)`, the variation of `a` from `0` to `n` is equal to the variation of `c` from `0` to `n-1` plus 1 plus `d`, and `d` is odd.
  - Consider two cases:
    - `sum(0..n-1) (\i. c i * r pow i) = &0`: Apply the inductive hypothesis to the polynomial with coefficients `c` from `0` to `n-1` to obtain a function `b` and natural numbers `k` and `m` such that `sum(0..n-1) (\i. c i * x pow i)` factors as `(x - r)^k * sum(0..m) (\i. b i * x pow i)`. The goal polynomial `sum(0..n) (\i. a i * x pow i)` then factors as `(x - r)^(k+1) * sum(0..m) (\i. b i * x pow i)`. We need to appropriately adjust the even number `d` in the inductive hypothesis.
    - `sum(0..n-1) (\i. c i * r pow i) <> &0`: Then we can directly construct the polynomial coefficient `b = c`, `k = 1` and use the factored form given by `VARIATION_POSITIVE_ROOT_FACTOR`. The even adjustment factor comes directly from `VARIATION_POSITIVE_ROOT_FACTOR`.
  - Since `d` is odd, write it as `2 * p + 1`. Simplify using arithmetic.

### Mathematical insight
This theorem is a refinement of the relationship between roots of a polynomial and the variation in sign of its coefficients. It states that if a polynomial evaluates to zero at a positive value `r`, it can be factored by `(x - r)^k`, where `k` is a positive integer. Moreover, there is a connection between `k`, the difference in variation between coefficients of original polynomial and the new polynomial and `d` which is a multiple of `2`.

### Dependencies
- `SUM_CLAUSES_NUMSEG`
- `real_pow`
- `REAL_MUL_RID`
- `VARIATION_POSITIVE_ROOT_FACTOR`
- `MONO_EXISTS`
- `SWAP_EXISTS_THM`
- `REAL_POW_1`
- `ADD1`
- `ADD_ASSOC`
- `ODD_EXISTS`
- `SUC_SUB1`
- `EVEN_ADD`
- `EVEN_MULT`

### Porting notes (optional)
- The proof relies heavily on rewriting and arithmetic simplification, so a proof assistant with good automation for these tasks would be beneficial.
- The use of `X_CHOOSE_THEN` and `X_GEN_TAC` suggests a need for mechanisms to introduce and manage existential variables.


---

## VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR

### Name of formal statement
VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR = prove
 (`!r n a.
    ~(a n = &0) /\ &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0
    ==> ?b m. m < n /\ ~(b m = &0) /\
              (!x. sum(0..n) (\i. a i * x pow i) =
                   (x - r) pow
                   (multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r) *
                   sum(0..m) (\i. b i * x pow i)) /\
              ~(sum(0..m) (\j. b j * r pow j) = &0) /\
              ?d. EVEN d /\
                  variation(0..n) a = variation(0..m) b +
                     multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r + d`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:num->real` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r = k`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`b:num->real`; `m:num`] THEN ASM_REWRITE_TAC[]);;
```
### Informal statement
For all real numbers `r`, natural numbers `n`, and functions `a` from natural numbers to real numbers, if it is not the case that `a n` equals 0, and `0 < r`, and the sum from 0 to `n` of `a i * r` raised to the power of `i` is equal to 0, then there exist a function `b` from natural numbers to real numbers and a natural number `m` such that `m < n`, it is not the case that `b m` equals 0, and for all `x`, the sum from 0 to `n` of `a i * x` raised to the power of `i` is equal to `(x - r)` raised to the power of the multiplicity of the function that maps `x` to the sum from 0 to `n` of `a i * x` raised to the power of `i` at `r`, multiplied by the sum from 0 to `m` of `b i * x` raised to the power of `i`, and it is not the case that the sum from 0 to `m` of `b j * r` raised to the power of `j` equals 0, and there exists a natural number `d` such that `d` is even, and the variation of `a` from 0 to `n` is equal to the variation of `b` from 0 to `m` plus the multiplicity of the function that maps `x` to the sum from 0 to `n` of `a i * x` raised to the power of `i` at `r` plus `d`.

### Informal sketch
The theorem states that when a polynomial $\sum_{i=0}^n a_i x^i$ evaluates to 0 at a positive real root `r`, and $a_n \neq 0$, then we can factor out $(x-r)^k$, where `k` is the multiplicity of the root `r`. After factoring, the new polynomial $\sum_{i=0}^m b_i x^i$ also does not evaluate to 0 at `r`, $b_m \neq 0$, and the variation in sign of the coefficients has changed by $k+d$, where `d` is an even number.

- The proof starts by assuming the antecedent of the implication.
- It uses `VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR` to get the polynomial after factoring out `(x-r)^k`.
- It introduces `b` and `m` using existential introduction, relying on the previous result.
- It rewrites based on the assumption `multiplicity (\x. sum(0..n) (\i. a i * x pow i)) r = k`, which is then proved by `MULTIPLICITY_UNIQUE`.
- Finally, more existential introductions are performed for `b` and `m`, and the goal is rewritten using assumptions.

### Mathematical insight
This theorem relates a positive real root of a polynomial to the multiplicity of the root and variation. It's related to Descartes' rule of signs, which bounds the number of positive real roots of a polynomial by the number of sign changes in its coefficients. This result shows how the variation changes upon factoring out a root.

### Dependencies
- `VARIATION_POSITIVE_ROOT_MULTIPLE_FACTOR`
- `MONO_EXISTS`
- `MULTIPLICITY_UNIQUE`


---

## DESCARTES_RULE_OF_SIGNS

### Name of formal statement
DESCARTES_RULE_OF_SIGNS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DESCARTES_RULE_OF_SIGNS = prove
 (`!f a n. f = (\x. sum(0..n) (\i. a i * x pow i)) /\
           (?i. i IN 0..n /\ ~(a i = &0))
           ==> ?d. EVEN d /\
                   variation(0..n) a =
                   nsum {r | &0 < r /\ f(r) = &0} (\r. multiplicity f r) + d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`a:num->real`; `n:num`] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `a:num->real` THEN ASM_CASES_TAC `(a:num->real) n = &0` THENL
   [ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[NUMSEG_SING; IN_SING; UNWIND_THM2]
    THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN(MP_TAC o SPEC `a:num->real`)] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[IN_NUMSEG; ARITH_RULE `i <= n ==> i <= n - 1 \/ i = n`];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
      ASM_SIMP_TAC[LE_0; LE_1; SUM_CLAUSES_RIGHT] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
      MATCH_MP_TAC VARIATION_SUBSET THEN
      REWRITE_TAC[SUBSET_NUMSEG; IN_DIFF; IN_NUMSEG] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; X_GEN_TAC `i:num` THEN STRIP_TAC] THEN
      SUBGOAL_THEN `i:num = n` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    DISCH_THEN(K ALL_TAC)] THEN
  ASM_CASES_TAC `{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} = {}` THENL
   [ASM_REWRITE_TAC[NSUM_CLAUSES; ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM1] THEN
    ONCE_REWRITE_TAC[GSYM NOT_ODD] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ODD_VARIATION_POSITIVE_ROOT) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real`; `n:num`; `a:num->real`]
    VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:num->real`; `m:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `b:num->real`) THEN ANTS_TAC THENL
   [EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL; LE_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d2:num`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC `d1 + d2:num` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[EVEN_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE
   `x + y = z ==> (x + d1) + (y + d2):num = z + d1 + d2`) THEN
  SUBGOAL_THEN
   `{r | &0 < r /\ sum(0..n) (\i. a i * r pow i) = &0} =
    r INSERT {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `x IN s /\ s DELETE x = t ==> s = x INSERT t`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_SUB_0] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE] THEN
      X_GEN_TAC `s:real` THEN
      FIRST_X_ASSUM(K ALL_TAC o SPEC_VAR) THEN
      ASM_CASES_TAC `s:real = r` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {r | &0 < r /\ sum(0..m) (\i. b i * r pow i) = &0}`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r | sum(0..m) (\i. b i * r pow i) = &0}` THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_POLYFUN_FINITE_ROOTS] THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL];
    SIMP_TAC[NSUM_CLAUSES; IN_ELIM_THM] THEN DISCH_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ARITH_RULE `s1:num = s2 ==> s1 + m = m + s2`) THEN
  MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `s:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun t -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [t]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MULTIPLICITY_OTHER_ROOT THEN
  REWRITE_TAC[MESON[] `(?i. P i /\ Q i) <=> ~(!i. P i ==> ~Q i)`] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~(sum (0..m) (\j. b j * r pow j) = &0)` THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LZERO; SUM_0]);;
```

### Informal statement
For all functions `f` from real numbers to real numbers, all functions `a` from natural numbers to real numbers, and all natural numbers `n`, if `f` is equal to the function that maps `x` to the sum from `0` to `n` of `a(i) * x^i`, and there exists an `i` in the natural number range `0` to `n` such that `a(i)` is not equal to `0`, then there exists a natural number `d` such that `d` is even and the variation of the sequence `a` from `0` to `n` is equal to the sum over the set of positive real numbers `r` where `f(r) = 0` of the multiplicity of `r` as a root of `f`, plus `d`.

### Informal sketch
The proof proceeds by:
- Induction on `n`.
- Case splitting on `a(n) = 0`.
- Further case splitting on `n = 0` when `a(n) = 0`.
- In the case where `a(n)` is not zero, case splitting on whether the set of positive roots of `f` is empty.
- Application of `ODD_VARIATION_POSITIVE_ROOT` in the case when the set of positive roots is empty, using lemmas about sums and parities of numbers.
- In the case where positive roots exist, choose such a root `r` and apply the theorem `VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR` to factor out `x - r` from the polynomial `f`.
- Induction hypothesis is then applied to the quotient polynomial, and the result is obtained by combining the induction hypothesis with the properties of multiplicities and variations.

### Mathematical insight
Descartes' Rule of Signs relates the number of sign changes in the coefficients of a polynomial (the `variation`) to the number of positive real roots of the polynomial. Specifically, the number of sign changes is equal to the number of positive real roots, counted with multiplicity, plus a non-negative even number. This theorem is a fundamental result in real analysis and polynomial theory.

### Dependencies
- `num_WF`
- `NUMSEG_SING`
- `IN_SING`
- `UNWIND_THM2`
- `IN_NUMSEG`
- `ARITH_RULE`
- `MONO_EXISTS`
- `LE_0`
- `LE_1`
- `SUM_CLAUSES_RIGHT`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`
- `VARIATION_SUBSET`
- `SUBSET_NUMSEG`
- `IN_DIFF`
- `UNWIND_THM1`
- `GSYM`
- `NOT_ODD`
- `ODD_VARIATION_POSITIVE_ROOT`
- `MEMBER_NOT_EMPTY`
- `IN_ELIM_THM`
- `LEFT_IMP_EXISTS_THM`
- `VARIATION_POSITIVE_ROOT_MULTIPLICITY_FACTOR`
- `IN_NUMSEG`
- `LE_REFL`
- `EVEN_ADD`
- `SET_RULE`
- `REAL_ENTIRE`
- `REAL_POW_EQ_0`
- `REAL_SUB_0`
- `EXTENSION`
- `IN_DELETE`
- `FINITE_SUBSET`
- `REAL_POLYFUN_FINITE_ROOTS`
- `NSUM_CLAUSES`
- `REAL_ENTIRE`
- `MULTIPLICITY_OTHER_ROOT`

### Porting notes (optional)
- The usage of `NSUM` and `SUM` with explicit index sets might need adjustment based on how summation is handled in the target proof assistant.
- The `variation` function is not standard and will likely need to be defined separately.
- Theorems involving root multiplicities might also need to be explicitly ported or proven.


---

