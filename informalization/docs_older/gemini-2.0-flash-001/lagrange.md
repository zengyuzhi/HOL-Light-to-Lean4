# lagrange.ml

## Overview

Number of statements: 4

`lagrange.ml` provides a basic formalization of group theory culminating in Lagrange's theorem. It contains a minimal development of groups, intended as a stepping stone to the theorem. For a more comprehensive treatment of group theory, users are directed to `Library/grouptheory.ml`.


## group

### Name of formal statement
group

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let group = new_definition
  `group(g,( ** ),i,(e:A)) <=>
    (e IN g) /\ (!x. x IN g ==> i(x) IN g) /\
    (!x y. x IN g /\ y IN g ==> (x ** y) IN g) /\
    (!x y z. x IN g /\ y IN g /\ z IN g ==> (x ** (y ** z) = (x ** y) ** z)) /\
    (!x. x IN g ==> (x ** e = x) /\ (e ** x = x)) /\
    (!x. x IN g ==> (x ** i(x) = e) /\ (i(x) ** x = e))`;;
```

### Informal statement
The predicate `group(g, **, i, e)` holds if and only if the following conditions are met:

1.  The element `e` belongs to the set `g`.
2.  For all `x`, if `x` belongs to `g`, then `i(x)` belongs to `g`.
3.  For all `x` and `y`, if `x` belongs to `g` and `y` belongs to `g`, then `x ** y` belongs to `g`.
4.  For all `x`, `y`, and `z`, if `x` belongs to `g`, `y` belongs to `g`, and `z` belongs to `g`, then `x ** (y ** z) = (x ** y) ** z`.
5.  For all `x`, if `x` belongs to `g`, then `x ** e = x` and `e ** x = x`.
6.  For all `x`, if `x` belongs to `g`, then `x ** i(x) = e` and `i(x) ** x = e`.

### Informal sketch
The definition of `group` introduces a predicate that characterizes a group in terms of its carrier set `g`, binary operation `**`, inverse operation `i`, and identity element `e`. The definition is a direct formalization of the standard group axioms: closure of `g` under `**` and `i`, associativity of `**`, and the identity and inverse laws. The predicate `group(g, **, i, e)` is defined to be true if and only if all these axioms hold.

### Mathematical insight
This definition captures the essence of a group structure. It's a fundamental concept in abstract algebra, providing a foundation for studying more complex algebraic structures. The definition ensures that the set `g`, equipped with the operation `**`, the inverse `i`, and the identity `e`, satisfies the necessary properties to be considered a group. The `group` definition is essential for formulating and proving theorems in group theory, such as Lagrange's theorem mentioned in the comment.

### Dependencies
- `Library/prime.ml`

### Porting notes (optional)
- Most proof assistants have built-in libraries for group theory. This definition can be used to verify compatibility or to define a group structure from scratch.
- The infix notation `**` might need adjustments depending on the target proof assistant capabilities.
- The handling of the type `A` might vary depending on the type system of the target proof assistant.


---

## subgroup

### Name of formal statement
subgroup

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let subgroup = new_definition
  `subgroup h (g,( ** ),i,(e:A)) <=> h SUBSET g /\ group(h,( ** ),i,e)`;;
```

### Informal statement
Given a set `h`, a set `g`, a binary operation ` ** `, a unary operation `i`, and an element `e` of type `A`, `h` is a subgroup of the group defined by `g`, ` ** `, `i`, and `e` if and only if `h` is a subset of `g` and `h` forms a group under the operations ` ** `, `i`, and `e`.

### Informal sketch
- The definition of `subgroup` simply combines the subset relation with the `group` predicate.
- To prove that a set `h` with operations ` ** `, `i`, and `e` is a subgroup of a group `g` with the same operations, one needs to show two things:
  - `h` must be a subset of `g`.
  - The set `h` with the operations ` ** `, `i`, and `e` must satisfy the group axioms.

### Mathematical insight
The notion of a subgroup is a fundamental concept in group theory. It formalizes the idea of a group contained within another group, inheriting the group's operations. It is important for understanding the structure of groups and for constructing new groups from existing ones.

### Dependencies
- Definition: `group`
- Theorem: `SUBSET`


---

## GROUP_LAGRANGE_COSETS

### Name of formal statement
GROUP_LAGRANGE_COSETS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GROUP_LAGRANGE_COSETS = prove
 (`!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> ?q. (CARD(g) = CARD(q) * CARD(h)) /\
                (!b. b IN g ==> ?a x. a IN q /\ x IN h /\ (b = a ** x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[group; subgroup; SUBSET] THEN STRIP_TAC THEN
  ABBREV_TAC
   `coset = \a:A. {b:A | b IN g /\ (?x:A. x IN h /\ (b = a ** x))}` THEN
  SUBGOAL_THEN `!a:A. a IN g ==> a IN (coset a)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "coset" THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(h:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!a. FINITE((coset:A->A->bool) a)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "coset" THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `g:A->bool` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A x:A y. a IN g /\ x IN g /\ y IN g /\ ((a ** x) :A = a ** y)
                ==> (x = y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(e:A ** x:A):A = e ** y` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN
     `((i(a):A ** a:A) ** x) = (i(a) ** a) ** y`
     (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. a IN g ==> (CARD(coset a :A->bool) = CARD(h:A->bool))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(coset:A->A->bool) (a:A) = IMAGE (\x. a ** x) (h:A->bool)`
    SUBST1_TAC THENL
     [EXPAND_TAC "coset" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A y. x IN g /\ y IN g ==> (i(x ** y) = i(y) ** i(x))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(x:A ** y:A) :A` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(x:A ** (y ** i(y))) ** i(x)` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN g ==> (i(i(x)) = x)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(i:A->A)(x)` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. a IN g /\ b IN g
          ==> ((coset:A->A->bool) a = coset b) \/
              ((coset a) INTER (coset b) = {})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `((i:A->A)(b) ** a:A) IN (h:A->bool)` THENL
     [DISJ1_TAC THEN EXPAND_TAC "coset" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      GEN_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN
       `!x:A. x IN h ==> (b ** (i(b) ** a:A) ** x = a ** x) /\
                         (a ** i(i(b) ** a) ** x = b ** x)`
       (fun th -> EQ_TAC THEN REPEAT STRIP_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[th]) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISJ2_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN EXPAND_TAC "coset" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[TAUT `(a /\ b) /\ (a /\ c) <=> a /\ b /\ c`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(i(b:A) ** a ** y):A = i(b) ** b ** z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A ** y):A = e ** z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A ** y):A = z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((i(b:A) ** a:A) ** y):A = z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `((i(b:A) ** a:A) ** y) ** i(y) = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A) ** (y ** i(y)) = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A) ** e = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(i(b:A) ** a:A):A = z ** i(y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{c:A | ?a:A. a IN g /\ (c = (@)(coset a))}` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> b /\ a`) THEN CONJ_TAC THENL
   [X_GEN_TAC `b:A` THEN DISCH_TAC THEN
    EXISTS_TAC `(@)((coset:A->A->bool) b)` THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `b:A` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(@)((coset:A->A->bool) b) IN (coset b)` MP_TAC THENL
     [REWRITE_TAC[IN] THEN MATCH_MP_TAC SELECT_AX THEN
      ASM_MESON_TAC[IN];
      ALL_TAC] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RATOR_CONV)
                         [SYM th]) THEN
    REWRITE_TAC[] THEN
    ABBREV_TAC `C = (@)((coset:A->A->bool) b)` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(i:A->A)(c)` THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = {c:A | ?a:A. a IN g /\ (c = (@)(coset a))}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!a:A b. a IN g /\ b IN g /\ a IN coset(b) ==> b IN coset(a)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "coset" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(i:A->A) c` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A b c. a IN coset(b) /\ b IN coset(c) /\ c IN g ==> a IN coset(c)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "coset" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A b:A. a IN coset(b) ==> a IN g` ASSUME_TAC THENL
   [EXPAND_TAC "coset" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A b. a IN coset(b) /\ b IN g ==> (coset a = coset b)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN
    MAP_EVERY UNDISCH_TAC
     [`!a:A b:A. a IN coset(b) ==> a IN g`;
      `!a:A b c. a IN coset(b) /\ b IN coset(c) /\ c IN g ==> a IN coset(c)`;
      `!a:A b. a IN g /\ b IN g /\ a IN coset(b) ==> b IN coset(a)`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. a IN g ==> (@)(coset a):A IN (coset a)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `!a:A. a IN g ==> a IN coset a` THEN
    DISCH_THEN(MP_TAC o SPEC `a:A`) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN; SELECT_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:A. a IN q ==> a IN g` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:A x:A a' x'. a IN q /\ a' IN q /\ x IN h /\ x' IN h /\
                    ((a' ** x') :A = a ** x) ==> (a' = a) /\ (x' = x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `(c ==> a /\ b ==> d) ==> a /\ b /\ c ==> d`) THEN
    STRIP_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `a1:A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `a2:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `a:A IN g /\ a' IN g` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) /\ a ==> a /\ b`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((coset:A->A->bool) a1 = coset a) /\ (coset a2 = coset a')`
    MP_TAC THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    ONCE_ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "coset" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(x:A ** (i:A->A)(x')):A` THEN
    ASM_SIMP_TAC[] THEN UNDISCH_TAC `(a':A ** x':A):A = a ** x` THEN
    DISCH_THEN(MP_TAC o C AP_THM `(i:A->A) x'` o AP_TERM `(**):A->A->A`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g = IMAGE (\(a:A,x:A). (a ** x):A) {(a,x) | a IN q /\ x IN h}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[EXISTS_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    REWRITE_TAC[PAIR_EQ] THEN
    REWRITE_TAC[CONJ_ASSOC; ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {(a:A,x:A) | a IN q /\ x IN h}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
      CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
      REWRITE_TAC[PAIR_EQ] THEN REPEAT GEN_TAC THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_PRODUCT THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `g:A->bool` THEN
    ASM_REWRITE_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_PRODUCT THEN CONJ_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `g:A->bool` THEN
  ASM_REWRITE_TAC[SUBSET]);;
```
### Informal statement
For all `g`, `h`, `**`, `i`, and `e`, if `(g, **, i, e)` forms a group, `h` is a subgroup of `(g, **, i, e)`, and `g` is finite, then there exists a set `q` such that the cardinality of `g` is equal to the cardinality of `q` multiplied by the cardinality of `h`, and for all `b` in `g`, there exist `a` in `q` and `x` in `h` such that `b` is equal to `a ** x`.

### Informal sketch
The proof demonstrates Lagrange's theorem by constructing a set of coset representatives.
- First, the coset of an element `a` in `g` is defined as `{b | b IN g /\ (?x. x IN h /\ (b = a ** x))}`.
- It is shown that `a` is in its own coset `coset a`.
- It is also shown that the subgroup `h` is finite, and that each coset is finite.
- Then we prove that for all `a`, `x`, `y` in `g`, `a ** x = a ** y` implies `x = y` (cancellation law).
- It is shown that for any element `a` in `g`, the cardinality of the coset of `a` is equal to the cardinality of `h`. This is done by demonstrating that `coset a` is the image of `h` under the injective map `x -> a ** x`, using the theorem `CARD_IMAGE_INJ`.
- Next, we verify group properties for inverses, proving `i(x ** y) = i(y) ** i(x)` and `i(i(x)) = x` for elements `x`, `y` in `g`.
- It is proven that for any elements `a` and `b` in `g`, either their cosets `coset a` and `coset b` are equal or their intersection is empty.
- A set `q` is constructed containing a representative element from each distinct coset.Specifically, `q` is the set `{c | ?a. a IN g /\ (c = (@)(coset a))}`, where `(@)` is the Hilbert choice operator.
- It is shown that if `a` is in `g` and `b` is in the coset of `a`, then the coset of `b` is the same as the coset of `a`. And, if `a` is in the coset of `b` and `b` is in coset of `c` and `c` is in `g` then `a` is in coset of `c`
- It is proven that `g` is equal to the image of the cartesian product of `q` and `h` under the operation `(a, x) -> a ** x` and use the result that this mapping is injective.
- Finally, using `CARD_PRODUCT` and `CARD_IMAGE_INJ`, the Lagrange theorem `CARD g = CARD q * CARD h` is derived.

### Mathematical insight
Lagrange's theorem is a fundamental result in group theory. It states that for any finite group `g`, the order (cardinality) of any subgroup `h` of `g` must divide the order of `g`. The theorem is proved by partitioning `g` into cosets of `h`, each of which has the same cardinality as `h`. The set of coset representatives `q` essentially indexes these distinct cosets.

### Dependencies
- Definitions:
  - `group`
  - `subgroup`
  - `SUBSET`
- Theorems:
  - `FINITE_SUBSET`
  - `IN_ELIM_THM`
  - `EXTENSION`
  - `IN_IMAGE`
  - `CARD_IMAGE_INJ`
  - `EQ_TRANS`
  - `SELECT_AX`
  - `RIGHT_EXISTS_AND_THM`
  - `CONJ_ASSOC`
  - `CONJ_SYM`
  - `FORALL_PAIR_THM`
  - `CARD_PRODUCT`
  - `FINITE_PRODUCT`

### Porting notes (optional)
The proof relies heavily on rewriting and equational reasoning within group theory, so a proof assistant with strong automation for these tasks will be beneficial. The use of the Hilbert choice operator `(@)` to select coset representatives may require special attention in systems without built-in choice. In proof assistants like Coq, one might need to use quotient types or other techniques to represent cosets and avoid direct reliance on choice.


---

## GROUP_LAGRANGE

### Name of formal statement
GROUP_LAGRANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GROUP_LAGRANGE = prove
 (`!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> (CARD h) divides (CARD g)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP GROUP_LAGRANGE_COSETS) THEN
  MESON_TAC[DIVIDES_LMUL; DIVIDES_REFL]);;
```

### Informal statement
For all `g`, `h`, `**`, `i`, and `e` of type `A`, if `(g, **, i, e)` is a group, `h` is a subgroup of `(g, **, i, e)`, and `g` is finite, then the cardinality of `h` divides the cardinality of `g`.

### Informal sketch
The proof proceeds as follows:
- Assume `g` is a group with operation `**`, identity `i` and neutral element `e`, `h` is a subgroup of `g`
and `g` is finite.
- Apply `GROUP_LAGRANGE_COSETS` to show that the cardinality of `g` is the cardinality of `h` multiplied by the index (number of cosets).
- Use a MESON tactic that employs `DIVIDES_LMUL` (if a divides b, then a divides b*c) and `DIVIDES_REFL` (a divides a) to conclude that the cardinality of `h` divides the cardinality of `g`.

### Mathematical insight
This theorem states Lagrange's theorem in group theory, which asserts that for any finite group `g` and subgroup `h` of `g`, the order of `h` divides the order of `g`. The theorem is a fundamental result in finite group theory, providing constraints on the possible sizes of subgroups.

### Dependencies
- `group`
- `subgroup`
- `FINITE`
- `CARD`
- `GROUP_LAGRANGE_COSETS`
- `DIVIDES_LMUL`
- `DIVIDES_REFL`


---

