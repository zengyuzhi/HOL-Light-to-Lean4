# piseries.ml

## Overview

Number of statements: 89

`piseries.ml` formalizes Taylor series expansions for trigonometric functions, specifically tangent and cotangent. It achieves this by developing a partial fraction expansion for the cotangent function. The file builds upon results from analysis, transcendental functions, the floor function, polynomial theory, and iteration, and is related to Machin-like formulas.


## REAL_LE_1_POW2

### Name of formal statement
REAL_LE_1_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_LE_1_POW2 = prove
 (`!n. &1 <= &2 pow n`,
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> 0 < n`;
              EXP_LT_0; ARITH]);;
```

### Informal statement
For all natural numbers `n`, 1 ≤ 2<sup>n</sup>, where the numbers are interpreted as real numbers.

### Informal sketch
The proof proceeds as follows:
- Rewrite using `REAL_OF_NUM_POW` and `REAL_OF_NUM_LE` to convert the natural numbers 1 and 2 to their real counterparts, and the less-than-or-equal relation to real less-than-or-equal relation, so the goal becomes `&1 <= &2 pow n`.
- Apply `ARITH_RULE` to transform the goal `!n. &1 <= &2 pow n` into `!n. 0 < n ==> &1 <= &2 pow n`.
- Use `EXP_LT_0` to handle the base case `n = 0`, showing `&1 <= &2 pow 0` simplifies to `&1 <= &1`, which is trivially true.
- Finally employ `ARITH` to deal with the inductive step, showing that if `&1 <= &2 pow n`, then `&1 <= &2 pow (SUC n)`.

### Mathematical insight
This theorem establishes a basic inequality between the real number 1 and powers of 2. It's a fundamental result used in many areas of real analysis and computer science, often as a base case or bound in inductive arguments and algorithm analysis.

### Dependencies
- `REAL_OF_NUM_POW`
- `REAL_OF_NUM_LE`
- `EXP_LT_0`


---

## REAL_LT_1_POW2

### Name of formal statement
REAL_LT_1_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_LT_1_POW2 = prove
 (`!n. &1 < &2 pow n <=> ~(n = 0)`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&2 pow 0`)) THEN
  MATCH_MP_TAC REAL_POW_MONO_LT THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN POP_ASSUM MP_TAC THEN ARITH_TAC);;
```
### Informal statement
For all natural numbers `n`, 1 is less than 2 to the power of `n` if and only if `n` is not equal to 0.

### Informal sketch
The proof proceeds as follows:
- By induction on `n`.
- Case `n = 0`: We assume `n = 0` and simplify both sides of the inequality `&1 < &2 pow n`. The right side `&2 pow 0` is reduced to 1, making the inequality `&1 < &1`, which is false.
- Then, use `REAL_POW_MONO_LT` which states `0 < a /\ 1 < b ==> a pow n < b pow n` and `REAL_OF_NUM_LT` which states `!m n. &m < &n <=> m < n`.
- Finally, the goal is solved by arithmetic reasoning.

### Mathematical insight
The theorem states that 2 raised to any positive integer power is strictly greater than 1. This is a basic and important property related to the growth of powers of numbers greater than 1.

### Dependencies
- `REAL_RAT_REDUCE_CONV`
- `REAL_POW_MONO_LT`
- `REAL_OF_NUM_LT`


---

## REAL_POW2_CLAUSES

### Name of formal statement
REAL_POW2_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_POW2_CLAUSES = prove
 (`(!n. &0 <= &2 pow n) /\
   (!n. &0 < &2 pow n) /\
   (!n. &0 <= inv(&2 pow n)) /\
   (!n. &0 < inv(&2 pow n)) /\
   (!n. inv(&2 pow n) <= &1) /\
   (!n. &1 - inv(&2 pow n) <= &1) /\
   (!n. &1 <= &2 pow n) /\
   (!n. &1 < &2 pow n <=> ~(n = 0)) /\
   (!n. &0 <= &1 - inv(&2 pow n)) /\
   (!n. &0 <= &2 pow n - &1) /\
   (!n. &0 < &1 - inv(&2 pow n) <=> ~(n = 0))`,
  SIMP_TAC[REAL_LE_1_POW2; REAL_LT_1_POW2; REAL_SUB_LE; REAL_SUB_LT;
           REAL_INV_LE_1] THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_INV_EQ; REAL_POW_LT; REAL_POW_LE;
           REAL_OF_NUM_LE; REAL_OF_NUM_LT; ARITH;
           REAL_ARITH `&1 - x <= &1 <=> &0 <= x`] THEN
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&2 pow 1)` THEN
  ASM_SIMP_TAC[REAL_LE_INV2; REAL_POW_MONO; REAL_POW_LT; REAL_OF_NUM_LT; ARITH;
               REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```
### Informal statement
Prove the conjunction of the following statements for all natural numbers `n`:
1.  `0 <= 2^n`
2.  `0 < 2^n`
3.  `0 <= 1/(2^n)`
4.  `0 < 1/(2^n)`
5.  `1/(2^n) <= 1`
6.  `1 - (1/(2^n)) <= 1`
7.  `1 <= 2^n`
8.  `1 < 2^n` if and only if `n` is not equal to `0`
9.  `0 <= 1 - (1/(2^n))`
10. `0 <= 2^n - 1`
11. `0 < 1 - (1/(2^n))` if and only if `n` is not equal to `0`.

### Informal sketch
The proof proceeds as follows:

- First apply simplification using theorems related to inequalities of `1 pow 2`, inequalities less than `1 pow 2`, real subtraction inequalities, and the inequality of the inverse less than `1`.
- Then simplify using theorems related to inequalities of inverses and powers, real number conversions, and arithmetic reasoning. We also use the tactic `REAL_ARITH` which uses linear arithmetic decision procedures.
- Generalize the goal and perform case splitting on the condition `n = 0`.
- Simplify using the assumption `n = 0`
- Apply a conversion to reduce rational expressions (`REAL_RAT_REDUCE_CONV`).
- Use transitivity with a suitably instantiated lemma.
- Instantiate an existential with `inv(&2 pow 1)`.
- Simplify using theorems related to the inverse of `2`, monotonicity of powers, inequalities of powers, number conversions, and arithmetic. Also rewrite `1 <= n <=> ~(n = 0)`.
- Apply a conversion to reduce rational expressions again.

### Mathematical insight
This theorem establishes several basic inequalities relating powers of 2 with other constants and their inverses in the real numbers. These inequalities are fundamental for reasoning about the growth and decay of exponential functions and are frequently used in proofs involving real analysis.

### Dependencies
- `REAL_LE_1_POW2`
- `REAL_LT_1_POW2`
- `REAL_SUB_LE`
- `REAL_SUB_LT`
- `REAL_INV_LE_1`
- `REAL_LE_INV_EQ`
- `REAL_LT_INV_EQ`
- `REAL_POW_LT`
- `REAL_POW_LE`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_LT`
- `REAL_LE_INV2`
- `REAL_POW_MONO`
- `REAL_LET_TRANS`
### Porting notes (optional)
The `REAL_ARITH` tactic might need to be replaced by a similar tactic in other proof assistants that can handle linear arithmetic over real numbers. Also, the conversions `REAL_RAT_REDUCE_CONV` might be automatically handled by other systems. The case split on `n = 0` and subsequent simplification may require explicit manipulation. The transitivity step using `REAL_LET_TRANS` is likely to map onto a transitivity rule application in other systems.

---

## REAL_INTEGER_CLOSURES

### Name of formal statement
REAL_INTEGER_CLOSURES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let REAL_INTEGER_CLOSURES = prove
 (`(!n. ?p. abs(&n) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x + y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x - y) = &p) /\
   (!x y. (?m. abs(x) = &m) /\ (?n. abs(y) = &n) ==> ?p. abs(x * y) = &p) /\
   (!x r. (?n. abs(x) = &n) ==> ?p. abs(x pow r) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(--x) = &p) /\
   (!x. (?n. abs(x) = &n) ==> ?p. abs(abs x) = &p)`,
  REWRITE_TAC[GSYM integer; INTEGER_CLOSED]);;
```
### Informal statement
The absolute value of any integer is an integer; if the absolute values of two real numbers `x` and `y` are integers, then the absolute values of their sum `x + y`, their difference `x - y`, their product `x * y`, `x` to the power of `r`, negation `--x`, and absolute value `abs x` are also integers.

### Informal sketch
The proof uses `REWRITE_TAC` with `GSYM integer`（the definition of `integer`) and `INTEGER_CLOSED` (a pre-existing theorem asserting that the set of integers is closed under the above operations). The goal is to prove closure properties for integers regarding absolute values of sums, differences, products, and negations. By rewriting with `GSYM integer`, we may be able to replace integer tests using existential quantifiers with an underlying set membership condition. The `INTEGER_CLOSED` theorem then proves all closure properties directly.

### Mathematical insight
Essentially, this theorem states that if two real numbers have integer absolute values, then standard arithmetic operations performed on these numbers result in real numbers that also have integer absolute values. It confirms that `abs x` maps integers to integers, and arithmetic operations preserve this property.

### Dependencies
- Theorems: `INTEGER_CLOSED`
- Definitions: `integer`


---

## PI_APPROX_25_BITS

### Name of formal statement
PI_APPROX_25_BITS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let PI_APPROX_25_BITS = time PI_APPROX_BINARY_RULE 25;;
```

### Informal statement
The theorem `PI_APPROX_25_BITS` states that the result of applying the `PI_APPROX_BINARY_RULE` to the integer 25 is computed within a certain time frame. `PI_APPROX_BINARY_RULE` is an unspecified function that computes an approximation of pi to a specified binary precision (in this case, 25 bits).

### Informal sketch
The theorem asserts the successful computation of a binary approximation of pi to 25 bits of precision using the `PI_APPROX_BINARY_RULE` function. The proof involves applying the `time` tactic to the goal `PI_APPROX_BINARY_RULE 25`. The actual content of `PI_APPROX_BINARY_RULE` or the proof requirements needed to define it are not evident from this statement. Typically, the proof would involve unwinding the definition of `PI_APPROX_BINARY_RULE` and then demonstrating that the resulting code produces the intended approximation of pi within the allowed time.

### Mathematical insight
The theorem serves to establish the computational feasibility of approximating pi to 25 bits of binary precision using a specific rule or function defined by `PI_APPROX_BINARY_RULE`. The `time` function is used to confirm that the calculation falls within some reasonable time limit. This is a performance or empirical theorem, rather than a purely logical one.

### Dependencies
- `PI_APPROX_BINARY_RULE`


---

## POLYMERIZE_CONV

### Name of formal statement
POLYMERIZE_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let POLYMERIZE_CONV =
  let pth = prove
   (`a = poly [a] x`,
    REWRITE_TAC[poly; REAL_MUL_RZERO; REAL_ADD_RID])
  and qth = prove
   (`x * poly p x = poly (CONS (&0) p) x`,
    REWRITE_TAC[poly; REAL_ADD_LID]) in
  let conv_base = GEN_REWRITE_CONV I [pth]
  and conv_zero = GEN_REWRITE_CONV I [qth]
  and conv_step = GEN_REWRITE_CONV I [GSYM(CONJUNCT2 poly)] in
  let is_add = is_binop `(+):real->real->real`
  and is_mul = is_binop `(*):real->real->real` in
  let rec conv tm =
    if is_add tm then
      let l,r = dest_comb tm in
      let r1,r2 = dest_comb r in
      let th1 = AP_TERM l (AP_TERM r1 (conv r2)) in
      TRANS th1 (conv_step(rand(concl th1)))
    else if is_mul tm then
      let th1 = AP_TERM (rator tm) (conv (rand tm)) in
      TRANS th1 (conv_zero(rand(concl th1)))
    else conv_base tm in
  conv;;
```

### Informal statement
The function `POLYMERIZE_CONV` is defined using a conversion `conv` which transforms an arbitrary real polynomial expression in terms of addition and multiplication into a canonical, list-based form `poly`. If the input term is an addition of the form `l + (r1 * r2)`, then the conversion transforms `r2` using the `conv` function itself. An equality theorem is created with `l` applied to the term `r1` applied to the converted `r2`, and this equality is then transformed by the conversion `conv_step` which uses the polynomial expansion property. If the term is a multiplication `a * b`, `b` is transformed by the `conv` function. Then, a new equality theorem is created with `a` applied to the converted `b` and this equality is transformed by the conversion `conv_zero` which rewrites using the fact that `x * poly p x = poly (CONS (&0) p) x`. If it is neither addition nor multiplication, then the term is converted into the base polynomial form `poly [a] x`. This base case conversion `conv_base` rewrites terms `a` as `poly [a] x`.

### Informal sketch
The `POLYMERIZE_CONV` conversion transforms real polynomial expressions into a canonical list-based form `poly`.
- It handles sums and products recursively.

- Base cases:
    - A constant `a` is converted to the polynomial `poly [a] x` using the `conv_base` conversion, derived from the theorem `a = poly [a] x`.

- Recursive cases:

    -  For an addition `l + (r1 * r2)`:
       - Convert `r2` recursively using `conv`.
       - Apply `l` to `r1` applied to the converted `r2`.
       - The result `l + (r1 * poly p x)` is rewritten using `conv_step` and the theorem `CONJUNCT2 poly`, which is implicitly `poly (p ++ q) x = poly p x + poly q x` after suitable substitutions and symmetry.
    -  For a multiplication `a * b`:
       - The subterm `b` is recursively converted using `conv`.
       - Applying `a` to the converted `b`.
       - The result of this application is rewritten using `conv_zero` and the theorem `x * poly p x = poly (CONS (&0) p) x`.

The conversion uses derived conversions based on rewriting with provided theorems: `pth`, `qth`, and `CONJUNCT2 poly`.

### Mathematical insight
The conversion aims to represent polynomials in a standard form based on lists of coefficients. The recursive calls systematically break down the polynomial expression into simpler arithmetic operations until only constants remain, which can be trivially converted to the equivalent `poly` form. Then, the conversion rewrites the nested polynomial `poly` via list operations until the whole term is a `poly` expression in canonical form.

### Dependencies
- Definitions:
    - `poly`
- Theorems:
    - `REAL_MUL_RZERO`
    - `REAL_ADD_RID`
    - `REAL_ADD_LID`
    - `CONJUNCT2 poly`


---

## cot

### Name of formal statement
cot

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let cot = new_definition
  `cot x = cos x / sin x`;;
```

### Informal statement
The cotangent of `x` is defined to be the cosine of `x` divided by the sine of `x`.

### Informal sketch
The definition is introduced directly by equational definition. No proof is necessary.

### Mathematical insight
This definition introduces the cotangent function (`cot`) in terms of the cosine (`cos`) and sine (`sin`) functions. This is the standard definition of the cotangent function.

### Dependencies
None


---

## COT_TAN

### Name of formal statement
COT_TAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
prove
 (`cot(x) = inv(tan(x))`,
  REWRITE_TAC[cot; tan; REAL_INV_DIV]);;
```

### Informal statement
Prove that the cotangent of `x` is equal to the inverse of the tangent of `x`.

### Informal sketch
The proof proceeds by rewriting the left-hand side of the equation `cot(x) = inv(tan(x))` using the definitions of `cot` and `tan`, and the theorem `REAL_INV_DIV`.

- The definitions of `cot` and `tan` are used to rewrite `cot(x)` and `tan(x)` in terms of `cos(x)` and `sin(x)`.
- The theorem `REAL_INV_DIV`, which states that `inv(x/y) = y/x`, is used to simplify `inv(tan(x))`.

### Mathematical insight
This theorem establishes the fundamental relationship between the cotangent and tangent functions, namely that they are reciprocals of each other. This is a basic trigonometric identity.

### Dependencies
- Definitions: `cot`, `tan`
- Theorems: `REAL_INV_DIV`


---

## SUM_PERMUTE_0

### Name of formal statement
SUM_PERMUTE_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_PERMUTE_0 = prove
 (`!n p. (!y. y < n ==> ?!x. x < n /\ (p(x) = y))
        ==> !f. sum(0,n)(\n. f(p n)) = sum(0,n) f`,
  INDUCT_TAC THEN GEN_TAC THEN TRY(REWRITE_TAC[sum] THEN NO_TAC) THEN
  DISCH_TAC THEN GEN_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  REWRITE_TAC[LESS_SUC_REFL] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [sum] THEN REWRITE_TAC[ADD_CLAUSES] THEN
  ABBREV_TAC `q:num->num = \r. if r < k then p(r) else p(SUC r)` THEN
  SUBGOAL_THEN `!y:num. y < n ==> ?!x. x < n /\ (q x = y)` MP_TAC THENL
   [X_GEN_TAC `y:num` THEN DISCH_TAC THEN (MP_TAC o ASSUME)
      `!y. y < (SUC n) ==> ?!x. x < (SUC n) /\ (p x = y)` THEN
    DISCH_THEN(MP_TAC o SPEC `y:num`) THEN
    W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
     [MATCH_MP_TAC LT_TRANS THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[LESS_SUC_REFL];
      DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MP th))] THEN
    CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    CONJ_TAC THENL
     [DISJ_CASES_TAC(SPECL [`x:num`; `k:num`] LTE_CASES) THENL
       [EXISTS_TAC `x:num` THEN EXPAND_TAC "q" THEN BETA_TAC THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `&k` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
        UNDISCH_TAC `k < (SUC n)` THEN
        REWRITE_TAC[GSYM LT_SUC_LE; LE_ADD2];
        MP_TAC(ASSUME `k <= x:num`) THEN REWRITE_TAC[LE_LT] THEN
        DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC SUBST_ALL_TAC) THENL
         [EXISTS_TAC `x - 1` THEN EXPAND_TAC "q" THEN BETA_TAC THEN
          UNDISCH_TAC `k < x:num` THEN
          DISCH_THEN(X_CHOOSE_THEN `d:num` MP_TAC o MATCH_MP LESS_ADD_1) THEN
          REWRITE_TAC[GSYM ADD1; ADD_CLAUSES] THEN
          DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[LT_SUC]) THEN
          ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
          UNDISCH_TAC `(k + d) < k:num` THEN
          REWRITE_TAC[GSYM LE_SUC_LT] THEN CONV_TAC CONTRAPOS_CONV THEN
          REWRITE_TAC[GSYM NOT_LT; REWRITE_RULE[ADD_CLAUSES] LESS_ADD_SUC];
          SUBST_ALL_TAC(ASSUME `(p:num->num) x = n`) THEN
          UNDISCH_TAC `y < n:num` THEN ASM_REWRITE_TAC[LT_REFL]]];
      SUBGOAL_THEN `!z. q z :num = p(if z < k then z else SUC z)` MP_TAC THENL
       [GEN_TAC THEN EXPAND_TAC "q" THEN BETA_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[];
        DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
      MAP_EVERY X_GEN_TAC [`x1:num`; `x2:num`] THEN STRIP_TAC THEN
      UNDISCH_TAC `!y. y < (SUC n) ==>
                          ?!x. x < (SUC n) /\ (p x = y)` THEN
      DISCH_THEN(MP_TAC o SPEC `y:num`) THEN
      REWRITE_TAC[MATCH_MP LESS_SUC (ASSUME `y < n:num`)] THEN
      CONV_TAC(ONCE_DEPTH_CONV EXISTS_UNIQUE_CONV) THEN
      DISCH_THEN(MP_TAC o SPECL [`if x1 < k then x1 else SUC x1`;
        `if x2 < k then x2 else SUC x2`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      W(C SUBGOAL_THEN MP_TAC o funpow 2 (fst o dest_imp) o snd) THENL
       [CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_SUC] THEN
        MATCH_MP_TAC LESS_SUC THEN ASM_REWRITE_TAC[];
        DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MATCH_MP th)) THEN
        REPEAT COND_CASES_TAC THEN REWRITE_TAC[SUC_INJ] THENL
         [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x2 < k:num)` THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LT_TRANS THEN
          EXISTS_TAC `SUC x2` THEN ASM_REWRITE_TAC[LESS_SUC_REFL];
          DISCH_THEN(SUBST_ALL_TAC o SYM) THEN UNDISCH_TAC `~(x1  < k:num)` THEN
          CONV_TAC CONTRAPOS_CONV THEN DISCH_THEN(K ALL_TAC) THEN
          REWRITE_TAC[] THEN MATCH_MP_TAC LT_TRANS THEN
          EXISTS_TAC `SUC x1` THEN ASM_REWRITE_TAC[LESS_SUC_REFL]]]];
    DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
      [GSYM th]) THEN BETA_TAC THEN
    UNDISCH_TAC `k < (SUC n)` THEN
    REWRITE_TAC[LE_SUC; LT_SUC_LE; LE_ADD2] THEN
    DISCH_THEN(X_CHOOSE_TAC `d:num` o MATCH_MP LESS_EQUAL_ADD) THEN
    GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o ONCE_DEPTH_CONV)
      [ASSUME `n = k + d:num`] THEN REWRITE_TAC[GSYM SUM_TWO] THEN
    GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV)
      [ASSUME `n = k + d:num`] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD_SUC)] THEN
    REWRITE_TAC[GSYM SUM_TWO; sum; ADD_CLAUSES] THEN BETA_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN BINOP_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN
      REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
      BETA_TAC THEN EXPAND_TAC "q" THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN
      REWRITE_TAC[ASSUME `(p:num->num) k = n`; REAL_EQ_LADD] THEN
      REWRITE_TAC[ADD1; SUM_REINDEX] THEN BETA_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN BETA_TAC THEN
      REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      EXPAND_TAC "q" THEN BETA_TAC THEN ASM_REWRITE_TAC[ADD1]]]);;
```

### Informal statement
For all natural numbers `n` and all functions `p` from natural numbers to natural numbers, if `p` is a permutation of the set of natural numbers less than `n` (that is, for every `y` less than `n`, there exists a unique `x` less than `n` such that `p(x) = y`), then for any function `f` from natural numbers to real numbers, the sum of `f(p(m))` from `m = 0` to `n` is equal to the sum of `f(m)` from `m = 0` to `n`.

### Informal sketch
The theorem is proved by induction on `n`.

- Base case: `n = 0`. The sum from 0 to 0 is just the function evaluated at 0. Hence, `f(p 0) = f(0)`.

- Inductive step: Assume the theorem holds for `n`. We need to prove it for `SUC n`.
  - The assumption that `p` is a permutation of `{0, ..., n}` is used by choosing a `k` such that `p(k) = n`. 
  - Define a function `q` such that `q(r) = p(r)` if `r < k` and `q(r) = p(SUC r)` if `r >= k`.
  - We then show that `q` is a permutation of `{0, ..., n-1}`. This involves showing that for all `y < n`, there exits a unique `x < n` such that `q(x) = y`.
  - Use the inductive hypotheses on `q` to say that the sum of `f(q(r))` from `r = 0` to `n` is the same as the sum of `f(r)` from `r = 0` to `n`.
  - Rewrite the original sum from `0` to `SUC n` of `f(p(r))` such that it becomes the sum from `0` to `SUC n` of `f(q(r))`
  - Finally, rewrite the sum from `0` to `SUC n` of `f(q(r))` to become the sum from `0` to `SUC n` of `f(r)`. This involves using the inductive hypthesis about `q` and some algebraic manipulations. This step makes use of `SUM_TWO`, `ADD_SYM`, `ADD_SUC`, and `REAL_ADD_ASSOC`.

### Mathematical insight
The theorem states that if we sum a function `f` over the range `{0, ..., n}`, then permuting the indices using a permutation `p` does not change the value of the sum.  This is a fundamental property of finite sums.

### Dependencies
Theorems:
- `sum`
- `LESS_SUC_REFL`
- `SUM_TWO`
- `ADD_SYM`
- `ADD_SUC`
- `REAL_ADD_ASSOC`
- `SUM_EQ`
- `REAL_ADD_SYM`
- `REAL_EQ_LADD`
- `SUM_REINDEX`
- `ADD1`
- `LTE_CASES`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_LE`
- `LT_SUC_LE`
- `ADD_CLAUSES`
- `LESS_ADD_1`
- `SUC_SUB1`
- `LT_SUC`
- `LE_SUC_LT`
- `NOT_LT`
- `LESS_ADD_SUC`
- `LT_REFL`
- `LESS_EQUAL_ADD`
- `SUC_INJ`

Definitions:
- `sum`

### Porting notes (optional)
The proof strategy relies heavily on rewriting and equational reasoning. Porting to other systems might require careful attention to how sums are defined and how rewriting is handled.The use of `EXISTS_UNIQUE_CONV` and tactics for choosing witnesses (e.g., `X_CHOOSE_THEN`) might need to be adapted based on the target system's capabilities. The definition of function `q` using `if-then-else` might need to be translated carefully depending on how conditional expressions are handled in the target system.


---

## SUM_REVERSE_0

### Name of formal statement
SUM_REVERSE_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_REVERSE_0 = prove
 (`!n f. sum(0,n) f = sum(0,n) (\k. f((n - 1) - k))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `\x. (n - 1) - x`] SUM_PERMUTE_0) THEN
  REWRITE_TAC[] THEN
  W(C SUBGOAL_THEN (fun th -> SIMP_TAC[th]) o funpow 2 lhand o snd) THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  EXISTS_TAC `n - 1 - m` THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;
```

### Informal statement
For all natural numbers `n` and functions `f` from natural numbers to some type, the sum of `f(k)` from `k = 0` to `n` is equal to the sum of `f((n - 1) - k)` from `k = 0` to `n`.

### Informal sketch
The proof demonstrates the equality between the sum of a function `f` from 0 to `n` and the sum of a transformed function `f((n-1)-k)` from 0 to `n`.
- Start by generalizing the variables `n` and `f`.
- Apply theorem `SUM_PERMUTE_0` after specializing it with  `n:num` and `\x. (n - 1) - x`.`SUM_PERMUTE_0` states that `sum(0, n) f = sum(0, n) (\k. f (p k))` where `p` is a permutation.
- Perform rewriting.
- Perform simplification.
- Generalize the variable `m`.
- Rewrite using `EXISTS_UNIQUE_THM`.
- Discharge the assumption and rewrite using `LEFT_AND_EXISTS_THM`.
- Perform an existential instantiation with `n - 1 - m`, followed by applying the conjunction tactic.
- Generalize variables and perform arithmetic simplification using `ARITH_TAC`.

### Mathematical insight
This theorem states that a summation can be reversed or reflected. The function `f` applied to `k` in the sequence from 0 to `n` is equivalent to applying `f` to `(n - 1) - k`, effectively reversing the order of the terms being summed (except that k is reversed with respect to n-1, which is required to get identical results). This is a useful property when manipulating summations, especially within proofs involving inductive definitions or series manipulations.

### Dependencies
- `SUM_PERMUTE_0`
- `EXISTS_UNIQUE_THM`
- `LEFT_AND_EXISTS_THM`


---

## SUM_REVERSE

### Name of formal statement
SUM_REVERSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_REVERSE = prove
 (`!n m f. sum(m,n) f = sum(m,n) (\k. f(((n + 2 * m) - 1) - k))`,
  REPEAT GEN_TAC THEN SUBST1_TAC(ARITH_RULE `m = 0 + m`) THEN
  REWRITE_TAC[SUM_REINDEX] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REVERSE_0] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN
  GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN
  DISCH_THEN(fun th -> AP_TERM_TAC THEN MP_TAC th) THEN
  ARITH_TAC);;
```

### Informal statement
For all natural numbers `n` and `m`, and for every function `f` from natural numbers to an arbitrary type, the sum of `f(k)` from `m` to `n` is equal to the sum of `f(((n + 2 * m) - 1) - k)` from `m` to `n`.

### Informal sketch
The proof proceeds as follows:
- Instantiate the goal.
- Rewrite the initial goal using `SUM_REINDEX`.
- Perform a generic rewrite using `SUM_REVERSE_0`
- Rewrite the result and match it with `SUM_EQ`.
- Perform arithmetic simplifications.
- Discharge the assumption.
- Apply the assumption.
- Perform arithmetic simplification to complete the proof.

### Mathematical insight
The theorem `SUM_REVERSE` states that the sum of a function over a range is equal to the sum of the function with a reversed index. This is a standard result when dealing with summations. The index transformation `k |--> ((n+2*m)-1) - k` effectively reverses the order of summation, and this theorem formalizes that such a re-indexing does not change the value of the sum.

### Dependencies
- Theorems: `SUM_REINDEX`, `SUM_REVERSE_0`, `SUM_EQ`, `ADD_CLAUSES`, `LE_0`


---

## MCLAURIN_SIN

### Name of formal statement
MCLAURIN_SIN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MCLAURIN_SIN = prove
 (`!x n. abs(sin x -
             sum(0,n) (\m. (if EVEN m then &0
                            else -- &1 pow ((m - 1) DIV 2) / &(FACT m)) *
                            x pow m))
         <= inv(&(FACT n)) * abs(x) pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sin`; `\n x. if n MOD 4 = 0 then sin(x)
                              else if n MOD 4 = 1 then cos(x)
                              else if n MOD 4 = 2 then --sin(x)
                              else --cos(x)`] MCLAURIN_ALL_LE) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [CONJ_TAC THENL
     [SIMP_TAC[MOD_0; ARITH_EQ; EQT_INTRO(SPEC_ALL ETA_AX)]; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN X_GEN_TAC `y:real` THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`m:num`; `4`] DIVISION) THEN
    REWRITE_TAC[ARITH_EQ] THEN ABBREV_TAC `d = m MOD 4` THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
    REWRITE_TAC[ADD1; GSYM ADD_ASSOC; MOD_MULT_ADD] THEN
    SPEC_TAC(`d:num`,`d:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN
    W(MP_TAC o DIFF_CONV o lhand o rator o snd) THEN
    SIMP_TAC[REAL_MUL_RID; REAL_NEG_NEG]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real`; `n:num`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real`
   (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
    `(x = y) /\ abs(u) <= v ==> abs((x + u) - y) <= v`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[SIN_0; COS_0; REAL_NEG_0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`r:num`; `4`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC
      (RAND_CONV o ONCE_DEPTH_CONV) [th] THEN
      MP_TAC(SYM th)) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
    UNDISCH_TAC `r MOD 4 < 4` THEN
    SPEC_TAC(`r MOD 4`,`d:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    SIMP_TAC[ARITH_RULE `(x + 1) - 1 = x`;
             ARITH_RULE `(x + 3) - 1 = x + 2`;
             ARITH_RULE `x * 4 + 2 = 2 * (2 * x + 1)`;
             ARITH_RULE `x * 4 = 2 * 2 * x`] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
    REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH_EVEN; REAL_POW_ONE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NEG; SIN_BOUND; COS_BOUND];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_LE_REFL]);;
```

### Informal statement
For all real numbers `x` and natural numbers `n`, the absolute value of the difference between `sin x` and the sum from `0` to `n` of the terms defined as follows is less than or equal to `1 / FACT n * abs(x) pow n`:
For each natural number `m`, the term is `0` if `m` is even; otherwise, it's `(-1) pow ((m - 1) DIV 2) / FACT m * x pow m`.

### Informal sketch
The proof proceeds by induction and Taylor's theorem.

- The base case uses `MCLAURIN_ALL_LE` to establish the inequality for `n = 0`.
- The inductive step aims to show that if the inequality holds for `n`, it also holds for `n + 1`. This involves showing that the derivative of the error term is bounded.
- The proof uses the division algorithm for `m` divided by `4` to simplify terms.
- Real number arithmetic (`REAL_MUL_RID`, `REAL_NEG_NEG`, `REAL_NEG_0`) is employed to derive a simplified expression.
- Lemma `SUM_EQ` is used to separate out the terms used in the summation from `0` to `n`.
- Arithmetic rules and theorems such as `EVEN_ADD`, `EVEN_MULT`, `ARITH_EVEN`, `REAL_POW_NEG`, `REAL_POW_ONE` are used to simplify even and odd terms.
- The theorem `REAL_LE_MUL2` and `REAL_LE_RMUL` are then used.
- Bounding `sin` and `cos` between `-1` and `1` using `SIN_BOUND` and `COS_BOUND` provides the required bounds on the error term.

### Mathematical insight
The theorem provides an explicit error bound for the Maclaurin series approximation of the sine function. This is a fundamental result in real analysis and numerical analysis, allowing for accurate approximations of `sin x` using a finite number of terms.

### Dependencies
- `MCLAURIN_ALL_LE`
- `DIVISION`
- `ADD1`
- `ADD_ASSOC`
- `MOD_MULT_ADD`
- `SIN_0`
- `COS_0`
- `REAL_NEG_0`
- `EVEN_ADD`
- `EVEN_MULT`
- `ARITH_EVEN`
- `real_div`
- `REAL_MUL_LZERO`
- `DIV_MULT`
- `REAL_POW_NEG`
- `REAL_POW_ONE`
- `REAL_ABS_MUL`
- `REAL_INV_MUL`
- `REAL_LE_MUL2`
- `REAL_ABS_POS`
- `REAL_MUL_LID`
- `REAL_ABS_INV`
- `REAL_ABS_NUM`
- `REAL_LE_RMUL`
- `REAL_LE_INV_EQ`
- `REAL_POS`
- `SIN_BOUND`
- `COS_BOUND`
- `REAL_ABS_POW`
- `REAL_LE_REFL`
- `MOD_0`
- `ARITH_EQ`

### Porting notes (optional)
Porting this theorem requires careful attention to the definitions of summation, division, and real arithmetic, which may vary between proof assistants. The use of tactic-specific HOL Light constructs like `ONCE_DEPTH_CONV` or `EXPAND_CASES_CONV` indicates reliance on HOL Light's reduction and rewriting engine; these steps may require manual expansion or alternative automation strategies in other systems. The manipulation of modular arithmetic and the case splitting on `m MOD 4` indicates an area where specific arithmetic reasoning capabilities will be needed.


---

## COT_HALF_TAN

### Name of formal statement
COT_HALF_TAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_HALF_TAN = prove
 (`~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) - tan(pi * x / &2)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[cot; tan] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN `pi * x = &2 * pi * x / &2`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = (a * c) * b`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ABBREV_TAC `y = pi * x / &2` THEN
  REWRITE_TAC[COS_DOUBLE; SIN_DOUBLE] THEN
  SUBGOAL_THEN `~(sin y = &0) /\ ~(cos y = &0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[SIN_ZERO; COS_ZERO; real_div] THEN
    CONJ_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b * c = d) <=> (b * a * c = d)`] THEN
    SIMP_TAC[GSYM REAL_MUL_LNEG; REAL_EQ_MUL_RCANCEL; REAL_ENTIRE;
             REAL_INV_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LT_IMP_NZ;
             PI_POS] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(CHOOSE_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `abs`) o
      CONJUNCT2)) THEN
    UNDISCH_TAC `~(integer x)` THEN
    SIMP_TAC[integer; REAL_ABS_NEG; REAL_ABS_NUM; NOT_EXISTS_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&2 * sin y * cos y` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
    `(h * (c * s' - s * c')) * t * s * c =
     (t * h) * (c * c * s * s' - s * s * c * c')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID; REAL_POW_2]);;
```

### Informal statement
For all real numbers `x`, if `x` is not an integer, then the cotangent of `pi` times `x` is equal to one-half times the difference between the cotangent of `pi` times `x` divided by 2 and the tangent of `pi` times `x` divided by 2.

### Informal sketch
The proof demonstrates the identity relating `cot(pi * x)` to `cot(pi * x / 2)` and `tan(pi * x / 2)` under the condition that `x` is not an integer.

- The proof starts by simplifying the expression `&1 / &2 * (cot(pi * x / &2) - tan(pi * x / &2))` using algebraic manipulations and rewriting with the definitions of `cot` and `tan` in terms of `sin` and `cos`.
- A subgoal `pi * x = &2 * pi * x / &2` is introduced and proved to facilitate the use of double angle formulas.
- An abbreviation `y = pi * x / &2` is introduced for brevity. The double angle formulas for `cos` and `sin` are applied: `COS_DOUBLE` and `SIN_DOUBLE`.
- A subgoal `~(sin y = &0) /\ ~(cos y = &0)` is introduced and discharged using the assumption `~(integer x)` along with properties of integers, real numbers, `sin`, `cos`, and `pi`. This ensures that the cotangent and tangent functions are well-defined.
- The main goal is then simplified using `REAL_EQ_RCANCEL_IMP` to cancel out the common denominator, followed by algebraic manipulations and simplification to arrive at the desired equality.

### Mathematical insight
This theorem provides a formula for expressing the cotangent of an angle in terms of the cotangent and tangent of half that angle. This is a trigonometric identity that can be useful in simplifying expressions or solving equations involving trigonometric functions. The non-integer constraint on `x` is crucial to ensure the well-definedness of the cotangent and tangent functions in the formula.

### Dependencies
- `real_div`
- `REAL_ADD_RDISTRIB`
- `REAL_ADD_LDISTRIB`
- `REAL_MUL_LID`
- `cot`
- `tan`
- `REAL_MUL_RID`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `COS_DOUBLE`
- `SIN_DOUBLE`
- `SIN_ZERO`
- `COS_ZERO`
- `REAL_MUL_LNEG`
- `REAL_EQ_MUL_RCANCEL`
- `REAL_ENTIRE`
- `REAL_INV_EQ_0`
- `REAL_LT_IMP_NZ`
- `PI_POS`
- `OR_EXISTS_THM`
- `TAUT` (for `a /\ b \/ a /\ c <=> a /\ (b \/ c)`)
- `integer`
- `REAL_ABS_NEG`
- `REAL_ABS_NUM`
- `NOT_EXISTS_THM`
- `REAL_EQ_RCANCEL_IMP`
- `REAL_DIV_RMUL`
- `REAL_MUL_RINV`
- `REAL_POW_2`

### Porting notes (optional)
The proof relies heavily on real arithmetic simplification and rewriting with trigonometric identities. A proof assistant with good support for these features will be helpful. The handling of the non-integer condition might also require attention, as different systems may have different ways of representing and reasoning about integers and real numbers.


---

## COT_HALF_POS

### Name of formal statement
COT_HALF_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_HALF_POS = prove
 (`~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) + cot(pi * (x + &1) / &2)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[cot; COS_ADD; SIN_ADD; COS_PI2; SIN_PI2] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_SUB_LZERO] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN `pi * x = &2 * pi * x / &2`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = (a * c) * b`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  ABBREV_TAC `y = pi * x / &2` THEN
  REWRITE_TAC[COS_DOUBLE; SIN_DOUBLE] THEN
  SUBGOAL_THEN `~(sin y = &0) /\ ~(cos y = &0)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN REWRITE_TAC[SIN_ZERO; COS_ZERO; real_div] THEN
    CONJ_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b * c = d) <=> (b * a * c = d)`] THEN
    SIMP_TAC[GSYM REAL_MUL_LNEG; REAL_EQ_MUL_RCANCEL; REAL_ENTIRE;
             REAL_INV_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LT_IMP_NZ;
             PI_POS] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(CHOOSE_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `abs`) o
      CONJUNCT2)) THEN
    UNDISCH_TAC `~(integer x)` THEN
    SIMP_TAC[integer; REAL_ABS_NEG; REAL_ABS_NUM; NOT_EXISTS_THM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&2 * sin y * cos y` THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
    `(h * c * s' + h * --s * c') * t * s * c =
     (t * h) * (c * c * s * s' - s * s * c * c')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_LID; REAL_POW_2]);;
```

### Informal statement
If `x` is not an integer, then `cot(pi * x)` is equal to `1/2 * (cot(pi * x / 2) + cot(pi * (x + 1) / 2))`.

### Informal sketch
The proof proceeds by rewriting the cotangent in terms of sines and cosines, and then using trigonometric identities to relate the cotangent of `pi * x` to the cotangents of `pi * x / 2` and `pi * (x + 1) / 2`. The main steps are as follows:

- Rewrite using the definition of `cot` in terms of `cos` and `sin`.
- Apply the angle addition formulas `COS_ADD` and `SIN_ADD`.
- Simplify using known values of `cos` and `sin` at `pi/2` (specifically `COS_PI2` and `SIN_PI2`).
- Show that `pi * x = 2 * pi * x / 2`.
- Introduce `y = pi * x / 2`.
- Apply double angle formulas `COS_DOUBLE` and `SIN_DOUBLE`.
- Prove the subgoal `~(sin y = 0) /\ ~(cos y = 0)` using the assumption `~(integer x)`. This ensures that we are not dividing by zero. This involves a case split, discharging the case where `x` is an integer, eventually using `integer`, `REAL_ABS_NEG`, `REAL_ABS_NUM`, and `NOT_EXISTS_THM`.
- Cancel `sin y * cos y` terms and simplify to reach the conclusion.

### Mathematical insight
This theorem expresses a relationship between the cotangent function at a point and the cotangent function at related points (specifically, at the half-angle points). It is an identity that relates the cotangent of an angle to the cotangents of its half angles. This kind of half-angle formula is useful in simplifying expressions, integrating functions, and solving trigonometric equations.

### Dependencies
- `real_div`
- `REAL_ADD_RDISTRIB`
- `REAL_ADD_LDISTRIB`
- `REAL_MUL_LID`
- `cot`
- `COS_ADD`
- `SIN_ADD`
- `COS_PI2`
- `SIN_PI2`
- `REAL_MUL_RZERO`
- `REAL_ADD_LID`
- `REAL_SUB_LZERO`
- `REAL_MUL_RID`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `COS_DOUBLE`
- `SIN_DOUBLE`
- `SIN_ZERO`
- `COS_ZERO`
- `REAL_EQ_MUL_RCANCEL`
- `REAL_ENTIRE`
- `REAL_INV_EQ_0`
- `REAL_LT_IMP_NZ`
- `PI_POS`
- `OR_EXISTS_THM`
- `integer`
- `REAL_ABS_NEG`
- `REAL_ABS_NUM`
- `NOT_EXISTS_THM`
- `REAL_EQ_RCANCEL_IMP`
- `REAL_DIV_RMUL`
- `REAL_MUL_RINV`
- `REAL_POW_2`


---

## COT_HALF_NEG

### Name of formal statement
COT_HALF_NEG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_HALF_NEG = prove
 (`~(integer x)
   ==> (cot(pi * x) = &1 / &2 * (cot(pi * x / &2) + cot(pi * (x - &1) / &2)))`,
  STRIP_TAC THEN ASM_SIMP_TAC[COT_HALF_POS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  SUBST1_TAC(REAL_ARITH `x + &1 = (x - &1) + &2`) THEN
  ABBREV_TAC `y = x - &1` THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_ADD_LDISTRIB] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[cot; SIN_ADD; COS_ADD; SIN_PI; COS_PI] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_SUB_RZERO] THEN
  REWRITE_TAC[real_div; REAL_MUL_RNEG; REAL_MUL_LNEG; REAL_INV_NEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; REAL_MUL_RID]);;
```
### Informal statement
For any real number `x` such that `x` is not an integer, the cotangent of `pi` times `x` is equal to `1/2 * (cot(pi * x / 2) + cot(pi * (x - 1) / 2))`.

### Informal sketch
The proof proceeds as follows:
- Start by applying `COT_HALF_POS` after stripping the assumptions and simplifying.
- Apply the function to the terms using `AP_TERM_TAC`.
- Use the equality `x + 1 = (x - 1) + 2` to rewrite the expression; this can be shown using real arithmetic.
- Introduce a variable `y` such that `y = x - 1`.
- Rewrite using identities related to division, distribution over addition, and then simplify.
- Apply identities involving multiplication by an inverse element, the multiplicative identity, and the relationship between a real number and its numeral representation, followed by arithmetic simplifications.
- Expand `cot` using its definition in terms of sine and cosine, and then apply trigonometric identities for angle addition (`SIN_ADD`, `COS_ADD`), as well as identities for sine and cosine of `pi` (`SIN_PI`, `COS_PI`).
- Simplify by applying identities related to multiplication and addition by zero, and subtraction by zero.
- Rewrite the expression using facts about division, multiplication and negation involving real numbers.
- Simplify by applying `REAL_NEG_NEG` and multiplication by the multiplicative identity `REAL_MUL_RID`.

### Mathematical insight
The theorem expresses a trigonometric identity that relates `cot(pi * x)` to the cotangent of `pi` times `x/2` and `pi` times `(x-1)/2`. It is a variant of the half-angle formula adapted to the `cot` function. The non-integer constraint is necessary because the cotangent function has singularities at integer multiples of `pi`.

### Dependencies
- `COT_HALF_POS`
- `real_div`
- `REAL_ADD_RDISTRIB`
- `REAL_ADD_LDISTRIB`
- `REAL_MUL_RINV`
- `REAL_MUL_RID`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `cot`
- `SIN_ADD`
- `COS_ADD`
- `SIN_PI`
- `COS_PI`
- `REAL_MUL_RZERO`
- `REAL_ADD_RID`
- `REAL_SUB_RZERO`
- `REAL_MUL_RNEG`
- `REAL_MUL_LNEG`
- `REAL_INV_NEG`
- `REAL_NEG_NEG`

### Porting notes (optional)
Care should be taken to ensure that the definitions of trigonometric functions like `cot`, `sin`, and `cos`, and related constants like `pi`, are consistent with HOL Light's definitions. The handling of real number arithmetic might also require careful attention, as different proof assistants may have different levels of automation for real number reasoning.


---

## COT_HALF_MULTIPLE

### Name of formal statement
COT_HALF_MULTIPLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_HALF_MULTIPLE = prove
 (`~(integer x)
   ==> !n. cot(pi * x) =
           sum(0,2 EXP n)
             (\k. cot(pi * (x + &k) / &2 pow n) +
                  cot(pi * (x - &k) / &2 pow n)) / &2 pow (n + 1)`,
  DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[EXP; real_pow; REAL_DIV_1; ADD_CLAUSES; REAL_POW_1] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC[real_div; REAL_ADD_RID; REAL_SUB_RZERO; GSYM REAL_MUL_2] THEN
    REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = b * a * c`] THEN
    SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `sum(0,2 EXP n)
       (\k. &1 / &2 * (cot (pi * (x + &k) / &2 pow n / &2) +
                       cot (pi * ((x + &k) / &2 pow n + &1) / &2)) +
            &1 / &2 * (cot (pi * (x - &k) / &2 pow n / &2) +
                       cot (pi * ((x - &k) / &2 pow n - &1) / &2))) /
    &2 pow (n + 1)` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN BINOP_TAC THENL
     [MATCH_MP_TAC COT_HALF_POS THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x + &k) / &2 pow n - &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
      MATCH_MP_TAC COT_HALF_NEG THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x - &k) / &2 pow n + &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; SUM_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  ONCE_REWRITE_TAC[real_div] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  BINOP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_pow; REAL_POW_ADD; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  SUBGOAL_THEN `!k. (x + &k) / &2 pow n + &1 = (x + &(2 EXP n + k)) / &2 pow n`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
    EXISTS_TAC `&2 pow n` THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES;
                 REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_RID; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REWRITE_TAC[REAL_ADD_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. (x - &k) / &2 pow n - &1 = (x - &(2 EXP n + k)) / &2 pow n`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
    EXISTS_TAC `&2 pow n` THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES;
                 REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_RID; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXP; MULT_2;
              GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM(CONJUNCT2 real_pow))] THEN
  REWRITE_TAC[SUM_ADD] THEN
  CONV_TAC(ONCE_DEPTH_CONV (ALPHA_CONV `j:num`)) THEN
  REWRITE_TAC[REAL_ADD_AC; ADD_AC]);;
```

### Informal statement
For any real number `x` such that `x` is not an integer, for any natural number `n`, the cotangent of `pi * x` is equal to the sum from `k = 0` to `2^n` of (`cot(pi * (x + k) / (2^n)) + cot(pi * (x - k) / (2^n))) / (2^(n + 1))`.

### Informal sketch
The theorem is proved by induction on `n`.

- Base case (`n = 0`): Simplify the sum using `REAL_SUM_CONV` and arithmetic facts to show that `cot(pi * x) = cot(pi * x)`.
- Inductive step: Assume the theorem holds for `n`.  We need to prove it for `n + 1`.
  - Use the inductive hypothesis.
  - Apply the identity `cot(2 * x) = 1/2 * (cot(x) + cot(x + pi/2))`. The HOL Light equivalents are `COT_HALF_POS` and `COT_HALF_NEG`. These are applied within the summation. The assumption `~(integer x)` is needed to apply these identities.
  - Simplify the summation by distributing the sum and combining terms using algebraic manipulations like `REAL_ADD_LDISTRIB`, `SUM_CMUL`, etc.
  - Offset the summation index using `SUM_OFFSET` to obtain `sum(0, 2^n) f(k) + sum(2^n, 2^(n+1)) f(k) = sum(0, 2^(n+1)) f(k)`.
  - Rewrite using arithmetic facts about real numbers, powers, and multiplication.

### Mathematical insight
The theorem expresses `cot(pi * x)` as a sum of cotangents of related values, where the number of terms in the sum doubles with each increment of `n`. This identity relates the cotangent function at a point to a sum of cotangent values at finer subdivisions of the interval. It suggests a recursive decomposition of the cotangent, which can be useful in various contexts, such as numerical analysis or special function theory.

### Dependencies
- `EXP`
- `real_pow`
- `REAL_DIV_1`
- `ADD_CLAUSES`
- `REAL_POW_1`
- `real_div`
- `REAL_ADD_RID`
- `REAL_SUB_RZERO`
- `REAL_MUL_2`
- `REAL_MUL_RINV`
- `REAL_MUL_RID`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `COT_HALF_POS`
- `COT_HALF_NEG`
- `REAL_DIV_LMUL`
- `REAL_POW2_CLAUSES`
- `REAL_LT_IMP_NZ`
- `integer`
- `REAL_INTEGER_CLOSURES`
- `REAL_ADD_LDISTRIB`
- `SUM_CMUL`
- `REAL_MUL_SYM`
- `REAL_MUL_ASSOC`
- `REAL_POW_ADD`
- `REAL_INV_MUL`
- `REAL_EQ_LCANCEL_IMP`
- `REAL_SUB_LDISTRIB`
- `MULT_2`
- `SUM_OFFSET`
- `SUM_ADD`

### Porting notes (optional)
- The proof relies heavily on rewriting and equational reasoning within summations.  Proof assistants with strong support for these techniques (e.g., via tactics like `rewrite`, `simp`, `field`, etc.) will likely be beneficial.  The precise names and properties of real number arithmetic lemmas may need adjustment based on the target system's standard library.
- The handling of the `integer` predicate and its interaction with real numbers may differ across systems.  Care must be taken to ensure compatibility when porting.


---

## COT_HALF_KNOPP

### Name of formal statement
COT_HALF_KNOPP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_HALF_KNOPP = prove
 (`~(integer x)
   ==> !n. cot(pi * x) =
           cot(pi * x / &2 pow n) / &2 pow n +
           sum(1,2 EXP n - 1)
             (\k. cot(pi * (x + &k) / &2 pow (n + 1)) +
                  cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1)`,
  DISCH_TAC THEN GEN_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SPEC `n:num` o MATCH_MP COT_HALF_MULTIPLE) THEN
  SUBGOAL_THEN `!f. sum(0,2 EXP n) f = f 0 + sum(1,2 EXP n - 1) f`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL
   [GEN_TAC THEN SUBGOAL_THEN `2 EXP n = 1 + (2 EXP n - 1)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [SIMP_TAC[ARITH_RULE `~(x = 0) ==> (1 + (x - 1) = x)`;
               EXP_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    REWRITE_TAC[SUM_1; REAL_ADD_AC]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RID; REAL_SUB_RZERO; GSYM REAL_MUL_2] THEN
  GEN_REWRITE_TAC LAND_CONV [real_div] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `(&2 * cot (pi * x / &2 pow n)) / &2 pow (n + 1) +
    sum(1,2 EXP n - 1)
       (\k. &1 / &2 * (cot (pi * (x + &k) / &2 pow n / &2) +
                       cot (pi * ((x + &k) / &2 pow n - &1) / &2)) +
            &1 / &2 * (cot (pi * (x - &k) / &2 pow n / &2) +
                       cot (pi * ((x - &k) / &2 pow n + &1) / &2))) /
    &2 pow (n + 1)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[] THEN BINOP_TAC THENL
     [MATCH_MP_TAC COT_HALF_NEG THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x + &k) / &2 pow n - &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
      MATCH_MP_TAC COT_HALF_POS THEN
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = &2 pow n * (x - &k) / &2 pow n + &k`
        (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [SIMP_TAC[REAL_DIV_LMUL; REAL_POW2_CLAUSES; REAL_LT_IMP_NZ] THEN
        REAL_ARITH_TAC;
        SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; SUM_CMUL] THEN
  ONCE_REWRITE_TAC[AC REAL_ADD_AC
   `(a + b) + (c + d) = (a + c) + (b + d)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SUM_ADD] THEN
  GEN_REWRITE_TAC (funpow 2 (LAND_CONV o RAND_CONV) o RAND_CONV)
    [SUM_REVERSE] THEN
  SUBGOAL_THEN `(2 EXP n - 1 + 2 * 1) - 1 = 2 EXP n` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(2 EXP n = 0)` MP_TAC THENL
     [REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
      SPEC_TAC(`2 EXP n`,`m:num`) THEN ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_ADD] THEN
  BINOP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[real_div; REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[LE_0; ADD_CLAUSES] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a = e) /\ (d = e) /\ (b = f) /\ (c = f)
    ==> ((a + b) + (c + d) = (e + f) * &2)`) THEN
  UNDISCH_TAC `k < 2 EXP n - 1 + 1` THEN
  SIMP_TAC[ARITH_RULE `~(p = 0) ==> (k < p - 1 + 1 <=> k < p)`;
           EXP_EQ_0; ARITH_EQ] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x. (x / &2 pow n + &1 = (x + &2 pow n) / &2 pow n) /\
                    (x / &2 pow n - &1 = (x - &2 pow n) / &2 pow n)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_POW2_CLAUSES; REAL_ADD_RDISTRIB;
             REAL_SUB_RDISTRIB; REAL_MUL_LID; REAL_DIV_RMUL;
             REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. x / &2 pow n / &2 = x / &2 pow (n + 1)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[REAL_POW_ADD; real_div; REAL_POW_1; REAL_INV_MUL;
                GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[LT_IMP_LE; GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_POW] THEN
  CONJ_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;
```

### Informal statement
If `x` is not an integer, then for all natural numbers `n`, the cotangent of `pi * x` equals the expression consisting of the cotangent of `pi * x / 2^n` divided by `2^n` plus the sum from 1 to `2^n - 1` of the cotangent of `pi * (x + k) / 2^(n + 1)` plus the cotangent of `pi * (x - k) / 2^(n + 1)`, all divided by `2^(n + 1)`.

### Informal sketch
The proof proceeds as follows:
- Start by discharging the assumption that `x` is not an integer and generalizing.
- Apply `COT_HALF_MULTIPLE` after specializing it to `n:num` and substituting into the first assumption. Specifically `COT_HALF_MULTIPLE` states:
`cot (pi * x) = cot (pi * x / &2) / &2 - cot (pi * (x / &2 + &1 / &2)) + cot (pi * (x / &2 - &1 / &2))`
- Transform the sum `sum(0, 2 EXP n) f` to `f 0 + sum(1, 2 EXP n - 1) f`.
 - Decompose `2 EXP n` into `1 + (2 EXP n - 1)`.
 - Simplify using arithmetic rules and rewrite with the sum of differences.
- Simplify using identities for addition, subtraction, multiplication, and division.
- Distribute addition and rewrite with the inverse of division.
- Perform the main step, which involves rewriting the goal using an equation. This step uses the trigonometric identity for `cot(2x)` and rearranges the summation. Introducing the equation and proving equality.
- Separate the equation into two parts using `CONJ_TAC`:
 - The first part focuses on manipulating the summation, exploiting the trigonometric identity `cot(-x) = -cot(x)`. This involves rewriting the summation bounds and applying the cotangent half-angle formulas (`COT_HALF_NEG` and `COT_HALF_POS`).
  - Prove the relevant equalities for applying the half angle formulas
 - The second part simplifies the expression using arithmetic identities, properties of real numbers, and summation rules such as distributing scalar multiplication over a sum. Reverse one of the sums in the expression.
- Show that  `(2 EXP n - 1 + 2 * 1) - 1 = 2 EXP n` which requires showing that `~(2 EXP n = 0)`.
 - Rewrite the sum using the scalar multiplication and prove that each factor equals the same value.
- Simplify further by rewriting using arithmetic rules, division properties, and simplification tactics.
- Prove the nested subgoals which include identities related to real division/exponents showing that `x / &2 pow n + &1 = (x + &2 pow n) / &2 pow n` and `x / &2 pow n / &2 = x / &2 pow (n + 1)`.
- Apply assumptions and arithmetic simplifications to complete the proof.

### Mathematical insight
This theorem provides a formula for `cot(pi * x)` in terms of a sum of cotangents evaluated at related points. This decomposition is related to the Knopp's theorem about the cotangent function and can be useful in various areas of analysis and number theory. The main idea is to iteratively apply the half-angle formula for the cotangent function.

### Dependencies
- `COT_HALF_MULTIPLE`
- `real_div`
- `REAL_ADD_RDISTRIB`
- `SUM_EQ`
- `COT_HALF_NEG`
- `COT_HALF_POS`
- `REAL_ADD_LDISTRIB`
- `SUM_CMUL`
- `SUM_ADD`
- `SUM_REVERSE`
- `EXP_EQ_0`
- `LE_0`
- `ADD_CLAUSES`
- `REAL_MUL_SYM`
- `real_div`
- `REAL_MUL_LID`
- `REAL_EQ_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_ARITH`
- `integer`
- `REAL_INTEGER_CLOSURES`
- `LT_IMP_LE`
- `REAL_OF_NUM_SUB`
- `REAL_OF_NUM_POW`
### Porting notes (optional)
- The proof relies heavily on real arithmetic simplifications and summation manipulations.
- The use of `COT_HALF_POS` and `COT_HALF_NEG` assumes some trigonometric library.
- The tactic `REAL_ARITH_TAC` performs significant reasoning about inequalities and real arithmetic. Ensure that the target proof assistant has similar automation capabilities.


---

## SIN_SUMDIFF_LEMMA

### Name of formal statement
SIN_SUMDIFF_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_SUMDIFF_LEMMA = prove
 (`!x y. sin(x + y) * sin(x - y) = (sin x + sin y) * (sin x - sin y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH
   `(x + y) * (x - y) = x * x - y * y`] THEN
  REWRITE_TAC[SIN_ADD; real_sub; SIN_NEG; COS_NEG] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; GSYM REAL_MUL_ASSOC;
              REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH
   `(a = sx * sx + --(sy * sy)) <=> (a + sy * sy + --(sx * sx) = &0)`] THEN
  REWRITE_TAC[REAL_ARITH
   `a + --(sx * cy * cx * sy) + cx * sy * sx * cy + b = a + b`] THEN
  REWRITE_TAC[REAL_ARITH
   `(sx * cy * sx * cy + --(cx * sy * cx * sy)) + sy * sy + --(sx * sx) =
    (sy * sy + (sx * sx + cx * cx) * (cy * cy)) -
    (sx * sx + (sy * sy + cy * cy) * (cx * cx))`] THEN
  REWRITE_TAC[REWRITE_RULE[REAL_POW_2] SIN_CIRCLE; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_SUB_REFL]);;
```

### Informal statement
For all real numbers `x` and `y`,  `sin(x + y) * sin(x - y)` is equal to `(sin x + sin y) * (sin x - sin y)`.

### Informal sketch
The proof proceeds by expanding both sides of the equation and simplifying using trigonometric identities and algebraic manipulations to show their equivalence.
- Expand both sides using the sum and difference formulas for sine (`SIN_ADD`, `real_sub`, `SIN_NEG`, `COS_NEG`) and the distributive property of multiplication over addition.
- Rearrange terms using associativity and commutativity of addition and multiplication (`REAL_ADD_ASSOC`, `REAL_MUL_ASSOC`).
- Simplify using the identities `x * (-y) = -(x * y)` (`REAL_MUL_LNEG`, `REAL_MUL_RNEG`, `REAL_NEG_NEG`).
- Transform the equation into an equivalent form where both sides of the equation can be converted to `sin(y)^2 - sin(x)^2` to make use of `SIN_CIRCLE`: `sin(x)^2 + cos(x)^2 = 1`.
- Apply `SIN_CIRCLE` and simplify, demonstrating the equality.

### Mathematical insight
This theorem expresses a relationship between the sine of the sum and difference of two angles and the sines of the individual angles. It can be viewed as a trigonometric identity that simplifies certain expressions or facilitates calculations involving trigonometric functions.

### Dependencies
- `SIN_ADD`
- `real_sub`
- `SIN_NEG`
- `COS_NEG`
- `REAL_ADD_LDISTRIB`
- `REAL_ADD_RDISTRIB`
- `REAL_ADD_ASSOC`
- `REAL_MUL_ASSOC`
- `REAL_MUL_LNEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `REAL_POW_2`
- `SIN_CIRCLE`
- `REAL_MUL_LID`
- `REAL_SUB_REFL`
- REAL_ARITH


---

## SIN_ZERO_LEMMA

### Name of formal statement
SIN_ZERO_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_ZERO_LEMMA = prove
 (`!x. (sin(pi * x) = &0) <=> integer(x)`,
  REWRITE_TAC[integer; SIN_ZERO; EVEN_EXISTS] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c * d = c * b * a * d`] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_EQ; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
  SIMP_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB;
           REAL_EQ_MUL_LCANCEL; PI_POS; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[NOT_IMP; NOT_FORALL_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  REWRITE_TAC[REAL_MUL_RNEG; OR_EXISTS_THM] THEN
  REWRITE_TAC[REAL_ARITH
     `(abs(x) = a) <=> &0 <= a /\ ((x = a) \/ (x = --a))`] THEN
  REWRITE_TAC[REAL_POS]);;
```
### Informal statement
For all real numbers `x`, `sin(pi * x)` equals 0 if and only if `x` is an integer.

### Informal sketch
The proof proceeds as follows:
- Start with the equivalence `(sin(pi * x) = &0) <=> integer(x)`.
- Rewrite using the definitions of `integer` and `SIN_ZERO`, and `EVEN_EXISTS`.
- Rewrite `a /\ b <=> ~(a ==> ~b)`.
- Simplify using `LEFT_IMP_EXISTS_THM`.
- Rewrite using `GSYM REAL_OF_NUM_MUL`.
- Rewrite using `real_div`.
- Rewrite using associativity and commutativity of real multiplication.
- Simplify using `REAL_MUL_RINV`, `REAL_OF_NUM_EQ`, `ARITH_EQ`, and `REAL_MUL_RID`.
- Rewrite using `GSYM REAL_MUL_RNEG`.
- Simplify using the distributive laws for addition and subtraction over multiplication, a cancellation law, the positivity of pi, and the fact that a positive real number is non-zero.
- Rewrite using the negation of implication and the negation of forall.
- Rewrite by swapping the exists quantifier.
- Rewrite using `LEFT_EXISTS_AND_THM` and `EXISTS_REFL`.
- Rewrite using `REAL_MUL_RNEG` and `OR_EXISTS_THM`.
- Rewrite using the definition of absolute value for real numbers.
- Rewrite using `REAL_POS`.

### Mathematical insight
The theorem `SIN_ZERO_LEMMA` characterizes the zeroes of the sine function in terms of integer multiples of pi. Namely, `sin(pi * x) = 0` if and only if `x` is an integer. This is a fundamental property of the sine function and is used in many areas of mathematics.

### Dependencies
- Definitions: `integer`
- Theorems: `SIN_ZERO`, `EVEN_EXISTS`, `LEFT_IMP_EXISTS_THM`, `REAL_OF_NUM_MUL`, `real_div`, `REAL_MUL_AC`, `REAL_MUL_RINV`, `REAL_OF_NUM_EQ`, `ARITH_EQ`, `REAL_MUL_RID`, `REAL_MUL_RNEG`, `REAL_ADD_LDISTRIB`, `REAL_SUB_LDISTRIB`, `REAL_EQ_MUL_LCANCEL`, `PI_POS`, `REAL_LT_IMP_NZ`, `NOT_IMP`, `NOT_FORALL_THM`, `SWAP_EXISTS_THM`, `LEFT_EXISTS_AND_THM`, `EXISTS_REFL`, `OR_EXISTS_THM`, `REAL_ARITH` (specifically, the abs val property), `REAL_POS`.


---

## NOT_INTEGER_LEMMA

### Name of formal statement
NOT_INTEGER_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_INTEGER_LEMMA = prove
 (`~(x = &0) /\ abs(x) < &1 ==> ~(integer x)`,
  ONCE_REWRITE_TAC[GSYM REAL_ABS_ZERO] THEN
  CONV_TAC CONTRAPOS_CONV THEN SIMP_TAC[integer; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; REAL_OF_NUM_LT] THEN
  ARITH_TAC);;
```
### Informal statement
For all real numbers `x`, if `x` is not equal to 0 and the absolute value of `x` is less than 1, then `x` is not an integer.

### Informal sketch
The proof proceeds as follows:
- First, rewrite `abs(x) < &1` to `&0 < &1`, given `x = &0` via `REAL_ABS_ZERO` and `GSYM`.
- Then perform contraposition to change the goal to `integer x ==> x = &0 \/ ~(abs x < &1)`.
- Simplify using the definition of `integer` and `LEFT_IMP_EXISTS_THM`, resulting in the goal `!n. x = &n ==> x = &0 \/ ~(abs x < &1)`.
- Introduce the universal quantifier `n` and discharge the assumption `x = &n`.
- Rewrite the equalities using `REAL_OF_NUM_EQ` and `REAL_OF_NUM_LT` to convert numerical constants to real numbers.
- Finally, use `ARITH_TAC` to complete the proof by arithmetic reasoning, which can show that `x = &n` and `abs x < &1` implies `x = &0` is true for all integers `n`.

### Mathematical insight
This theorem states a basic property of real numbers: if a real number is strictly between -1 and 1, and is not 0, then it is not an integer. It's a useful lemma when reasoning about the properties of integers and real numbers.

### Dependencies
- `REAL_ABS_ZERO`
- `integer`
- `LEFT_IMP_EXISTS_THM`
- `REAL_OF_NUM_EQ`
- `REAL_OF_NUM_LT`


---

## NOT_INTEGER_DIV_POW2

### Name of formal statement
NOT_INTEGER_DIV_POW2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_INTEGER_DIV_POW2 = prove
 (`~(integer x) ==> ~(integer(x / &2 pow n))`,
  REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
  SUBGOAL_THEN `x = &2 pow n * x / &2 pow n`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
  THENL
   [SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES];
    SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]);;
```

### Informal statement
For any real number `x` and natural number `n`, if `x` is not an integer, then `x / (2^n)` is not an integer.

### Informal sketch
The proof proceeds as follows:
- First, rewrite the goal `~integer x ==> ~integer(x / &2 pow n)` to its contrapositive `integer(x / &2 pow n) ==> integer x`.
- Then introduce the subgoal `x = &2 pow n * x / &2 pow n`.
  - Use `GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)` on the subgoal.
- The proof is then split into two subgoals:
  - The first subgoal is proved by simplification using rewriting with `REAL_DIV_LMUL`, `REAL_LT_IMP_NZ`, and `REAL_POW2_CLAUSES`. These perform arithmetic simplifications and rewriting to show `x = &2 pow n * x / &2 pow n`
  - The second subgoal is proved by simplification using rewriting with `integer` and `REAL_INTEGER_CLOSURES`, which handle integer properties of real numbers. This uses the fact that if `x / &2 pow n` is an integer, then `&2 pow n * x / &2 pow n`, and hence `x` is an integer, via integer closure properties of multiplication.

### Mathematical insight
The theorem formalizes the intuition that if a real number is not an integer, then dividing it by a power of 2 will also result in a non-integer. This is because multiplying a non-integer by a fraction represented by the inverse of a power of 2 will generally preserve the fractional part, thus preventing it from becoming an integer.

### Dependencies
- Theorems: `TAUT`
- Definitions: `integer` and `REAL_INTEGER_CLOSURES`
- Lemmas: `REAL_DIV_LMUL`, `REAL_LT_IMP_NZ`, `REAL_POW2_CLAUSES`


---

## SIN_ABS_LEMMA

### Name of formal statement
SIN_ABS_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_ABS_LEMMA = prove
 (`!x. abs(x) < pi ==> (abs(sin x) = sin(abs x))`,
  GEN_TAC THEN ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[SIN_0; REAL_ABS_NUM] THEN
  REWRITE_TAC[real_abs] THEN ASM_CASES_TAC `&0 <= x` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `&0 < sin x`
     (fun th -> ASM_SIMP_TAC[th; REAL_LT_IMP_LE]) THEN
    MATCH_MP_TAC SIN_POS_PI THEN ASM_REWRITE_TAC[real_abs] THEN
    ASM_REWRITE_TAC[REAL_LT_LE];
    SUBGOAL_THEN `&0 < --(sin x)`
     (fun th -> SIMP_TAC[th; SIN_NEG;
                         REAL_ARITH `&0 < --x ==> ~(&0 <= x)`]) THEN
    REWRITE_TAC[GSYM SIN_NEG] THEN MATCH_MP_TAC SIN_POS_PI THEN
    ASM_SIMP_TAC[REAL_ARITH `~(x = &0) /\ ~(&0 <= x) ==> &0 < --x`]]);;
```
### Informal statement
For all real numbers `x`, if the absolute value of `x` is less than pi, then the absolute value of the sine of `x` is equal to the sine of the absolute value of `x`.

### Informal sketch
The proof proceeds by cases on the value of `x`:
- Case 1: `x = 0`. The goal `abs(sin 0) = sin(abs 0)` is simplified using the facts that `sin 0 = 0` and `abs 0 = 0`.
- Case 2: `x` is not `0`. We proceed by cases on the sign of `x`.
  - Case 2.1: `0 <= x`. We need to prove `abs(sin x) = sin x`. This holds if and only if `0 < sin x`. Using `abs x = x` if `0 <= x`, the goal becomes `abs(sin x) = sin x`. The subgoal `0 < sin x` is proven using `SIN_POS_PI`: `!x. 0 < x /\ x < pi ==> 0 < sin x`.
  - Case 2.2: It is not the case that `0 <= x`. We need to prove `abs(sin x) = sin(-x)`. The subgoal `0 < -sin x` is established using `SIN_NEG` (`!x. sin(-- x) = -- sin x`) and the fact that `0 < -x`. Hence the goal is reduced to `-(sin x) = sin(-x)`. Using `SIN_NEG` to rewrite `sin(-x)` to `-sin(x)` transforms the current goal to `-sin x = -sin x`, which is trivially true.

### Mathematical insight
The theorem states that when `abs(x) < pi`, the absolute value can be moved inside the sine function. This is due to the symmetry of the sine function around the origin and the fact that we are restricting the domain to be less than pi.  The symmetry of the sine function for `-pi < x < pi` about the origin can be succinctly expressed in this factored form.

### Dependencies
- `SIN_0`
- `REAL_ABS_NUM`
- `real_abs`
- `SIN_POS_PI`
- `SIN_NEG`
- `REAL_LT_IMP_LE`
- `REAL_LT_LE`
- `REAL_ARITH`


---

## SIN_EQ_LEMMA

### Name of formal statement
`SIN_EQ_LEMMA`

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_EQ_LEMMA = prove
 (`!x y. &0 <= x /\ x < pi / &2 /\ &0 <= y /\ y < pi / &2
         ==> ((sin x = sin y) <=> (x = y))`,
  SUBGOAL_THEN
   `!x y. &0 <= x /\ x < pi / &2 /\ &0 <= y /\ y < pi / &2 /\ x < y
          ==> sin x < sin y`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
    CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[REAL_ARITH `~(x = y) <=> x < y \/ y < x`] THEN
    ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sin`; `cos`; `x:real`; `y:real`] MVT_ALT) THEN
  ASM_REWRITE_TAC[DIFF_SIN; REAL_EQ_SUB_RADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_ARITH `x < a + x <=> &0 < a`] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  MATCH_MP_TAC COS_POS_PI2 THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_LT_TRANS]);;
```

### Informal statement
For all real numbers `x` and `y`, if `0 <= x` and `x < pi / 2` and `0 <= y` and `y < pi / 2`, then `sin x = sin y` if and only if `x = y`.

### Informal sketch
The theorem states that on the interval `[0, pi/2)`, the sine function is injective.
The proof proceeds as follows:
- First, handle the case `x < y` by assuming `!x y. &0 <= x /\ x < pi / &2 /\ &0 <= y /\ y < pi / &2 /\ x < y ==> sin x < sin y`.
- Then, consider the remaining case where `x` and `y` are not equal. By contraposition and rewriting `~(x = y)` as `x < y \/ y < x`, and using `ASM_MESON_TAC`, we complete this part.
- Next, use the Mean Value Theorem (`MVT_ALT`) to show that if `sin x = sin y`, then `x = y`.
- Apply `DIFF_SIN` which states that the derivative of `sin x` is `cos x`. Rewrite using `REAL_EQ_SUB_RADD`.
- Apply the Mean Value Theorem, yielding a `z` such that `sin y - sin x = (y - x) * cos z`. Choose that value `z` using `X_CHOOSE_THEN`.
- Simplify the inequality `x < a + x` to `0 < a`, where `a` corresponds to `y - x`.
- Use `REAL_LT_MUL` to show that `0 < (y - x) * cos z` implies `0 < y - x` and `0 < cos z`.
- Since `sin x = sin y`, if the premise is that `x` and `y` are within `[0, pi/2)`, then `cos z > 0` (by `COS_POS_PI2`).
- Use transitivity lemmas `REAL_LET_TRANS` and `REAL_LT_TRANS` and apply `ASM_MESON_TAC`.

### Mathematical insight
This theorem formalizes the well-known fact that the sine function is strictly increasing and therefore injective on the interval `[0, pi/2)`. This is a fundamental property used extensively in trigonometry and calculus.

### Dependencies
- `MVT_ALT` (Mean Value Theorem)
- `DIFF_SIN` (Derivative of sine)
- `REAL_EQ_SUB_RADD`
- `REAL_ARITH` (various real arithmetic lemmas)
- `REAL_LT_MUL`
- `COS_POS_PI2`
- `REAL_LET_TRANS`
- `REAL_LT_TRANS`
- `REAL_SUB_LT`

### Porting notes (optional)
The proof relies on the Mean Value Theorem, which may have slightly different formulations or names in other proof assistants. Ensure that the equivalent theorem is available. The real number arithmetic can also vary across systems. Specifically, pay attention to real number inequalities.


---

## KNOPP_TERM_EQUIVALENT

### Name of formal statement
KNOPP_TERM_EQUIVALENT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let KNOPP_TERM_EQUIVALENT = prove
 (`~(integer x) /\ k < 2 EXP n
   ==> ((cot(pi * (x + &k) / &2 pow (n + 1)) +
         cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1) =
        cot(pi * x / &2 pow (n + 1)) / &2 pow n /
        (&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 /
              sin(pi * x / &2 pow (n + 1)) pow 2))`,
  let lemma = prove
   (`~(x = &0) /\ (x * a = b) ==> (a = b / x)`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `x:real` THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL]) in
  REPEAT STRIP_TAC THEN SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_POW2_CLAUSES] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_POW_ADD] THEN
  REWRITE_TAC[REAL_POW_1; real_div] THEN
  GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC
   `((a * b') * c) * b * &2 = (&2 * a) * c * b * b'`] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_POW_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[real_div; REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
              REAL_ADD_RDISTRIB; REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_RID; GSYM real_div] THEN
  ABBREV_TAC `a = pi * x / &2 pow (n + 1)` THEN
  ABBREV_TAC `b = pi * &k / &2 pow (n + 1)` THEN
  SUBGOAL_THEN
   `~(sin(a + b) = &0) /\
    ~(sin a = &0) /\
    ~(sin(a - b) = &0) /\
    ~(&1 - sin(b) pow 2 / sin(a) pow 2 = &0)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT
      `(a /\ b /\ c) /\ (b ==> d) ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
      REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB] THEN
      REWRITE_TAC[SIN_ZERO_LEMMA] THEN REWRITE_TAC[real_div] THEN
      REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC[GSYM real_div] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC NOT_INTEGER_DIV_POW2 THEN
      ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `~(integer x)` THEN
        REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
        SUBGOAL_THEN `x = (x + &k) - &k`
         (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
        THENL
         [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
        UNDISCH_TAC `~(integer x)` THEN
        REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
        SUBGOAL_THEN `x = (x - &k) + &k`
         (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
        THENL
         [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM `( * ) (sin(a) pow 2)`) THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_POW_EQ_0; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(a * a = b * b) <=> ((a + b) * (a - b) = &0)`] THEN
    REWRITE_TAC[GSYM SIN_SUMDIFF_LEMMA] THEN
    REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[SIN_ZERO_LEMMA] THEN
    REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THEN
    MATCH_MP_TAC NOT_INTEGER_DIV_POW2 THENL
     [UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = (x + &k) - &k`
       (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
      UNDISCH_TAC `~(integer x)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      SUBGOAL_THEN `x = (x - &k) + &k`
       (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
      THENL
       [REAL_ARITH_TAC; SIMP_TAC[integer; REAL_INTEGER_CLOSURES]]];
    ALL_TAC] THEN
  REWRITE_TAC[cot; TAN_ADD; real_sub] THEN REWRITE_TAC[GSYM real_sub] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `sin(a + b)` THEN
  ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `sin(a - b)` THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a * (b + c * d) = a * b + c * a * d`] THEN
  ASM_SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
  EXISTS_TAC `&1 - sin(b) pow 2 / sin(a) pow 2` THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a * b * c * da = b * c * a * da`] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL] THEN
  MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN EXISTS_TAC `sin(a) pow 2` THEN
  ASM_REWRITE_TAC[REAL_POW_2; REAL_ENTIRE] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `((sa * sa) * (&1 - sb2 * sa' * sa') * others =
     (sa * sa) * v * w * x * y * sa') =
    (others * (sa * sa - sb2 * (sa * sa') * (sa * sa')) =
     sa * v * w * x * y * sa * sa')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID; REAL_MUL_RID] THEN
  SUBGOAL_THEN `sin(a - b) * cos(a + b) + sin(a + b) * cos(a - b) =
                sin(&2 * a)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM SIN_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SIN_DOUBLE] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ARITH
   `sa * samb * sapb * &2 * ca = (&2 * sa * ca) * samb * sapb`] THEN
  AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[SIN_SUMDIFF_LEMMA] THEN REAL_ARITH_TAC);;
```

### Informal statement
Given that `x` is not an integer and `k` is less than `2^n`, then
```
(cot(pi * (x + k) / (2^(n + 1))) + cot(pi * (x - k) / (2^(n + 1)))) / (2^(n + 1))
```
is equal to
```
cot(pi * x / (2^(n + 1))) / (2^n) / (1 - (sin(pi * k / (2^(n + 1))))^2 / (sin(pi * x / (2^(n + 1))))^2)
```

### Informal sketch
The proof establishes an equality involving cotangent and sine functions, under the assumption that `x` is not an integer and `k < 2^n`. The proof proceeds by simplification and rewriting using trigonometric identities and algebraic manipulations.

- The proof starts by stripping the theorem and simplifying using `REAL_EQ_LDIV_EQ` and `REAL_POW2_CLAUSES`.
- Rewrite using power rules (`REAL_POW_ADD`, `REAL_POW_1`).
- Applies AC rules to rearrange terms involving multiplication (`AC REAL_MUL_AC`).
- Simplifies using identities and arithmetic (`REAL_MUL_RINV`, `REAL_POW_EQ_0`, `REAL_OF_NUM_EQ`, `ARITH_EQ`).
- Distributes and simplifies using `REAL_ADD_LDISTRIB`, `REAL_SUB_LDISTRIB`, `REAL_ADD_RDISTRIB`, `REAL_SUB_RDISTRIB`, `REAL_MUL_RID`.
- Abbreviates `pi * x / &2 pow (n + 1)` to `a` and `pi * &k / &2 pow (n + 1)` to `b`.
- Establishes the subgoal `~(sin(a + b) = &0) /\ ~(sin a = &0) /\ ~(sin(a - b) = &0) /\ ~(&1 - sin(b) pow 2 / sin(a) pow 2 = &0)`.
- Proves the subgoal by splitting it into conjuncts and handling each conjunct separately. The proof uses `NOT_INTEGER_DIV_POW2` and the assumption `~(integer x)` to show `sin(a)`, `sin(a+b)`, and `sin(a-b)` are non-zero.
- Simplifies the main goal with `cot` expansion, tangent addition (`TAN_ADD`), and algebraic manipulations.
- Applies `REAL_EQ_LCANCEL_IMP` multiple times to cancel terms.
- Applies trigonometric identities like `SIN_SUMDIFF_LEMMA` and `SIN_DOUBLE` to simplify the expression.
- Proves `sin(a - b) * cos(a + b) + sin(a + b) * cos(a - b) = sin(&2 * a)` by rewriting and using `SIN_ADD`.
- Concludes the proof by further algebraic simplification and arithmetic reasoning.

### Mathematical insight
The theorem establishes a trigonometric identity useful in the analysis of certain sums involving cotangent functions. The condition `~(integer x)` ensures that the sine terms in the denominator are non-zero. Also, `k < 2 EXP n` prevents certain singularities. This kind of identity might show up in Fourier or number theoretic analysis.

### Dependencies
- `REAL_EQ_LCANCEL_IMP`
- `REAL_EQ_LDIV_EQ`
- `REAL_POW2_CLAUSES`
- `REAL_POW_ADD`
- `REAL_POW_1`
- `REAL_MUL_RINV`
- `REAL_POW_EQ_0`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `real_div`
- `REAL_ADD_LDISTRIB`
- `REAL_SUB_LDISTRIB`
- `REAL_ADD_RDISTRIB`
- `REAL_SUB_RDISTRIB`
- `REAL_MUL_RID`
- `SIN_ZERO_LEMMA`
- `NOT_INTEGER_DIV_POW2`
- `integer`
- `REAL_INTEGER_CLOSURES`
- `REAL_SUB_0`
- `REAL_DIV_LMUL`
- `REAL_POW_2`
- `SIN_SUMDIFF_LEMMA`
- `REAL_ENTIRE`
- `DE_MORGAN_THM`
- `cot`
- `TAN_ADD`
- `SIN_DOUBLE`
- `SIN_ADD`

### Porting notes (optional)
- The proof makes extensive use of real arithmetic rewriting and simplification. Other proof assistants may require more explicit guidance with respect to field and ring axioms.
- The `ABBREV_TAC` calls are used to introduce abbreviations for readability and manageability in HOL Light. These need to be manually expanded or replicated using similar abbreviation mechanisms in other systems.
- The tactic `GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]` applies theorem `th` to the randrand of the current goal, one may benefit from having a similar application control in another proof assistant.


---

## SIN_LINEAR_ABOVE

### Name of formal statement
SIN_LINEAR_ABOVE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_LINEAR_ABOVE = prove
 (`!x. abs(x) < &1 ==> abs(sin x) <= &2 * abs(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `2`] MCLAURIN_SIN) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[real_pow; REAL_POW_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; REAL_MUL_LID; REAL_POW_1; REAL_ADD_LID] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(a) <= abs(x) ==> abs(s - x) <= a ==> abs(s) <= &2 * abs(x)`) THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC; REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ABS_ABS] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * &1` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```
### Informal statement
For all real numbers `x`, if the absolute value of `x` is less than 1, then the absolute value of `sin(x)` is less than or equal to 2 times the absolute value of `x`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal.
- Apply the McLaurin series expansion of `sin x`, instantiated with `x` and `2`.
- Simplify the resulting sum.
- Rewrite using `real_pow` and `REAL_POW_1`.
- Reduce the resulting expression.
- Rewrite using several identities including `REAL_DIV_1`, `REAL_MUL_LID`, `REAL_POW_1`, `REAL_ADD_LID`.
- Use a real arithmetic tactic with the hypothesis `abs(a) <= abs(x) ==> abs(s - x) <= a ==> abs(s) <= &2 * abs(x)`.
- Rewrite using `REAL_POW_2`, `REAL_MUL_ASSOC`, and `REAL_ABS_MUL`.
- Rewrite using `REAL_ABS_ABS`.
- Rewrite, moving the multiplicative identity to the right.
- Apply `REAL_LE_RMUL`, after rewriting with `REAL_ABS_POS`.
- Reduce the expression.
- Apply `REAL_LE_TRANS`, and prove the existence of `&1 / &2 * &1`.
- Split the goal into two subgoals and reduce the second subgoal.
- Apply `REAL_LE_LMUL` and simplify with `REAL_LT_IMP_LE`.
- Reduce the expression.

### Mathematical insight
The theorem `SIN_LINEAR_ABOVE` provides a linear upper bound for the absolute value of the sine function in the interval `(-1, 1)`. This is a useful estimate for bounding errors and proving convergence results, particularly for values of `x` near zero where the linear approximation of `sin(x)` by `x` is accurate. The constant 2 is not tight but is sufficient for many applications and simplifies the proof.

### Dependencies
- Theorems: `MCLAURIN_SIN`, `REAL_ARITH`, `REAL_LE_TRANS`, `REAL_LT_IMP_LE`, `REAL_LE_RMUL`, `REAL_LE_LMUL`
- Definitions: `real_pow`, `GSYM REAL_MUL_LID`, `REAL_ABS_POS`
- Other: `REAL_POW_1`, `REAL_DIV_1`, `REAL_MUL_LID`, `REAL_ADD_LID`, `REAL_POW_2`, `REAL_MUL_ASSOC`, `REAL_ABS_MUL`, `REAL_ABS_ABS`


---

## SIN_LINEAR_BELOW

### Name of formal statement
SIN_LINEAR_BELOW

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_LINEAR_BELOW = prove
 (`!x. abs(x) < &2 ==> abs(sin x) >= abs(x) / &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `3`] MCLAURIN_SIN) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[real_pow; REAL_POW_1] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; REAL_MUL_LID; REAL_POW_1; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
  SIMP_TAC[real_ge; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&3 * abs(a) <= &2 * abs(x)
    ==> abs(s - x) <= a ==> abs(x) <= abs(s) * &3`) THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_ABS; REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(LAND_CONV(RAND_CONV(RAND_CONV num_CONV))) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[REAL_ABS_POS; REAL_LT_IMP_LE]);;
```

### Informal statement
For all real numbers `x`, if the absolute value of `x` is less than 2, then the absolute value of `sin x` is greater than or equal to the absolute value of `x` divided by 3.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal.
- Apply the McLaurin series expansion for `sin x` (`MCLAURIN_SIN`) with specialization for `x` and `3`.
- Simplify the summation in the McLaurin expansion using `REAL_SUM_CONV`.
- Rewrite using `real_pow` and `REAL_POW_1` to prepare for reduction.
- Perform arithmetic reductions using conversion tactics (`NUM_REDUCE_CONV`, `REAL_RAT_REDUCE_CONV`).
- Use algebraic simplifications (`REAL_DIV_1`, `REAL_MUL_LID`, `REAL_POW_1`, `REAL_ADD_LID`, `REAL_MUL_LZERO`, `REAL_ADD_RID`).
- Simplify using `real_ge`, `REAL_LE_LDIV_EQ`, `REAL_OF_NUM_LT` and `ARITH` via `SIMP_TAC`.
- Apply a real arithmetic lemma regarding bounding differences and multiples.
- Simplify the absolute value expressions using rewriting (`REAL_ABS_MUL`, `REAL_ABS_POW`, `REAL_ABS_ABS`, `REAL_MUL_ASSOC`).
- Further reduce the goal using `REAL_RAT_REDUCE_CONV` and convert to numbers.
- Rewrite the equation with `REAL_MUL_SYM`, `real_pow`, and `GSYM REAL_MUL_ASSOC`.
- Apply `REAL_LE_LMUL` to rearrange terms, rewriting with `REAL_ABS_POS`.
- Simplify by rewriting with `real_div` and `REAL_MUL_LID` and `GSYM real_div`.
- Apply automatic simplification tactics again using `REAL_LE_LDIV_EQ`, `REAL_OF_NUM_LT` and `ARITH`.
- Transform via `GSYM REAL_POW_2` and apply `REAL_POW_LE2`.
- Apply assumptions to simplify final goal with `REAL_ABS_POS` and `REAL_LT_IMP_LE`.

### Mathematical insight
This theorem provides a lower bound for `|sin(x)|` in terms of `|x|` when `|x|` is small. It essentially states that `sin(x)` behaves roughly linearly near zero, and this linearity is bounded by a factor of 1/3. This is a useful estimate for arguments in which `x` is known to be small which is a recurring theme in analysis.

### Dependencies
- `MCLAURIN_SIN`
- `real_pow`
- `REAL_POW_1`
- `real_ge`
- `REAL_LE_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_ABS_MUL`
- `REAL_ABS_POW`
- `REAL_ABS_ABS`
- `REAL_MUL_ASSOC`
- `REAL_MUL_SYM`
- `REAL_LE_LMUL`
- `REAL_ABS_POS`
- `real_div`
- `REAL_MUL_LID`
- `GSYM real_div`
- `GSYM REAL_POW_2`
- `REAL_POW_LE2`
- `REAL_LT_IMP_LE`
- `ARITH`
- `REAL_DIV_1`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`
- `REAL_ADD_LID`


---

## KNOPP_TERM_BOUND_LEMMA

### Name of formal statement
KNOPP_TERM_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let KNOPP_TERM_BOUND_LEMMA = prove
 (`~(integer x) /\ k < 2 EXP n /\ &6 * abs(x) < &k
   ==> abs(a / (&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 /
                     sin(pi * x / &2 pow (n + 1)) pow 2))
       <= abs(a) / ((&k / (&6 * x)) pow 2 - &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
    SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  ONCE_REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LT2 THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    UNDISCH_TAC `&6 * abs(x) < &k` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC(TAUT `(b <=> a) ==> a ==> b`) THEN
    MATCH_MP_TAC REAL_LT_RDIV_EQ THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH; GSYM REAL_ABS_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x <= y ==> x - &1 <= abs(&1 - y)`) THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_DIV] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(abs(pi * &k / &2 pow (n + 1)) / &3) *
              inv(&2 * abs(pi * x / &2 pow (n + 1)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC
     `p * k * q' * k1 * k2 * p' * x' * q =
      k * (k1 * k2) * x' * (p * p') * (q * q')`] THEN
    SIMP_TAC[REAL_INV_INV; REAL_MUL_RINV; REAL_ABS_ZERO;
             REAL_LT_IMP_NZ; REAL_POW2_CLAUSES; PI_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ABS_DIV] THEN
  GEN_REWRITE_TAC RAND_CONV [real_div] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_DIV; REAL_LE_MUL;
           REAL_ABS_POS; REAL_POS] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM real_ge] THEN MATCH_MP_TAC SIN_LINEAR_BELOW THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM;
             REAL_LT_LDIV_EQ; REAL_POW2_CLAUSES] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `pi * &2 pow n` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LMUL_EQ; PI_POS; REAL_OF_NUM_POW; REAL_OF_NUM_LT];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_LE_RMUL_EQ; REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC(C MATCH_MP PI_APPROX_25_BITS (REAL_ARITH
     `abs(p - y) <= e ==> y + e <= a ==> p <= a`)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[GSYM REAL_ABS_NZ; SIN_ZERO_LEMMA] THEN
    ASM_SIMP_TAC[NOT_INTEGER_DIV_POW2] THEN
    MATCH_MP_TAC SIN_LINEAR_ABOVE THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM;
             REAL_LT_LDIV_EQ; REAL_POW2_CLAUSES] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&6)` THEN
    CONV_TAC (LAND_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(&k * pi)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
      SIMP_TAC[PI_POS; REAL_ARITH `&0 < x ==> &0 < abs x`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(&2 pow n * pi)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_ABS_POW; REAL_ABS_NUM;
                REAL_ABS_MUL; GSYM REAL_MUL_ASSOC] THEN
    SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC(C MATCH_MP PI_APPROX_25_BITS (REAL_ARITH
     `abs(p - y) <= e ==> abs y + e <= a ==> abs p <= a`)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;
```

### Informal statement
If `x` is not an integer, `k` is less than `2` to the power of `n`, and `6` times the absolute value of `x` is less than `k`, then the absolute value of `a` divided by (`1` minus (`sin(pi * k / (2` to the power of `(n + 1)`))`squared` divided by `sin(pi * x / (2` to the power of `(n + 1)`))`squared`)) is less than or equal to the absolute value of `a` divided by ((`k / (6 * x))` squared minus `1`).

### Informal sketch
The proof establishes an inequality between two real-valued expressions under certain conditions.

- First, the goal is stripped to introduce the assumptions into the hypothesis. We also assume that `x` is not zero to proceed.
- The initial goal is split into proving `~(x=&0)` and the main inequality.
    - The proof of `~(x = &0)` uses the assumption that `x` is not an integer. It applies the tautology `(~b ==> ~a) <=> (a ==> b)` and simplifies using `integer`, `REAL_ABS_NUM`, `REAL_OF_NUM_EQ`, and `GSYM EXISTS_REFL`.
- The absolute value of the division on the left-hand side of the main goal is rewritten as the division of absolute values. Then `real_div` is used and lemmas `REAL_LE_LMUL` and `REAL_ABS_POS` are applied. Using `REAL_LE_INV2`, the goal is reduced to proving that the denominator on the left-hand side, `(&k / (&6 * x)) pow 2 - &1`, is less than or equal to `&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 / sin(pi * x / &2 pow (n + 1)) pow 2`.
- We prove `&1 - (&k / (&6 * x)) pow 2 <= &0 .`
    - The lemma `REAL_SUB_LT` is used. The expression `REAL_POW2_ABS` is instantiated. The lemmas `REAL_ABS_DIV`, `REAL_ABS_MUL`, and `REAL_ABS_NUM` are applied. The goal is then reduced to proving `&1 <= (&k / (&6 * x)) pow 2`. Using the hypothesis `&6 * abs(x) < &k` and lemmas `REAL_LT_RDIV_EQ`, `REAL_LT_MUL`, `REAL_OF_NUM_LT`, and `REAL_ABS_NZ`.
- We prove `&1 - sin(pi * &k / &2 pow (n + 1)) pow 2 / sin(pi * x / &2 pow (n + 1)) pow 2 <= &1 - (&k / (&6 * x)) pow 2`.
    - First prove `&0 <= y ==> x - &1 <= abs(&1 - y)`.
    - The inequality involves bounding `sin(pi * k / (2^(n+1)))^2 / sin(pi * x / (2^(n+1)))^2` by `(k / (6x))^2`.
        - Apply `REAL_LE_SQUARE`.
        - `REAL_POW_DIV` and `REAL_POW2_ABS` are applied.Then lemma `REAL_POW_LE2` is used which simplifies to bounding `abs(sin(pi * k / (2^(n+1))) / sin(pi * x / (2^(n+1))))` by `abs(pi * k / (2^(n+1))) / (3 * abs(pi * x / (2^(n+1))))`.
        - The rest of the proof uses the inequalities `abs sin x >= 2/pi abs x` (SIN_LINEAR_ABOVE) and `sin x <= x` (SIN_LINEAR_BELOW) for small `x`.

### Mathematical insight
This lemma provides a bound on the term inside the Knopp's series. It shows how the convergence depends on `x` not being an integer, and on the relationship between `k`, `n`, and `x`. Essentially, it states that under certain conditions, the function inside the absolute value is bounded by another function (which is simpler and easier to analyze).

### Dependencies
- `integer`
- `REAL_ABS_NUM`
- `REAL_OF_NUM_EQ`
- `EXISTS_REFL`
- `REAL_ABS_DIV`
- `real_div`
- `REAL_LE_LMUL`
- `REAL_ABS_POS`
- `REAL_LE_INV2`
- `REAL_SUB_LT`
- `REAL_POW2_ABS`
- `REAL_ABS_MUL`
- `REAL_ABS_NUM`
- `REAL_POW_2`
- `REAL_POW_LT2`
- `REAL_OF_NUM_LE`
- `REAL_LT_RDIV_EQ`
- `REAL_LT_MUL`
- `REAL_OF_NUM_LT`
- `REAL_ABS_NZ`
- `SIN_LINEAR_BELOW`
- `REAL_POW_2`
- `REAL_LE_SQUARE`
- `REAL_POW_DIV`
- `REAL_POW_LE2`
- `SIN_LINEAR_ABOVE`
- `PI_APPROX_25_BITS`
- `SIN_ZERO_LEMMA`
- `NOT_INTEGER_DIV_POW2`
- `PI_POS`

### Porting notes (optional)
- The proof relies heavily on real number arithmetic and inequalities, and trigonometric inequalities (`SIN_LINEAR_BELOW`, `SIN_LINEAR_ABOVE`, `PI_APPROX_25_BITS`). Ensure these are available, or prove them first.
- The numerous calls to `REAL_ARITH` suggest using a similar tool in the target proof assistant for automatically discharging arithmetic goals.
- The proof makes heavy use of rewriting and simplification tactics for real number expressions, so ensure that the target system has similar capabilities.


---

## KNOPP_TERM_BOUND

### Name of formal statement
KNOPP_TERM_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let KNOPP_TERM_BOUND = prove
 (`~(integer x) /\ k < 2 EXP n /\ &6 * abs(x) < &k
   ==> abs((cot(pi * (x + &k) / &2 pow (n + 1)) +
            cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1))
       <= abs(cot(pi * x / &2 pow (n + 1)) / &2 pow n) *
          (&36 * x pow 2) / (&k pow 2 - &36 * x pow 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[KNOPP_TERM_EQUIVALENT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs(cot(pi * x / &2 pow (n + 1)) / &2 pow n) /
              ((&k / (&6 * x)) pow 2 - &1)` THEN
  ASM_SIMP_TAC[KNOPP_TERM_BOUND_LEMMA] THEN
  GEN_REWRITE_TAC LAND_CONV [real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_DIV] THEN AP_TERM_TAC THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&6 pow 2`)) THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN REWRITE_TAC[REAL_POW_DIV] THEN
  SUBGOAL_THEN `&0 < (&6 * x) pow 2`
   (fun th -> SIMP_TAC[th; REAL_EQ_RDIV_EQ; REAL_SUB_RDISTRIB;
                       REAL_MUL_LID; REAL_DIV_RMUL; REAL_LT_IMP_NZ]) THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LT THEN
  REWRITE_TAC[GSYM REAL_ABS_NZ; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  UNDISCH_TAC `~(integer x)` THEN
  REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
  SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL]);;
```
### Informal statement
Assume that `x` is not an integer, `k` is less than `2^n`, and `6 * abs(x)` is less than `k`. Then the absolute value of `(cot(pi * (x + k) / (2^(n+1))) + cot(pi * (x - k) / (2^(n+1)))) / (2^(n+1))` is less than or equal to `abs(cot(pi * x / (2^(n+1))) / (2^n)) * (36 * x^2) / (k^2 - 36 * x^2)`.

### Informal sketch
The proof proceeds by:
- Stripping the assumptions.
- Using `KNOPP_TERM_EQUIVALENT` to simplify the cotangent terms.
- Applying `REAL_LE_TRANS` with an intermediate term.
- Proving that this intermediate term is equal to `abs(cot(pi * x / (2^(n+1))) / (2^n)) /((k / (6 * x))^2 - 1)`. This simplification uses `KNOPP_TERM_BOUND_LEMMA`.
- Rewriting using distributivity of division over multiplication.
- Applying `REAL_LE_LMUL` and showing positivity of the absolute value term.
- Showing equality implies less than or equal.
- Rewriting `REAL_INV_DIV` and simplifying `6^2` to `36`.
- Rewriting `REAL_POW_MUL` and `REAL_POW_DIV`.
- Showing `0 < (6 * x)^2`.
- Using the fact that `x` is not an integer to discharge the assumptions that `x` is not zero, using `REAL_ABS_NZ`, `REAL_ENTIRE`, `REAL_OF_NUM_EQ` and `ARITH_EQ`.
- Discharging the assumption that `x` is not an integer.
- Tautology and simplification to finish the proof, using `integer`, `REAL_ABS_NUM`, `REAL_OF_NUM_EQ`, and `EXISTS_REFL`.

### Mathematical insight
This theorem provides an upper bound for a specific expression involving cotangent functions. The expression arises in the context of bounding terms in a sum related to number-theoretic functions. The assumptions ensure that the terms in the expression are well-defined and that the bound is meaningful. Such bounds play a crucial role in analytic number theory, where we often use complex analysis to study the distribution of prime numbers.

### Dependencies
- `KNOPP_TERM_EQUIVALENT`
- `REAL_LE_TRANS`
- `KNOPP_TERM_BOUND_LEMMA`
- `REAL_LE_LMUL`
- `REAL_ABS_POS`
- `REAL_EQ_IMP_LE`
- `REAL_INV_DIV`
- `REAL_RAT_REDUCE_CONV`
- `REAL_POW_MUL`
- `REAL_POW_DIV`
- `REAL_EQ_RDIV_EQ`
- `REAL_SUB_RDISTRIB`
- `REAL_MUL_LID`
- `REAL_DIV_RMUL`
- `REAL_LT_IMP_NZ`
- `REAL_POW2_ABS`
- `REAL_POW_LT`
- `REAL_ABS_NZ`
- `REAL_ENTIRE`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `integer`
- `REAL_ABS_NUM`
- `EXISTS_REFL`


---

## SUMMABLE_INVERSE_SQUARES_LEMMA

### Name of formal statement
SUMMABLE_INVERSE_SQUARES_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_INVERSE_SQUARES_LEMMA = prove
 (`(\n. inv(&(n + 1) * &(n + 2))) sums &1`,
  REWRITE_TAC[sums] THEN
  SUBGOAL_THEN
   `!n. sum(0,n) (\m. inv(&(m + 1) * &(m + 2))) = &1 - inv(&(n + 1))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [INDUCT_TAC THEN REWRITE_TAC[sum] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[ADD_CLAUSES] THEN
    REWRITE_TAC[REAL_ARITH `(&1 - a + b = &1 - c) <=> (b + c = a)`] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_LINV_UNIQ THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC; REAL_ADD_LDISTRIB] THEN
    SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH_RULE `~(n + 1 = 0)`] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH_RULE `SUC(n + 1) = n + 2`] THEN
    MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&(n + 2)` THEN
    SIMP_TAC[REAL_ADD_RDISTRIB; real_div; GSYM REAL_MUL_ASSOC; REAL_OF_NUM_EQ;
             REAL_MUL_LINV; ARITH_RULE `~(n + 2 = 0)`; REAL_MUL_LID;
             REAL_MUL_RID] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_SUB_RZERO] THEN
  MATCH_MP_TAC SEQ_SUB THEN REWRITE_TAC[SEQ_CONST] THEN
  MATCH_MP_TAC SEQ_INV0 THEN X_GEN_TAC `x:real` THEN
  X_CHOOSE_TAC `N:num` (SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[real_gt; GE] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH_RULE `a < b + 1 <=> a <= b`]);;
```

### Informal statement
The series defined by the function that maps a natural number `n` to the real number `1/((n+1)*(n+2))` is summable, and its sum is equal to 1. Formally, the sequence of partial sums converges to 1.

### Informal sketch
The proof proceeds as follows:

- First, rewrite the goal using definition of `sums`.
- Reduce the main goal to proving the following subgoal: for all natural numbers `n`, the sum from `m = 0` to `n` of `1/((m+1)*(m+2))` equals `1 - 1/(n+1)`.
- Prove this subgoal by induction on `n`.
    - Base case: Verify the equality for `n = 0`.
    - Inductive step : Assuming the equality holds for some `n`, prove that it holds for `n+1`. This involves rewriting using the definition of `sum`, performing arithmetic simplifications, and using the inductive hypothesis.
- Use this result to show the limit of the partial sums when n tends to infinity, is one. This part of the proof involves epsilon-delta reasoning from the definition of convergence of sequences.
    - Use `REAL_ARCH_SIMPLE`to find `N` such that for any x > 0, `1 / (N + 1) < x`.
    - Show that for all `n > N`, `|1 - (1 - 1/(n+1))| < x`

### Mathematical insight
The theorem demonstrates that the infinite series of inverse squares of the form `1/((n+1)*(n+2))` converges to 1. This is a standard result in real analysis and provides an explicit example of a convergent infinite series. The function `1/((n+1)*(n+2))` can be seen as a telescoping series which are known to converge if the terms approach zero.

### Dependencies
- Definitions:
    - `sums`
    - `sum`
- Theorems/Lemmas:
    - `ADD_CLAUSES`
    - `REAL_ARITH` `(&1 - a + b = &1 - c) <=> (b + c = a)`
    - `REAL_MUL_LINV_UNIQ`
    - `REAL_MUL_SYM`
    - `REAL_INV_MUL`
    - `REAL_MUL_ASSOC`
    - `REAL_ADD_LDISTRIB`
    - `REAL_MUL_RINV`
    - `REAL_OF_NUM_EQ`
    - `REAL_MUL_LID`
    - `REAL_EQ_RCANCEL_IMP`
    - `REAL_ADD_RDISTRIB`
    - `real_div`
    - `REAL_OF_NUM_ADD`
    - `REAL_MUL_LINV`
    - `REAL_MUL_RID`
    - `REAL_SUB_RZERO`
    - `SEQ_SUB`
    - `SEQ_CONST`
    - `SEQ_INV0`
    - `REAL_ARCH_SIMPLE`
    - `real_gt`
    - `GE`
    - `REAL_LET_TRANS`
    - `REAL_OF_NUM_LT`

### Porting notes (optional)
- The proof relies on induction and basic real arithmetic. Porting to other proof assistants like Coq or Lean should be relatively straightforward, provided the appropriate definitions and lemmas for real numbers and series are available.
- The tactic `ARITH_TAC` handles some arithmetic reasoning automatically. In other proof assistants, one might need to explicitly invoke decision procedures or tactics for linear arithmetic.
- The use of `REAL_ARCH_SIMPLE` suggests reliance on the Archimedean property of real numbers. Make sure that an equivalent axiom or theorem is available in the target proof assistant.


---

## SUMMABLE_INVERSE_SQUARES

### Name of formal statement
SUMMABLE_INVERSE_SQUARES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_INVERSE_SQUARES = prove
 (`summable (\n. inv(&n pow 2))`,
  MATCH_MP_TAC SUM_SUMMABLE THEN
  EXISTS_TAC `sum(0,2) (\n. inv(&n pow 2)) +
              suminf (\n. inv(&(n + 2) pow 2))` THEN
  MATCH_MP_TAC SER_OFFSET_REV THEN
  MATCH_MP_TAC SER_ACONV THEN MATCH_MP_TAC SER_COMPARA THEN
  EXISTS_TAC `\n. inv(&(n + 1) * &(n + 2))` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUMMABLE THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[SUMMABLE_INVERSE_SQUARES_LEMMA]] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_POW_2; REAL_INV_MUL; REAL_ABS_INV; REAL_ABS_NUM;
              REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC);;
```
### Informal statement
The series whose nth term is the inverse of `n` squared is summable. More formally, the sequence defined by the function that maps `n` to `1/(n^2)` is summable.

### Informal sketch
The proof proceeds as follows:
- Start by using the theorem `SUM_SUMMABLE` which states that if the tail of a series is summable then the whole series is summable.
- Then, show that the tail of the series, starting from index 2, is summable assuming the series whose `n`th term is `1/((n+2)^2)` is summable.
- The proof proceeds by showing that `1/((n+2)^2)` is absolutely convergent using `SER_ACONV` by comparing the series against a simpler series. The offset series theorem `SER_OFFSET_REV` is applied. Comparison is accomplished via `SER_COMPARA`.
- Provide a witness function: `\n. inv(&(n + 1) * &(n + 2))`, and show that the witness is summable .
- Split this goal into proving two facts, showing that the terms of the witness series are positive using `ALL_TAC` and showing that the tail of the series whose `n`th term is `1/((n+1)*(n+2))` is summable. The latter makes use of `SUMMABLE_INVERSE_SQUARES_LEMMA`.
- Finally, it remains to show that for all `n`, `inv(&(n + 2) pow 2) <= inv(&(n + 1) * &(n + 2))`. This is established by rewriting with `REAL_POW_2`, `REAL_INV_MUL`, `REAL_ABS_INV`, `REAL_ABS_NUM`, `REAL_ABS_MUL`, `REAL_LE_RMUL`, `REAL_LE_INV_EQ; REAL_POS`, `REAL_LE_INV2`, `REAL_OF_NUM_LT`, `REAL_OF_NUM_LE` and then by using `ARITH_TAC`.

### Mathematical insight
This theorem establishes that the series of inverse squares converges. This is a classic result in real analysis, often used as a benchmark for testing convergence of other series.

### Dependencies
- `SUM_SUMMABLE`
- `SER_OFFSET_REV`
- `SER_ACONV`
- `SER_COMPARA`
- `SUMMABLE_INVERSE_SQUARES_LEMMA`
- `REAL_POW_2`
- `REAL_INV_MUL`
- `REAL_ABS_INV`
- `REAL_ABS_NUM`
- `REAL_ABS_MUL`
- `REAL_LE_RMUL`
- `REAL_LE_INV_EQ`
- `REAL_POS`
- `REAL_LE_INV2`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_LE`

### Porting notes (optional)
When porting this theorem, ensure that the target proof assistant has adequate support for real number arithmetic and series convergence. The `ARITH_TAC` tactic is used heavily, so a good arithmetic decision procedure is necessary. The definitions and theorems in the dependencies will be required.


---

## SUMMABLE_INVERSE_POWERS

### Name of formal statement
SUMMABLE_INVERSE_POWERS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUMMABLE_INVERSE_POWERS = prove
 (`!m. 2 <= m ==> summable (\n. inv(&(n + 1) pow m))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SER_COMPAR THEN
  EXISTS_TAC `\m. inv (&(m + 1) pow 2)` THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    REWRITE_TAC[summable] THEN
    EXISTS_TAC
     `suminf (\m. inv (&m pow 2)) - sum(0,1) (\m. inv (&m pow 2))` THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] SER_OFFSET) THEN
    REWRITE_TAC[SUMMABLE_INVERSE_SQUARES]]);;
```
### Informal statement
For all natural numbers `m`, if `2 <= m`, then the sequence defined by the function that maps each natural number `n` to `1/((n + 1)^m)` is summable.

### Informal sketch
The proof demonstrates that the series of inverse powers, `1/((n+1)^m)`, is summable for `m >= 2`.

- The proof starts by reducing the problem to showing that `summable (\n. inv(&(n + 1) pow m))` for `2 <= m`.
- It leverages `SER_COMPAR`, a theorem stating a comparison test for series convergence.
- An existential instantiation is performed to show that for a specific m (in this case m=2) there exist a summable function.
- The goal is then to show that `abs(1/((n+1)^m)) <= 1/((n + 1)^2)` for all n.
- Absolute values are simplified.
- The proof then relies on showing `inv(&(n+1) pow m)` converges by comparing it to `inv(&(n+1) pow 2)`, which corresponds to the known convergent series of inverse squares.
- Exploiting `REAL_LE_INV2` and inequalities between real powers (`REAL_POW_LT`, `REAL_POW_MONO`), with `REAL_OF_NUM_LT` and `REAL_OF_NUM_LE` to relate natural numbers to reals, allows proving the key inequality within the comparison test
- Finally, it uses `SUMMABLE_INVERSE_SQUARES` to establish that the inverse square series is summable. A shift (`SER_OFFSET`) is used to match indices.

### Mathematical insight
This theorem is a standard result in real analysis, stating that the series of inverse powers `\sum_{n=1}^{\infty} 1/n^m` converges for `m > 1`. The HOL Light theorem proves it for `m >= 2` where m is a natural number. This is important because it establishes the convergence of a family of common series, which are very useful as comparison series for proving the convergence of other series.

### Dependencies
- `SER_COMPAR`
- `REAL_ABS_INV`
- `REAL_ABS_POW`
- `REAL_ABS_NUM`
- `REAL_LE_INV2`
- `REAL_POW_LT`
- `REAL_OF_NUM_LT`
- `ARITH_RULE`
- `REAL_POW_MONO`
- `REAL_OF_NUM_LE`
- `summable`
- `SUMMABLE_INVERSE_SQUARES`
- `RIGHT_IMP_FORALL_THM`
- `SER_OFFSET`

### Porting notes (optional)
- The tactic `ARITH_TAC` encapsulates some arithmetic reasoning; you need to unfold or replace it with equivalent steps in other proof assistants.
- The simplification is done by `SIMP_TAC`, ensure all the rewrite rules given to it are available or proved in the target prover.
- The theorem `SER_COMPAR` or an equivalent one about comparison tests for series is crucial for transplanting this proof.


---

## COT_TYPE_SERIES_CONVERGES

### Name of formal statement
COT_TYPE_SERIES_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_TYPE_SERIES_CONVERGES = prove
 (`!x. ~(integer x) ==> summable (\n. inv(&n pow 2 - x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SER_ACONV THEN MATCH_MP_TAC SER_COMPARA THEN
  EXISTS_TAC `\n. &2 / &n pow 2` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUMMABLE THEN
    EXISTS_TAC `&2 * suminf (\n. inv(&n pow 2))` THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC SER_CMUL THEN
    MATCH_MP_TAC SUMMABLE_SUM THEN
    REWRITE_TAC[SUMMABLE_INVERSE_SQUARES]] THEN
  MP_TAC(SPEC `&2 * abs x + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &n pow 2`
   (fun th -> SIMP_TAC[th; REAL_LE_RDIV_EQ])
  THENL
   [MATCH_MP_TAC REAL_POW_LT THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&2 * abs x + &1 <= &N` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_ABS_INV] THEN
  REWRITE_TAC[GSYM real_div] THEN
  SUBGOAL_THEN `&0 < abs(&n pow 2 - x)`
   (fun th -> SIMP_TAC[REAL_LE_LDIV_EQ; th])
  THENL
   [REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
    DISCH_TAC THEN
    SUBST1_TAC(REAL_ARITH `x = &n pow 2 - (&n pow 2 - x)`) THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    SIMP_TAC[integer; REAL_INTEGER_CLOSURES]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * abs(x) + &1 <= a ==> a <= &2 * abs(a - x)`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; EXP_2; LE_SQUARE_REFL];
    ASM_SIMP_TAC[REAL_POW_LE2; REAL_OF_NUM_LE; LE_0]]);;
```
### Informal statement
For all `x`, if `x` is not an integer, then the series whose `n`-th term is `1 / (n^2 - x)` is summable.

### Informal sketch
The proof shows that if `x` is not an integer, then the series  `Σ(1 / (n^2 - x))` converges. The central idea is to use the absolute convergence test for series (`SER_ACONV`) by comparing the given series to a known convergent series (the inverse square series `Σ(1/n^2)`).

- First, the absolute convergence test `SER_ACONV` and a comparison test `SER_COMPARA` are applied.
- An existential goal appears, requiring a comparison with the summable series `2 / n^2`, where `n` is a natural number.
- It is shown that the series `Σ(2 / n^2)` is summable by rewriting and using `SER_CMUL` and `SUMMABLE_INVERSE_SQUARES`.
- An `N` is found, such that for all `n > N`, `|1 / (n^2 - x)| <= 2 / n^2`.
  - A suitable `N` is chosen based on the Archimedean property `REAL_ARCH_SIMPLE`.
  - It is proven that for `n > N`, `0 < n^2` and `0 < |n^2 - x|`.
  - Relationships between `|x|`, `N`, and `n` are established, leading to the desired inequality.
- The non-integrality of `x` is used to show that `n^2 - x` is non-zero for any `n`, which ensures that the term `1 / (n^2 - x)` is well-defined.

### Mathematical insight
The theorem establishes the convergence of a specific type of series, where the terms are of the form `1 / (n^2 - x)`. The condition that `x` is not an integer is crucial because it prevents the denominator from becoming zero for any `n`. The series is shown to converge absolutely by comparing its terms to the terms of the convergent series `Σ(1/n^2)`. This result is useful in complex analysis when studying Mittag-Leffler's theorem.

### Dependencies
- `SER_ACONV`
- `SER_COMPARA`
- `SUM_SUMMABLE`
- `SER_CMUL`
- `SUMMABLE_SUM`
- `SUMMABLE_INVERSE_SQUARES`
- `REAL_ARCH_SIMPLE`
- `REAL_POW_LT`
- `REAL_LTE_TRANS`
- `REAL_OF_NUM_LE`
- `REAL_OF_NUM_POW`
- `REAL_ABS_INV`
- `REAL_ABS_NZ`
- `REAL_INTEGER_CLOSURES`
- `integer`
- `EXP_2`
- `LE_SQUARE_REFL`
- `REAL_POW_LE2`
- `LE_0`

### Porting notes (optional)
- The proof relies heavily on real analysis and comparison theorems for series convergence. Ensure that the target proof assistant has similar results available.
- The Archimedean property (`REAL_ARCH_SIMPLE`) is used to find a suitable `N`. This property is fundamental in real analysis and should be available in most proof assistants.
- The handling of real numbers and their properties (e.g., inequalities, absolute values) is crucial. Ensure that the target system has a well-developed real number theory.
- The tactic `TAUT` is used, which suggests the use of classical reasoning capabilities


---

## SIN_X_RANGE

### Name of formal statement
SIN_X_RANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_X_RANGE = prove
 (`!x. abs(sin(x) - x) <= abs(x) pow 2 / &2`,
  GEN_TAC THEN
  MP_TAC(SPECL [`x:real`; `2`] MCLAURIN_SIN) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[ARITH; REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_DIV_1; REAL_POW_1; REAL_MUL_LID] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
For all real numbers x, the absolute value of the difference between `sin(x)` and `x` is less than or equal to the absolute value of `x` squared, divided by 2.

### Informal sketch
The proof proceeds as follows:
- Start with the goal `!x. abs(sin(x) - x) <= abs(x) pow 2 / &2`.
- Instantiate the general Maclaurin series expansion for `sin(x)` at `x` and `2`. This introduces a sum over the series.
- Convert the sum using `REAL_SUM_CONV`.
- Simplify the resulting expression using arithmetic rules (`ARITH`), specifically applying rules to remove multiplications by zero (`REAL_MUL_LZERO`) and identities for real addition (`REAL_ADD_LID`, `REAL_ADD_RID`).
- Perform numeric reduction using `NUM_REDUCE_CONV` to simplify numerical expressions.
- Reduce rational expressions utilizing `REAL_RAT_REDUCE_CONV`.
- Apply rewriting rules to simplify real division (`REAL_DIV_1`), powers (`REAL_POW_1`), and remove identity multipliers (`REAL_MUL_LID`).
- Simplify real division rewriting with `real_div` and remove identity multipliers (`REAL_MUL_LID`) again.
- Use algebraic commutativity rules `REAL_MUL_AC` to arrange terms.

### Mathematical insight
This theorem provides an upper bound on the error when approximating `sin(x)` by `x`. It leverages the Maclaurin series expansion of `sin(x)` and then simplifies to obtain the `abs(x)^2 / 2` bound. This is a crucial estimate in real analysis.

### Dependencies
- `MCLAURIN_SIN`
- `ARITH`
- `REAL_MUL_LZERO`
- `REAL_ADD_LID`
- `REAL_ADD_RID`
- `REAL_DIV_1`
- `REAL_POW_1`
- `REAL_MUL_LID`
- `real_div`
- `REAL_MUL_AC`

### Porting notes (optional)
- The main challenge in porting this theorem is likely the availability and automation of Maclaurin series expansions. Ensure that the target proof assistant has facilities for handling such expansions, or provide the expansion manually.
- Arithmetic simplification tactics might behave differently in other proof assistants. Review each step.


---

## SIN_X_X_RANGE

### Name of formal statement
SIN_X_X_RANGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_X_X_RANGE = prove
 (`!x. ~(x = &0) ==> abs(sin(x) / x - &1) <= abs(x) / &2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_MUL; GSYM REAL_ABS_NZ] THEN
  ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM REAL_POW_2; SIN_X_RANGE; GSYM real_div]);;
```

### Informal statement
For all real numbers `x`, if `x` is not equal to 0, then the absolute value of (`sin(x) / x` minus 1) is less than or equal to the absolute value of `x` divided by 2.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the goal, introducing the assumption `x` is non-zero.
- Cancel `REAL_LE_LCANCEL_IMP` against the goal using `MATCH_MP_TAC`. This transforms the goal so that it involves only absolute values and eliminates an implication.
- Introduce an existential variable `abs(x)` using `EXISTS_TAC`.
- Rewrite using associativity and commutativity of absolute value: `GSYM REAL_ABS_MUL; GSYM REAL_ABS_NZ`
- Simplify using distribution, `REAL_SUB_LDISTRIB; REAL_DIV_LMUL`
- Rewrite using real division, associativity and the right identity: `real_div; REAL_MUL_ASSOC; REAL_MUL_RID`
- Rewrite using `REAL_POW_2`, `SIN_X_RANGE` and division: `GSYM REAL_POW_2; SIN_X_RANGE; GSYM real_div`

### Mathematical insight
This theorem provides a bound on the approximation of `sin(x)/x` by 1.  Specifically, it states that for non-zero `x`, the difference between  `sin(x)/x` and 1 is bounded by `abs(x)/2`. This result is useful in analysis for evaluating limits and approximating functions.

### Dependencies
- `REAL_LE_LCANCEL_IMP`
- `REAL_ABS_MUL`
- `REAL_ABS_NZ`
- `REAL_SUB_LDISTRIB`
- `REAL_DIV_LMUL`
- `real_div`
- `REAL_MUL_ASSOC`
- `REAL_MUL_RID`
- `REAL_POW_2`
- `SIN_X_RANGE`


---

## SIN_X_LIMIT

### Name of formal statement
SIN_X_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIN_X_LIMIT = prove
 (`((\x. sin(x) / x) tends_real_real &1)(&0)`,
  REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN EXISTS_TAC `e:real` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(x) / &2` THEN
  ASM_SIMP_TAC[SIN_X_X_RANGE; REAL_ABS_NZ] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `abs(x) < e` THEN REAL_ARITH_TAC);;
```
### Informal statement
The function `sin(x) / x` tends to 1 as x tends to 0 in the real numbers.

### Informal sketch
The proof demonstrates that `sin(x) / x` approaches 1 as `x` approaches 0. The proof proceeds as follows:
- Start by rewriting with the definition of `LIM`, presumably a definition of limits in HOL Light.
- Assume an arbitrary real number `e` greater than 0, representing the desired level of closeness to the limit, and aim to show the existence of a `delta` such that when `abs(x)` is less than `delta`, then `abs(sin(x) / x - 1)` is less than `e`.
- Rewrite `abs(1 - 1)` to `0`.
- Provide a candidate for `delta`, namely `e`.
- Assume that `abs(x)` is less than `e`.
- Apply `REAL_LET_TRANS` to leverage the fact that `abs(sin(x) / x - 1) <= abs(x) / 2` (from `SIN_X_X_RANGE`).
- Choose `abs(x) / 2` as the required value and use `SIN_X_X_RANGE` , `REAL_ABS_NZ`, `REAL_LT_LDIV_EQ`, `REAL_OF_NUM_LT`, and `ARITH` to eventually show that `abs(sin(x) / x - 1) < e`. Conclude.

### Mathematical insight
This theorem establishes a fundamental limit in calculus, showing that the ratio of `sin(x)` to `x` approaches 1 as `x` gets arbitrarily close to 0. This limit is crucial for deriving various trigonometric identities and differentiation rules.

### Dependencies
- `LIM`
- `SIN_X_X_RANGE`
- `REAL_ABS_NZ`
- `REAL_LT_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_SUB_RZERO`
- `REAL_LET_TRANS`

### Porting notes (optional)
The main challenge in porting this theorem would be to ensure that the definitions of `tends_real_real`, `sin`, and the real number operations (`/`, `-`, `abs`) are consistent. The `SIN_X_X_RANGE` theorem might require some effort to prove in other systems if it's not already available. The real arithmetic tactics used are standard and have analogues in most common proof assistants.


---

## COT_X_LIMIT

### Name of formal statement
COT_X_LIMIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_X_LIMIT = prove
 (`((\x. x * cot(x)) tends_real_real &1)(&0)`,
  SUBGOAL_THEN `(cos tends_real_real &1)(&0)` MP_TAC THENL
   [MP_TAC(SPEC `&0` DIFF_COS) THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIFF_CONT) THEN
    REWRITE_TAC[contl; REAL_ADD_LID; COS_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o C CONJ SIN_X_LIMIT) THEN
  DISCH_THEN(MP_TAC o C CONJ (REAL_ARITH `~(&1 = &0)`)) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_DIV) THEN
  REWRITE_TAC[REAL_DIV_1; cot] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC; REAL_INV_INV]);;
```

### Informal statement
The limit of the function $f(x) = x \cdot \cot(x)$ as $x$ approaches $0$ is $1$.
Formally: `((\x. x * cot(x)) tends_real_real &1)(&0)`

### Informal sketch
The proof demonstrates that $\lim_{x \to 0} x \cot(x) = 1$.

- First, it is proved, using the standard properties of limits, that $\lim_{x \to 0} \cos(x) = 1$. This is achieved by using `DIFF_COS` which differentiates `cos(x)` and states that it equals `-sin(x)`. Then, `DIFF_CONT` proves that differential functions are continuous, which gives us the continuity of `cos` at zero. Then rewrite with `contl`, `REAL_ADD_LID`, and `COS_0` to show 1.
- Next, it uses the fact that $\lim_{x \to 0} \sin(x) / x = 1$ (`SIN_X_LIMIT`).
- It is shown that $x$ is not equal to $0$ (`REAL_ARITH `~(&1 = &0)``).
- Then, `LIM_DIV` theorem is applied, which states that if $\lim_{x \to a} f(x) = l$ and $\lim_{x \to a} g(x) = m$, where $m \neq 0$, then $\lim_{x \to a} f(x) / g(x) = l/m$.
- Rewriting the goal using the definition of cotangent (`cot`) as $\cos(x) / \sin(x)$ and `REAL_DIV_1`, `REAL_INV_MUL`, `REAL_MUL_AC`, `REAL_INV_INV` simplifies the main goal using algebraic manipulations to arrive at the desired result 1.

### Mathematical insight
The theorem `COT_X_LIMIT` establishes an important limit involving the cotangent function. This limit is crucial in various areas of calculus, especially when dealing with indeterminate forms and evaluating limits of trigonometric functions. It builds upon the well-known limit of $\sin(x)/x$ as $x$ approaches 0 and uses the continuity of cosine function at 0. This result is frequently used in proving other limit theorems and evaluating complex limits.

### Dependencies
- `contl`
- `REAL_ADD_LID`
- `COS_0`
- `DIFF_COS`
- `DIFF_CONT`
- `SIN_X_LIMIT`
- `LIM_DIV`
- `REAL_DIV_1`
- `cot`
- `REAL_DIV`
- `REAL_INV_MUL`
- `REAL_MUL_AC`
- `REAL_INV_INV`
- `CONJ_ASSOC`

### Porting notes (optional)
- The proof relies heavily on rewriting with algebraic identities and limit theorems. Make sure the target proof assistant has similar theorems available.
- Automation may be needed to handle the algebraic simplifications.
- The tactic `REAL_ARITH` is used to prove `~(&1 = &0)`. Ensure a corresponding tactic or library for real arithmetic is available in the target system.


---

## COT_LIMIT_LEMMA

### Name of formal statement
COT_LIMIT_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_LIMIT_LEMMA = prove
 (`!x. ~(x = &0)
       ==> (\n. (x / &2 pow n) * cot(x / &2 pow n)) tends_num_real &1`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC COT_X_LIMIT THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THEN
  X_CHOOSE_TAC `N:num` (SPEC `abs(x) / d` REAL_ARCH_POW2) THEN
  EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN
  DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_POW2_CLAUSES; REAL_LT_DIV; GSYM REAL_ABS_NZ] THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW2_CLAUSES] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 pow N` THEN
  ASM_REWRITE_TAC[REAL_POW2_THM]);;
```
### Informal statement
For all real numbers `x`, if `x` is not equal to 0, then the sequence defined by the function mapping `n` to `(x / (2^n)) * cot(x / (2^n))` tends to the limit 1, as `n` tends to infinity in the natural numbers.

### Informal sketch
The proof proceeds as follows:
- Assume `x` is a real number not equal to 0.
- Introduce a real number `e` as a variable.
- Use the theorem `COT_X_LIMIT` (limit of cotangent) to show that the limit of `cot(x)` as `x` tends to 0 is infinity.
- Rewrite the limit using `LIM` tactic to introduce epsilon-delta definition
- Specialize the limit definition with `e`.
- Assume that `abs(x)` is nonzero; rewrite using lemmas about absolute values.
- Choose a real number `d` based on the epsilon-delta definition of the limit, where `0 < abs(x) < d ==> abs(cot(x) - 1) < e`.
- Further reduce with `REAL_SUB_RZERO` tactic
- Instantiate the Archimedean principle `REAL_ARCH_POW2` with `abs(x) / d` to find a natural number `N` such that `2^N > abs(x) / d`.
- Show that for any `n` greater than or equal to `N`, `abs((x / 2^n) * cot(x / 2^n) - 1) < e`. This involves using the Archimedean property and properties of absolute values, powers, and inequalities. The proof involves rewriting with lemmas like `REAL_ABS_DIV`, `REAL_ABS_POW`, and `REAL_ABS_NUM` for absolute value manipulations, and `REAL_LT_DIV`, `REAL_LT_LDIV_EQ`, and `REAL_POW2_CLAUSES` for inequalities and powers of 2.

### Mathematical insight
The theorem states that for any non-zero real number `x`, the given sequence converges to 1. This is a fundamental result often used in the analysis of series and sequences, especially those involving trigonometric functions. The proof relies on the limit of `cot(x)` as `x` approaches 0 and the Archimedean property to manipulate real numbers and establish the convergence.

### Dependencies
- `COT_X_LIMIT`: The limit of `x*cot(x)` as `x` approaches 0 is 1.
- `LIM`: Definition of limit.
- `REAL_SUB_RZERO`
- `REAL_ARCH_POW2`: Archimedean property of real numbers with powers of 2.
- `REAL_ABS_DIV`: Absolute value of a division.
- `REAL_ABS_POW`: Absolute value of power.
- `REAL_ABS_NUM`: Absolute value of a number.
- `REAL_POW2_CLAUSES`: Properties of powers of 2.
- `REAL_LT_DIV`: Properties of less than and division.
- `REAL_LT_LDIV_EQ`: Properties of less than and division, equality case.
- `REAL_MUL_SYM`: Symmetry of multiplication.
- `REAL_LTE_TRANS`: Transitivity of less than or equal to.
- `REAL_POW2_THM`

### Porting notes (optional)
- The proof relies heavily on real number arithmetic and inequalities. A target proof assistant needs to have good support for these.
- The Archimedean property is crucial; ensure the target system has an equivalent axiom or theorem.
- The tactics used in HOL Light are not directly transferable. The proof sketch outlines the mathematical reasoning, which should guide the porting process.


---

## COT_LIMIT_LEMMA1

### Name of formal statement
COT_LIMIT_LEMMA1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_LIMIT_LEMMA1 = prove
 (`~(x = &0)
   ==> (\n. (pi / &2 pow (n + 1)) * cot(pi * x / &2 pow (n + 1)))
       tends_num_real (inv(x))`,
  DISCH_TAC THEN
  MP_TAC(SPEC `pi * x * inv(&2)` COT_LIMIT_LEMMA) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ; PI_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `p * x * a * b * c = x * (p * (a * b)) * c`] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[ADD1; GSYM real_div] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [GSYM REAL_MUL_LID] THEN
  FIRST_ASSUM(SUBST1_TAC o GSYM o MATCH_MP REAL_MUL_LINV) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `x * p * q * c = x * (p * q) * c`] THEN
  ASM_REWRITE_TAC[GSYM real_div]);;
```
### Informal statement
If `x` is not equal to 0, then the sequence defined by the function that maps `n` to `(pi / (&2 to the power of (n + 1))) * cot(pi * x / (&2 to the power of (n + 1)))` tends to the limit `1/x` as `n` tends to infinity.

### Informal sketch
The proof proceeds as follows:
- Assume `x` is not zero.
- Apply `COT_LIMIT_LEMMA` after specializing it with `pi * x / &2`. `COT_LIMIT_LEMMA` states that as `x` approaches 0, `x * cot(x)` approaches 1.
- Simplify using real number properties such as `REAL_ENTIRE` (entirety of real numbers), `REAL_LT_IMP_NZ` (if a real number is positive, then it is non-zero), and `PI_POS` (`pi` is positive).
- Reduce the real rational expression.
- Rewrite using `real_div` (definition of real division), `REAL_MUL_LID` (real multiplication identity), and associativity of real multiplication (`REAL_MUL_ASSOC`).
- Reorder the expression using associativity and commutativity of real multiplication: `p * x * a * b * c = x * (p * (a * b)) * c`.
- Rewrite using the inverse property of real multiplication (`REAL_INV_MUL`).
- Rewrite power expressions using `real_pow`.
- Simplify using `ADD1` (addition with 1) and `real_div`.
- Rewrite using identity of real multiplication.
- Use the inverse property of real multiplication.
- Rewrite using the associativity of real multiplication.
- Rewrite using neutral element of multiplication.
- Use the theorem stating that multiplication of sequences preserves limits.
- Rewrite using the fact that the limit of a constant sequence is the constant itself (`SEQ_CONST`).
- Reorder the expression using associativity and commutativity of real multiplication.
- Simplify by canceling out common factors.

### Mathematical insight
This theorem establishes the limit of a specific sequence involving the cotangent function. The sequence is constructed such that it converges to `1/x`. This result is likely used in the further analysis or approximation of functions.

### Dependencies
- `PI_POS`
- `COT_LIMIT_LEMMA`
- `REAL_ENTIRE`
- `REAL_LT_IMP_NZ`
- `real_div`
- `REAL_MUL_LID`
- `REAL_MUL_ASSOC`
- `REAL_INV_MUL`
- `real_pow`
- `ADD1`
- `REAL_MUL_LINV`
- `REAL_MUL_RID`
- `SEQ_MUL`
- `SEQ_CONST`
- `REAL_RAT_REDUCE_CONV`

### Porting notes (optional)
- The proof relies heavily on rewriting with properties of real numbers. Ensure that the target proof assistant has adequate support for these properties.
- The use of `AC` (associativity and commutativity) reordering may need to be adapted depending on the specific AC rewriting capabilities of the target system.


---

## COT_X_BOUND_LEMMA_POS

### Name of formal statement
COT_X_BOUND_LEMMA_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_X_BOUND_LEMMA_POS = prove
 (`?M. !x. &0 < x /\ abs(x) <= &1 ==> abs(x * cot(x)) <= M`,
  MP_TAC COT_X_LIMIT THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`\x. x * cot(x)`; `d:real`; `&1`] CONT_BOUNDED_ABS) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CONT THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[DIFF_X]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    REWRITE_TAC[cot] THEN MATCH_MP_TAC CONT_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC DIFF_CONT THEN
      EXISTS_TAC `--(sin x)` THEN REWRITE_TAC[DIFF_COS];
      MATCH_MP_TAC DIFF_CONT THEN
      EXISTS_TAC `cos x` THEN REWRITE_TAC[DIFF_SIN];
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
      SUBGOAL_THEN `&1 < pi`
       (fun th -> ASM_MESON_TAC[th; REAL_LET_TRANS; REAL_LTE_TRANS]) THEN
      MP_TAC PI_APPROX_25_BITS THEN
      MATCH_MP_TAC(REAL_ARITH
       `&1 + e < a ==> abs(p - a) <= e ==> &1 < p`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:real`) THEN EXISTS_TAC `abs M + &2` THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  DISJ_CASES_TAC(SPECL [`abs x`; `d:real`] REAL_LTE_TOTAL) THENL
   [MATCH_MP_TAC(REAL_ARITH `abs(x - &1) < &1 ==> abs(x) <= abs(m) + &2`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs(x)`];
    MATCH_MP_TAC(REAL_ARITH `x <= m ==> x <= abs(m) + &2`) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < x`; `abs(x) <= &1`; `d <= abs(x)`] THEN
    REAL_ARITH_TAC]);;
```
### Informal statement
There exists a real number `M` such that for all real numbers `x`, if `0 < x` and `abs(x) <= 1`, then `abs(x * cot(x)) <= M`.

### Informal sketch
The proof demonstrates that `abs(x * cot(x))` is bounded when `0 < x` and `abs(x) <= 1`.

- First, the limit of x * cot(x) as x approaches 0 is computed by `COT_X_LIMIT` with some rewriting using `LIM`. It is implied that the limit is 1.
- We consider the specific case where x is `d`, with `d` being 1. It is shown that since `0 < d` and `d <= 1 ` then `abs(1 * cot(1))` exists.
- Continuity of `x * cot(x)` is established. This is needed to bound the function on the interval from `d` to 1, via `CONT_BOUNDED_ABS`.
- To prove that `x * cot(x)` is continuous, we need to show that `x*cot(x)` is continuous. The proof uses `DIFF_CONT` to show that `x` and `cot(x)` are differentiable. The continuity of `cot(x)` relies on the continuity of `cos(x)` and `sin(x)` and that `sin(x)` is non-zero on the interval.
- Based on the above continuity results, an `M` can be generated.
- A real number `x` is introduced and we perform a case split based upon whether `d <= abs(x)`.
Finally the proof shows that there exists a real `M` such that for every `x` if `0 < x` and `abs(x) <= 1`.

### Mathematical insight
This theorem asserts that the function `x * cot(x)` is bounded on the interval `(0, 1]`. This is a key property when working with trigonometric functions and their limits, particularly near singularities.

### Dependencies
- `COT_X_LIMIT`
- `LIM`
- `REAL_LT_01`
- `REAL_SUB_RZERO`
- `CONT_BOUNDED_ABS`
- `CONT_MUL`
- `DIFF_CONT`
- `DIFF_X`
- `DIFF_COS`
- `DIFF_SIN`
- `REAL_LT_IMP_NZ`
- `SIN_POS_PI`
- `PI_APPROX_25_BITS`
- `REAL_ARITH`
- `REAL_LTE_TOTAL`

### Porting notes (optional)
- The proof relies heavily on real analysis theorems, continuity, differentiability, limits and arithmetic reasoning (`REAL_ARITH_TAC`).
- Automation in other provers may differ; porting may require explicit tactics for real arithmetic or limit reasoning.
- The tactic `X_CHOOSE_TAC` is used; this tactic finds an element that satisfies an existential quantifier. This needs to be emulated using an appropriate tactic for the target proof assistant.


---

## COT_X_BOUND_LEMMA

### Name of formal statement
COT_X_BOUND_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_X_BOUND_LEMMA = prove
 (`?M. !x. ~(x = &0) /\ abs(x) <= &1 ==> abs(x * cot(x)) <= M`,
  X_CHOOSE_TAC `M:real` COT_X_BOUND_LEMMA_POS THEN
  EXISTS_TAC `M:real` THEN X_GEN_TAC `x:real` THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(x = &0) ==> &0 < x \/ &0 < --x`)) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `x * cot(x) = --x * cot(--x)` SUBST1_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[REAL_ABS_NEG]] THEN
  REWRITE_TAC[cot; SIN_NEG; COS_NEG; real_div; REAL_INV_NEG;
              REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]);;
```

### Informal statement
There exists a real number `M` such that for all real numbers `x`, if `x` is not equal to 0 and the absolute value of `x` is less than or equal to 1, then the absolute value of `x` multiplied by the cotangent of `x` is less than or equal to `M`.

### Informal sketch
The proof proceeds as follows:

- Choose a specific value for `M` using `COT_X_BOUND_LEMMA_POS` (presumably, a lemma stating the existence of such a positive `M`).
- Introduce the existential quantifier by providing `M`.
- Introduce the universal quantifier for `x`.
- Strip the quantifiers and implication.
- Split the proof into two cases based on `x` being positive or negative using `REAL_ARITH` to show `~(x = &0) ==> &0 < x \/ &0 < --x`.
- Simplify assumptions using `ASM_SIMP_TAC[]`.
- Introduce the subgoal `x * cot(x) = --x * cot(--x)` and substitute it, this leverages the fact that the function `x * cot(x)` is even so it suffices to prove the theorem for when `x` is positive.
- Handle the subgoal with `ALL_TAC`, indicating it's trivially true.
- Simplify using rewriting rules for cotangent, sine, cosine, division, inverse, multiplication, and negation properties of real numbers.

### Mathematical insight
The lemma establishes that `x * cot(x)` is bounded when `x` is near 0 (specifically, within the interval [-1, 1] excluding 0). This is important because `cot(x)` approaches infinity as `x` approaches 0. Multiplying by `x` tames this behavior, and the lemma shows it remains bounded. This result is useful in analysis and calculus for dealing with functions involving cotangent near 0, by finding a suitable bound `M`.

### Dependencies
Real analysis theorems related to:
- `cot`
- `SIN_NEG`
- `COS_NEG`
- `real_div`
- `REAL_INV_NEG`
- `REAL_MUL_LNEG`
- `REAL_MUL_RNEG`
- `REAL_NEG_NEG`
- `REAL_ABS_NEG`
- `COT_X_BOUND_LEMMA_POS` - A lemma exhibiting a positive real number `M` satisfying `!x. ~(x = &0) /\ abs(x) <= &1 ==> abs(x * cot(x)) <= M`
- `REAL_ARITH` - tactics involving arithmetic reasoning and simplification on real numbers

### Porting notes (optional)
- The proof relies on several real number arithmetic simplification rules, which may need to be explicitly provided or proved in other proof assistants.
- The tactic `X_CHOOSE_TAC` followed by `EXISTS_TAC` is intended to instantiate the existential quantifier using a specific value obtained from `COT_X_BOUND_LEMMA_POS`. In other proof assistants, one may need to use a constructive existence proof to extract the witness and then apply the existential introduction rule.


---

## COT_PARTIAL_FRACTIONS

### Name of formal statement
COT_PARTIAL_FRACTIONS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_PARTIAL_FRACTIONS = prove
 (`~(integer x)
   ==> (\n. (&2 * x pow 2) / (x pow 2 - &n pow 2)) sums
       ((pi * x) * cot(pi * x) + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
    SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL];
    ALL_TAC] THEN
  ABBREV_TAC
   `A = \n k. (pi * x / &2 pow n) * cot(pi * x / &2 pow n) +
              (pi * x / &2 pow (n + 1)) *
              sum(1,k) (\m. cot (pi * (x + &m) / &2 pow (n + 1)) +
                            cot (pi * (x - &m) / &2 pow (n + 1)))` THEN
  ABBREV_TAC
   `B = \n k. (pi * x / &2 pow (n + 1)) *
              sum(k + 1,2 EXP n - 1 - k)
                 (\m. cot(pi * (x + &m) / &2 pow (n + 1)) +
                      cot(pi * (x - &m) / &2 pow (n + 1)))` THEN
  SUBGOAL_THEN `!n. ~(x - &n = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x = (x - &n) + &n` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(x + &n = &0)` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `x = (x + &n) - &n` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[integer; REAL_INTEGER_CLOSURES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ~(x pow 2 - &n pow 2 = &0)` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * a - b * b = (a + b) * (a - b)`] THEN
    ASM_REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (&2 * x) / (x pow 2 - &n pow 2) = inv(x + &n) + inv(x - &n)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_EQ_LCANCEL_IMP THEN
    EXISTS_TAC `x pow 2 - &n pow 2` THEN ASM_SIMP_TAC[REAL_DIV_LMUL] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ADD_LDISTRIB] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * a - b * b = (a + b) * (a - b)`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(p * m) * p' + (p * m) * m' = m * p * p' + p * m * m'`] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. (\n. A n k) tends_num_real
                    (&1 + sum(1,k) (\n. (&2 * x pow 2) / (x pow 2 - &n pow 2)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "A" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SEQ_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC COT_LIMIT_LEMMA THEN
      ASM_SIMP_TAC[REAL_ENTIRE; PI_POS; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_CMUL] THEN MATCH_MP_TAC SEQ_SUM THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_2; real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(&2 * x * x) * d = x * (&2 * x) * d`] THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM real_div] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC SEQ_ADD THEN
    REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(p * x * d) * cc = x * (p * d) * cc`] THEN
    CONJ_TAC THEN MATCH_MP_TAC SEQ_MUL THEN REWRITE_TAC[SEQ_CONST] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[COT_LIMIT_LEMMA1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!k n. &6 * abs(x) < &k
          ==> abs(B n k)
              <= abs((pi * x / &2 pow (n + 1)) *
                     cot(pi * x / &2 pow (n + 1))) *
                 sum(k + 1,2 EXP n - 1 - k)
                    (\m. (&72 * x pow 2) / (&m pow 2 - &36 * x pow 2))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH lhand SUM_ABS_LE (lhand w))) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[ARITH_RULE
     `k + 1 <= r /\ r < (p - 1 - k) + k + 1 <=> k < r /\ r < p`] THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
    EXISTS_TAC `abs(inv(&2 pow (n + 1)))` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs(x)`; REAL_LT_INV_EQ;
             REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `abs(cot (pi * x / &2 pow (n + 1)) / &2 pow n) *
      (&36 * x pow 2) / (&r pow 2 - &36 * x pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC KNOPP_TERM_BOUND THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN
      EXISTS_TAC `&k` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_POW_ADD;
                REAL_ABS_MUL; REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    GEN_REWRITE_TAC RAND_CONV
     [AC REAL_MUL_AC `a * b * c * d * e = b * c * d * a * e`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n k:num. N <= k /\ pi * abs(x) <= &2 pow (n + 1)
                          ==> abs(B n k) < e`
  ASSUME_TAC THENL
   [X_CHOOSE_TAC `Bd:real` COT_X_BOUND_LEMMA THEN
    SUBGOAL_THEN
     `!k n. &9 * abs x < &k
            ==> abs(sum(k + 1,2 EXP n - 1 - k)
                       (\m. (&72 * x pow 2) / (&m pow 2 - &36 * x pow 2)))
                <= &144 * x pow 2 / &k`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; SUM_CMUL] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_POW; REAL_POW2_ABS] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&144 * x * y = &72 * x * &2 * y`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_LE_SQUARE; REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * sum(k + 1,2 EXP n - 1 - k) (\m. inv(&m * &m))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM SUM_CMUL] THEN
        W(fun (asl,w) -> MP_TAC(PART_MATCH lhand SUM_ABS_LE (lhand w))) THEN
        MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
        MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `&0 < &r * &r - &36 * x * x` ASSUME_TAC THENL
         [REWRITE_TAC[GSYM REAL_POW_2] THEN
          ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
          REWRITE_TAC[REAL_POW_2] THEN
          REWRITE_TAC[REAL_ARITH
           `&0 < r * r - &36 * x * x <=> (&6 * x) * (&6 * x) < r * r`] THEN
          MATCH_MP_TAC REAL_LT_MUL2 THEN
          SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_ABS_POS] THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&k` THEN
          ASM_REWRITE_TAC[REAL_ABS_NUM] THEN
          REWRITE_TAC[REAL_OF_NUM_LE] THEN
          ASM_SIMP_TAC[REAL_ARITH `&9 * abs(x) < a ==> &6 * abs(x) < a`] THEN
          UNDISCH_TAC `k + 1 <= r` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_LE_INV_EQ] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
        REWRITE_TAC[real_div] THEN
        ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
        REWRITE_TAC[GSYM real_div] THEN
        SUBGOAL_THEN `&0 < &r` ASSUME_TAC THENL
         [UNDISCH_TAC `k + 1 <= r` THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
          ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
        REWRITE_TAC[REAL_ARITH `&1 * x <= &2 * (x - y) <=> &2 * y <= x`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ &81 * x <= y ==> &2 * &36 * x <= y`) THEN
        REWRITE_TAC[REAL_LE_SQUARE] THEN
        REWRITE_TAC[REAL_ARITH `&81 * x * x = (&9 * x) * (&9 * x)`] THEN
        REWRITE_TAC[GSYM REAL_POW_2] THEN
        ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
        REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&k` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        UNDISCH_TAC `k + 1 <= r` THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[SUM_REINDEX] THEN
      SUBGOAL_THEN `?d. k = 1 + d` (CHOOSE_THEN SUBST1_TAC) THENL
       [REWRITE_TAC[GSYM LE_EXISTS] THEN
        MATCH_MP_TAC(ARITH_RULE `0 < k ==> 1 <= k`) THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
        UNDISCH_TAC `&9 * abs(x) < &k` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SPEC_TAC(`2 EXP n - 1 - (1 + d)`,`n:num`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV) [ADD_SYM] THEN
      REWRITE_TAC[SUM_REINDEX] THEN
      REWRITE_TAC[ARITH_RULE `(r + 1) + 1 = r + 2`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(d,n) (\r. inv(&(r + 1) * &(r + 2)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; REAL_LT_INV_EQ; REAL_OF_NUM_LT;
                 REAL_INV_MUL; ARITH_RULE `0 < n + 2`] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!n. sum(d,n) (\r. inv (&(r + 1) * &(r + 2))) =
            inv(&(d + 1)) - inv(&(d + n + 1))`
       (fun th -> REWRITE_TAC[th])
      THENL
       [INDUCT_TAC THEN REWRITE_TAC[sum; ADD_CLAUSES; REAL_SUB_REFL] THEN
        ASM_REWRITE_TAC[REAL_ARITH
         `((a - x) + y = a - z) <=> (y + z = x)`] THEN
        REWRITE_TAC[GSYM ADD_ASSOC; REAL_INV_MUL;
          ARITH_RULE `SUC(d + n + 1) = d + n + 2`] THEN
        MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
        EXISTS_TAC `&(d + n + 1) * &(d + n + 2)` THEN
        REWRITE_TAC[REAL_ARITH
         `(dn1' * dn2' + dn2') * (dn1 * dn2) =
          (dn1 * dn1' + dn1) * (dn2 * dn2')`] THEN
        SIMP_TAC[REAL_ENTIRE; REAL_MUL_RINV; REAL_OF_NUM_EQ;
                 ARITH_RULE `~(d + n + 1 = 0) /\ ~(d + n + 2 = 0)`] THEN
        SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV;
                 REAL_OF_NUM_EQ; ARITH_RULE `~(d + n + 1 = 0)`] THEN
        REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
        ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ADD_AC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x - y <= x`) THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?N. &9 * abs(x) + &1 <= &N /\
          (Bd * &144 * x pow 2) / e + &1 <= &N`
     (X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC)
    THENL
     [X_CHOOSE_TAC `N1:num` (SPEC `&9 * abs(x) + &1` REAL_ARCH_SIMPLE) THEN
      X_CHOOSE_TAC `N2:num`
       (SPEC `(Bd * &144 * x pow 2) / e + &1` REAL_ARCH_SIMPLE) THEN
      EXISTS_TAC `N1 + N2:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      ASM_MESON_TAC[REAL_POS;
                    REAL_ARITH `a <= m /\ b <= n /\ &0 <= m /\ &0 <= n
                                ==> a <= m + n /\ b <= m + n`];
      ALL_TAC] THEN
    EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `k:num`] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
     `abs((pi * x / &2 pow (n + 1)) * cot (pi * x / &2 pow (n + 1))) *
          sum(k + 1,2 EXP n - 1 - k)
              (\m. (&72 * x pow 2) / (&m pow 2 - &36 * x pow 2))` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `&N` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      UNDISCH_TAC `&9 * abs x + &1 <= &N` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `Bd * &144 * x pow 2 / &k` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      SUBGOAL_THEN `&0 < &k` (fun th -> SIMP_TAC[REAL_LT_LDIV_EQ; th]) THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `&9 * abs x + &1 <= &N` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_OF_NUM_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `x + &1 <= y ==> x < y`]] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_ABS] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[real_div; REAL_ENTIRE; REAL_LT_IMP_NZ; REAL_POW2_CLAUSES;
                   REAL_MUL_ASSOC; REAL_LT_INV_EQ; PI_POS] THEN
      SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW2_CLAUSES; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS] THEN
      ASM_REWRITE_TAC[GSYM real_abs]; ALL_TAC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N:real` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&9 * abs x + &1 <= &N` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n k. k < 2 EXP n
          ==> ((pi * x) *
               (cot (pi * x / &2 pow n) / &2 pow n +
                sum (1,2 EXP n - 1)
                    (\k. cot(pi * (x + &k) / &2 pow (n + 1)) +
                         cot(pi * (x - &k) / &2 pow (n + 1))) /
                &2 pow (n + 1)) = A n k + B n k)`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC; GSYM REAL_ADD_LDISTRIB] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV o funpow 3 LAND_CONV)
      [ARITH_RULE `x = 0 + x`] THEN
    REWRITE_TAC[SUM_REINDEX] THEN
    ONCE_REWRITE_TAC
     [REWRITE_RULE[REAL_ARITH `(a = b - c) <=> (c + a = b)`] SUM_DIFF] THEN
    ASM_SIMP_TAC[ARITH_RULE `n < p ==> (n + p - 1 - n = p - 1)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV o funpow 3 LAND_CONV)
     [ARITH_RULE `x = 0 + x`] THEN
    REWRITE_TAC[SUM_REINDEX] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; GSYM REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_AC]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_HALF_KNOPP) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN DISCH_TAC THEN
  REWRITE_TAC[sums; SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!e. &0 < e
        ==> ?N. !n k:num. N <= k /\ pi * abs(x) <= &2 pow (n + 1)
                          ==> abs (B n k) < e` THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `N1 + 1` THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[GE] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!k. (\n. A n k) tends_num_real
           &1 + sum (1,k) (\n. (&2 * x pow 2) / (x pow 2 - &n pow 2))` THEN
  DISCH_THEN(MP_TAC o SPEC `n - 1`) THEN REWRITE_TAC[SEQ] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN REWRITE_TAC[GE] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?m. n - 1 < 2 EXP m /\ N2 <= m /\ pi * abs(x) <= &2 pow (m + 1)`
  MP_TAC THENL
   [SUBGOAL_THEN `?m. &(n - 1) + &1 <= &m /\ &N2 <= &m /\ pi * abs(x) <= &m`
    MP_TAC THENL
     [X_CHOOSE_TAC `m1:num` (SPEC `&(n - 1) + &1` REAL_ARCH_SIMPLE) THEN
      X_CHOOSE_TAC `m2:num` (SPEC `&N2` REAL_ARCH_SIMPLE) THEN
      X_CHOOSE_TAC `m3:num` (SPEC `pi * abs(x)` REAL_ARCH_SIMPLE) THEN
      EXISTS_TAC `m1 + m2 + m3:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= a /\ y <= b /\ z <= c /\ &0 <= a /\ &0 <= b /\ &0 <= c
        ==> x <= a + b + c /\ y <= a + b + c /\ z <= a + b + c`) THEN
      ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC(REAL_ARITH
     `m <= m2 /\ m2 <= m22
      ==> x1 + &1 <= m /\ x2 <= m /\ x3 <= m
          ==> x1 < m2 /\ x2 <= m /\ x3 <= m22`) THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    REWRITE_TAC[REAL_ARITH `x <= x * &2 <=> &0 <= x`] THEN
    REWRITE_TAC[REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_POW] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`m:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `SUC(2 EXP n)` THEN
    ASM_REWRITE_TAC[LT_SUC] THEN REWRITE_TAC[MULT_2; ADD1; LE_ADD_LCANCEL] THEN
    REWRITE_TAC[num_CONV `1`; LE_SUC_LT; EXP_LT_0; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / &2 + e / &2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_LE_REFL; GSYM REAL_MUL_2; REAL_DIV_LMUL;
             REAL_OF_NUM_EQ; ARITH_EQ]] THEN
  UNDISCH_TAC
   `!n k. k < 2 EXP n ==> ((pi * x) * cot (pi * x) = A n k + B n k)` THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `n - 1`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(b) < e /\ abs((s - &1) - a) < e
    ==> abs(s - ((a + b) + &1)) < e + e`) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `N1 + 1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (0,n) (\r. (&2 * x pow 2) / (x pow 2 - &r pow 2)) - &1 =
    &1 + sum(1,n-1) (\r. (&2 * x pow 2) / (x pow 2 - &r pow 2))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `n = 1 + (n - 1)`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [UNDISCH_TAC `N1 + 1 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    MATCH_MP_TAC(REAL_ARITH `(a = &2) ==> ((x + a) - &1 = &1 + x)`) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
    REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN REWRITE_TAC[real_div] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_DIV_REFL; REAL_POW_EQ_0] THEN
    REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
If `x` is not an integer, then the function that maps `n` to `(2 * x^2) / (x^2 - n^2)` sums to `(pi * x) * cot(pi * x) + 1`.

### Informal sketch
The proof establishes the partial fraction decomposition of `pi * x * cot(pi * x) + 1` by showing that the sum of the given series converges to this expression, provided `x` is not an integer. The proof proceeds as follows:

- It begins by assuming that `x` is not an integer and proving `x` cannot be zero.
- Abbreviates two key expressions `A` and `B`, which represent partial sums related to the cotangent function.
- Establishes that `x - n != 0` and `x + n != 0` for all `n`, given that `x` is not an integer.
- Shows that `(2 * x) / (x^2 - n^2) = inv(x + n) + inv(x - n)` for all `n`.
- Proves that `A n k` tends to `1 + sum(1, k) ((2 * x^2) / (x^2 - n^2))` as `n` tends to infinity. This involves using `COT_LIMIT_LEMMA` and `COT_LIMIT_LEMMA1`.
- Demonstrates that for a given epsilon greater than 0, there exists an `N` such that for all `n` and `k` greater than or equal to `N`, and under the condition `pi * abs x <= 2^(n+1)`, `abs(B n k)` is less than epsilon. This part involves bounding `B n k` using inequalities and applying `COT_X_BOUND_LEMMA`.
- Shows that the partial sum `(pi * x) * (cot (pi * x / &2 pow n) / &2 pow n + sum (1,2 EXP n - 1) (\k. cot(pi * (x + &k) / &2 pow (n + 1)) + cot(pi * (x - &k) / &2 pow (n + 1))) / &2 pow (n + 1))` is equal to `A n k + B n k` for `k < 2 EXP n`.
- Utilizes `COT_HALF_KNOPP` and combines the limit results to show that the original series converges.

### Mathematical insight
This theorem provides a partial fraction decomposition for the function `(pi * x) * cot(pi * x) + 1`. Such decompositions are crucial in complex analysis and have applications in number theory and physics. The condition that `x` is not an integer is necessary to avoid singularities in the cotangent function and the terms of the series.

### Dependencies
- `integer`
- `REAL_ABS_NUM`
- `REAL_OF_NUM_EQ`
- `EXISTS_REFL`
- `REAL_INTEGER_CLOSURES`
- `REAL_POW_2`
- `REAL_ENTIRE`
- `DE_MORGAN_THM`
- `REAL_DIV_LMUL`
- `REAL_ADD_LDISTRIB`
- `REAL_MUL_RINV`
- `REAL_MUL_RID`
- `COT_LIMIT_LEMMA`
- `PI_POS`
- `REAL_LT_IMP_NZ`
- `SUM_CMUL`
- `SEQ_SUM`
- `real_div`
- `SEQ_CONST`
- `COT_LIMIT_LEMMA1`
- `SUM_ABS_LE`
- `REAL_ABS_POS`
- `REAL_LT_INV_EQ`
- `REAL_POW2_CLAUSES`
- `KNOPP_TERM_BOUND`
- `REAL_OF_NUM_LT`
- `AC REAL_MUL_AC `a * b * c * d * e = b * c * d * a * e``
- `REAL_RAT_REDUCE_CONV`
- `COT_X_BOUND_LEMMA`
- `REAL_ABS_NUM`
- `REAL_ABS_POW`
- `REAL_POW2_ABS`
- `REAL_LE_SQUARE`
- `REAL_LT_MUL2`
- `REAL_LE_INV_EQ`
- `REAL_LE_LDIV_EQ`
- `REAL_LE_RDIV_EQ`
- `REAL_LT_MUL`
- `REAL_POS`
- `SUM_REINDEX`
- `LE_EXISTS`
- `MONO_EXISTS`
- `LTE_TRANS`
- `EXP`
- `ARITH`
- `LT_SUC`
- `ADD1`
- `LE_ADD_LCANCEL`
- `EXP_LT_0`
- `ARITH_EQ`
- `COT_HALF_KNOPP`
- `sums`
- `SEQ`

### Porting notes (optional)
- Automation may be needed to discharge the various real arithmetic goals that arise during the proof.
- Special attention may be required when porting the convergence results and inequalities.


---

## COT_PARTIAL_FRACTIONS_SUBTERM

### Name of formal statement
COT_PARTIAL_FRACTIONS_SUBTERM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_PARTIAL_FRACTIONS_SUBTERM = prove
 (`abs(x) < &n
   ==> (\k. --(&2) * (x pow 2 / &n pow 2) pow (k + 1))
       sums ((&2 * x pow 2) / (x pow 2 - &n pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(x) < &n` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\k. (x pow 2 / &n pow 2) pow k) sums
    inv(&1 - (x pow 2 / &n pow 2))`
  MP_TAC THENL
   [MATCH_MP_TAC GP THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_POW; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_POW_LT2; REAL_ABS_POS; ARITH_EQ]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    SPEC `--(&2) * (x pow 2 / &n pow 2)` o MATCH_MP SER_CMUL) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM(CONJUNCT2 real_pow)] THEN
    REWRITE_TAC[ADD1]; ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_INV_MUL;
              GSYM REAL_MUL_ASSOC; REAL_MUL_LNEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_RNEG; GSYM REAL_INV_NEG] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_NEG_SUB; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_DIV_LMUL; REAL_POW_LT; REAL_LT_IMP_NZ]);;
```
### Informal statement
If the absolute value of `x` is less than `n`, then the series defined by the function that maps `k` to `--(&2) * (x pow 2 / &n pow 2) pow (k + 1)` sums to `(&2 * x pow 2) / (x pow 2 - &n pow 2)`.

### Informal sketch
The proof shows that if `abs(x) < &n`, then the series `\k. --(&2) * (x pow 2 / &n pow 2) pow (k + 1)` sums to `(&2 * x pow 2) / (x pow 2 - &n pow 2)`.
- First, the goal is split into two subgoals. The first subgoal checks that `0 < n` given that `abs(x) < n`, which is proven by real arithmetic.
- The second subgoal states that the series `\k. (x pow 2 / &n pow 2) pow k` sums to `inv(&1 - (x pow 2 / &n pow 2))`. This subgoal is then matched with the geometric progression theorem `GP`. The assumptions of `GP` are discharged and simplified using rewriting, and the assumptions are also simplified with arithmetic equations.
- The theorem `SER_CMUL` is used to multiply series by a constant.
- Afterwards, the goal is rewritten using properties of real numbers such as associativity of multiplication, and properties of exponentiation.
- Finally, the goal is rewritten using properties of division, negation, and distributivity of subtraction and multiplication. The assumptions are simplified further, and the proof is complete.

### Mathematical insight
This theorem establishes the convergence of a specific power series and its closed-form expression. This result is likely a step toward demonstrating properties of trigonometric or analytic functions in the real numbers. The power series expansion is essential for defining and manipulating functions within the formal system.

### Dependencies
- `REAL_ARITH`
- `REAL_ABS_DIV`
- `REAL_ABS_POW`
- `REAL_ABS_NUM`
- `REAL_LT_LDIV_EQ`
- `REAL_POW_LT`
- `REAL_MUL_LID`
- `REAL_POW_LT2`
- `REAL_ABS_POS`
- `ARITH_EQ`
- `SER_CMUL`
- `REAL_MUL_ASSOC`
- `real_pow`
- `ADD1`
- `real_div`
- `REAL_INV_MUL`
- `REAL_MUL_LNEG`
- `REAL_MUL_RNEG`
- `REAL_INV_NEG`
- `REAL_NEG_SUB`
- `REAL_SUB_LDISTRIB`
- `REAL_MUL_RID`
- `REAL_DIV_LMUL`
- `REAL_LT_IMP_NZ`
- `GP` (Geometric Progression theorem)
- `EQ_IMP`

### Porting notes (optional)
- When porting, ensure that the geometric progression theorem (`GP`) is available or can be proven.
- The extensive use of real arithmetic and rewriting suggests that a proof assistant with strong automation in these areas will be beneficial.
- Pay attention to the exact definitions and properties of real number operations (division, negation, exponentiation) in the target system.


---

## SEQ_LE_CONST

### Name of formal statement
SEQ_LE_CONST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SEQ_LE_CONST = prove
 (`!a x l N. (!n. n >= N ==> x(n) <= a) /\ x tends_num_real l ==> l <= a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEQ_LE THEN
  MAP_EVERY EXISTS_TAC [`x:num->real`; `\n:num. a:real`] THEN
  ASM_REWRITE_TAC[SEQ_CONST] THEN ASM_MESON_TAC[]);;
```
### Informal statement
For any real number `a`, any sequence `x` of real numbers, any real number `l`, and any natural number `N`, if it is the case that for every natural number `n`, if `n` is greater than or equal to `N`, then `x(n)` is less than or equal to `a`, and if `x` tends to `l` as `n` tends to infinity, then `l` is less than or equal to `a`.

### Informal sketch
The proof proceeds as follows:
- Assume that for all `n`, if `n >= N` then `x(n) <= a`, and `x` tends to `l`.
- Apply `SEQ_LE` to show that if the sequence `x` is less than or equal to the sequence `\n. a` then the limit `l` of `x` must be less than or equal to `a`
- Instantiate the existential with `x` and `\n. a`.
- Use `SEQ_CONST` to rewrite `(\n. a) n = a`.
- Combine the assumptions that for all `n. n >= N ==> x(n) <= a`, and `x` tends to `l` to complete the proof.

### Mathematical insight
This theorem states that if a sequence `x` of real numbers is bounded above by `a` from some point `N` onwards, and the sequence converges to a limit `l`, then the limit `l` is also less than or equal to `a`. This is a fundamental result in real analysis concerning the behavior of sequences and limits.

### Dependencies
- Theorem: `SEQ_LE`
- Theorem: `SEQ_CONST`


---

## SEQ_GE_CONST

### Name of formal statement
SEQ_GE_CONST

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SEQ_GE_CONST = prove
 (`!a x l N. (!n. n >= N ==> a <= x(n)) /\ x tends_num_real l ==> a <= l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SEQ_LE THEN
  MAP_EVERY EXISTS_TAC [`\n:num. a:real`; `x:num->real`] THEN
  ASM_REWRITE_TAC[SEQ_CONST] THEN ASM_MESON_TAC[]);;
```
### Informal statement
For all real numbers `a`, functions `x` from natural numbers to real numbers, real numbers `l`, and natural numbers `N`, if for all natural numbers `n`, `n` greater than or equal to `N` implies that `a` is less than or equal to `x(n)`, and `x` tends to `l` as `n` tends to infinity, then `a` is less than or equal to `l`.

### Informal sketch
The proof proceeds as follows:
- Assume that for all `n` greater than or equal to `N`, `a <= x(n)`, and `x` tends to `l`.
- Use `SEQ_LE` to prove the result.
- Introduce existential quantifiers for `n` and `x.`
- Rewrite using `SEQ_CONST`
- Apply MESON theorem prover to complete it.

### Mathematical insight
This theorem states that if a sequence `x(n)` is bounded below by `a` from some point `N` onwards, and `x(n)` converges to `l`, then `a` must be less than or equal to `l`. This is a fundamental property of limits, stating that the limit preserves inequalities.

### Dependencies
- Theorem: `SEQ_LE`
- Theorem: `SEQ_CONST`


---

## SUM_SWAP_0

### Name of formal statement
SUM_SWAP_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_SWAP_0 = prove
 (`!m n. sum(0,m) (\i. sum(0,n) (\j. a i j)) =
         sum(0,n) (\j. sum(0,m) (\i. a i j))`,
  INDUCT_TAC THEN
  ASM_SIMP_TAC[sum; SUM_CONST; REAL_MUL_RZERO; SUM_ADD]);;
```
### Informal statement
For all natural numbers `m` and `n`, the sum from `0` to `m` of the function that maps `i` to the sum from `0` to `n` of the function that maps `j` to `a i j` is equal to the sum from `0` to `n` of the function that maps `j` to the sum from `0` to `m` of the function that maps `i` to `a i j`.

### Informal sketch
The proof proceeds by induction on `m`.
- Base case: `m = 0`. Simplify using theorems about `sum`, `SUM_CONST`, `REAL_MUL_RZERO`, and `SUM_ADD`.
- Inductive step: Assume the theorem holds for `m`. Prove that it holds for `m+1`. Simplify using the induction hypothesis and theorems about `sum`, `SUM_CONST`, `REAL_MUL_RZERO`, and `SUM_ADD`.

### Mathematical insight
This theorem states that the order of summation can be swapped for a double summation where the bounds are independent of the summation variables. This is a fundamental property of summations and is crucial for manipulating and simplifying expressions involving sums.

### Dependencies
- `sum`
- `SUM_CONST`
- `REAL_MUL_RZERO`
- `SUM_ADD`


---

## SUM_SWAP

### Name of formal statement
SUM_SWAP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUM_SWAP = prove
 (`!m1 m2 n1 n2.
        sum(m1,m2) (\i. sum(n1,n2) (\j. a i j)) =
        sum(n1,n2) (\j. sum(m1,m2) (\i. a i j))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINDER_CONV o LAND_CONV o LAND_CONV)
    [ARITH_RULE `m = 0 + m`] THEN
  REWRITE_TAC[SUM_REINDEX; SUM_SWAP_0]);;
```
### Informal statement
For all `m1`, `m2`, `n1`, and `n2`, the sum from `i = m1` to `m2` of the sum from `j = n1` to `n2` of `a i j` is equal to the sum from `j = n1` to `n2` of the sum from `i = m1` to `m2` of `a i j`.

### Informal sketch
The proof proceeds by induction on the summation bounds. Notice that we are reindexing the summations, thus we need to properly manipulate initial offsets.
- The proof involves rewriting using arithmetic identities (`m = 0 + m`) to prepare for reindexing.
- The theorem `SUM_REINDEX` is applied to reindex the inner summation.
- Finally, `SUM_SWAP_0` probably deals with base case of empty summations that were introduced via reindexing.

### Mathematical insight
The theorem states that the order of summation can be interchanged for finite sums. This is a fundamental property used in various mathematical contexts, such as linear algebra and calculus.

### Dependencies
- `SUM_REINDEX`: For reindexing the summation.
- `SUM_SWAP_0`: Likely a base case for empty summations, introduced by `SUM_REINDEX`.
- `ARITH_RULE m = 0 + m`: For arithmetic rewriting.


---

## SER_SWAPDOUBLE_POS

### Name of formal statement
SER_SWAPDOUBLE_POS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SER_SWAPDOUBLE_POS = prove
 (`!z a l. (!m n. &0 <= a m n) /\ (!m. (a m) sums (z m)) /\ z sums l
           ==> ?s. (!n. (\m. a m n) sums (s n)) /\ s sums l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!m:num n. sum(0,n) (a m) <= z m` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SEQ_GE_CONST THEN
    EXISTS_TAC `\n. sum(0,n) (a(m:num))` THEN
    ASM_REWRITE_TAC[GSYM sums] THEN
    EXISTS_TAC `n:num` THEN X_GEN_TAC `p:num` THEN
    SIMP_TAC[GE; LEFT_IMP_EXISTS_THM; LE_EXISTS] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    ASM_SIMP_TAC[GSYM SUM_DIFF; SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m:num. &0 <= z m` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,n) (a(m:num))` THEN
    ASM_SIMP_TAC[SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. sum(0,n) z <= l` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SEQ_GE_CONST THEN
    EXISTS_TAC `\n. sum(0,n) z` THEN
    ASM_REWRITE_TAC[GSYM sums] THEN
    EXISTS_TAC `n:num` THEN X_GEN_TAC `p:num` THEN
    SIMP_TAC[GE; LEFT_IMP_EXISTS_THM; LE_EXISTS] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
    ASM_SIMP_TAC[GSYM SUM_DIFF; SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= l` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0,n) z` THEN
    ASM_SIMP_TAC[SUM_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?M N. !m n. M <= m /\ N <= n ==>
                        l - e <= sum(0,m) (\i. sum(0,n) (\j. a i j)) /\
                        sum(0,m) (\i. sum(0,n) (\j. a i j)) <= l`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN UNDISCH_TAC `z sums l` THEN
    REWRITE_TAC[sums; SEQ] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; GE; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
    SUBGOAL_THEN
     `?N. !m n. m < M /\ n >= N
                ==> abs(sum (0,n) (a m) - z m) < e / (&2 * &(M + 1))`
    MP_TAC THENL
     [SUBGOAL_THEN `&0 < e / (&2 * &(M + 1))` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_LT_MUL; ARITH;
                     ARITH_RULE `0 < n + 1`]; ALL_TAC] THEN
      SPEC_TAC(`e / (&2 * &(M + 1))`,`d:real`) THEN
      SPEC_TAC(`M:num`,`n:num`) THEN
      GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN
      INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN
      UNDISCH_TAC `!m:num. (a m) sums (z m)` THEN
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[sums; SEQ] THEN
      DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `N1:num`) THEN
      EXISTS_TAC `N0 + N1:num` THEN
      X_GEN_TAC `m:num` THEN X_GEN_TAC `p:num` THEN
      REWRITE_TAC[LT] THEN
      ASM_MESON_TAC[ARITH_RULE `a >= m + n ==> a >= m /\ a >= n:num`];
      ALL_TAC] THEN
    REWRITE_TAC[GE] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MAP_EVERY EXISTS_TAC [`M:num`; `N:num`] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `!s0. s0 <= s /\ s <= l /\ abs(s0 - l) < e
           ==> l - e <= s /\ s <= l`) THEN
    EXISTS_TAC `sum(0,M) (\i. sum (0,n) (\j. a i j))` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `M <= m:num` THEN
      SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      REWRITE_TAC[GSYM SUM_DIFF] THEN ASM_SIMP_TAC[SUM_POS]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum (0,m) z` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `e / &2 + e / &2` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[REAL_LE_REFL; GSYM REAL_MUL_2; REAL_DIV_LMUL;
               REAL_OF_NUM_EQ; ARITH_EQ]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!z. abs(x - z) <= e /\ abs(z - y) < e ==> abs(x - y) < e + e`) THEN
    EXISTS_TAC `sum(0,M) z` THEN ASM_SIMP_TAC[LE_REFL] THEN
    REWRITE_TAC[GSYM SUM_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&M * e / (&2 * &(M + 1))` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div; REAL_INV_MUL] THEN
      ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = (b * c) * a * d`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POS] THEN
      SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < n + 1`] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE; LE_ADD]] THEN
    W(fun (asl,w) -> MP_TAC(PART_MATCH lhand SUM_ABS_LE (lhand w))) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,M) (\n. e / (&2 * &(M + 1)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
      ASM_SIMP_TAC[ADD_CLAUSES; REAL_LT_IMP_LE];
      REWRITE_TAC[SUM_CONST; REAL_LE_REFL]]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. sum(0,m) (\i. (a:num->num->real) i n) <= l`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,M+m) (\i. sum(0,N+n+1) (\j. a i j))` THEN
    ASM_SIMP_TAC[LE_ADD] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= z + y`) THEN
    ASM_SIMP_TAC[SUM_POS] THEN MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN
    ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ &0 <= z ==> x <= y + z`) THEN
    ASM_SIMP_TAC[SUM_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(n,1) (\j. a (r:num) j)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_1; REAL_LE_REFL]; ALL_TAC] THEN
    SUBST1_TAC(ARITH_RULE `n = 0 + n`) THEN REWRITE_TAC[SUM_REINDEX] THEN
    ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
    ASM_SIMP_TAC[SUM_POS; REAL_LE_ADDL]; ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. ?s. (\m. a m n) sums s` MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[sums; GSYM convergent] THEN
    MATCH_MP_TAC SEQ_BCONV THEN CONJ_TAC THENL
     [MATCH_MP_TAC SEQ_BOUNDED_2 THEN
      MAP_EVERY EXISTS_TAC [`&0`; `l:real`] THEN ASM_SIMP_TAC[SUM_POS];
      REWRITE_TAC[mono] THEN DISJ1_TAC THEN
      SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
      REPEAT STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
      ASM_SIMP_TAC[SUM_POS; REAL_LE_ADDL]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `s:num->real` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?N. !n. N <= n
                    ==> l - e <= sum (0,n) s /\ sum(0,n) s <= l`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
    ONCE_REWRITE_TAC[SUM_SWAP_0] THEN DISCH_TAC THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!s0. l - e <= s0 /\ s0 <= s ==> l - e <= s`) THEN
      EXISTS_TAC `sum (0,n) (\j. sum (0,M) (\i. a i j))` THEN
      ASM_SIMP_TAC[LE_REFL] THEN MATCH_MP_TAC SUM_LE THEN
      X_GEN_TAC `r:num` THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SEQ_GE_CONST THEN
      EXISTS_TAC `\m. sum(0,m) (\m. a m (r:num))` THEN
      EXISTS_TAC `M:num` THEN ASM_REWRITE_TAC[GSYM sums] THEN
      SIMP_TAC[GE; LEFT_IMP_EXISTS_THM; LE_EXISTS] THEN
      ONCE_REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_DIFF)] THEN
      ASM_SIMP_TAC[SUM_POS; REAL_LE_ADDL]; ALL_TAC] THEN
    MATCH_MP_TAC SEQ_LE_CONST THEN
    EXISTS_TAC `\m. sum (0,n) (\j. sum (0,m) (\i. a i j))` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `0` THEN CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
      ONCE_REWRITE_TAC[SUM_SWAP_0] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum(0,m) z` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SEQ_SUM THEN X_GEN_TAC `m:num` THEN
    ASM_REWRITE_TAC[GSYM sums]; ALL_TAC] THEN
  REWRITE_TAC[sums; SEQ] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!e. &0 < e
        ==> (?N. !n. N <= n ==> l - e <= sum (0,n) s /\ sum (0,n) s <= l)` THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[GE] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `d < e ==> l - d <= x /\ x <= l ==> abs(x - l) < e`) THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;
```
### Informal statement
For all `z`, `a`, and `l`, if for all `m` and `n`, `a m n` is a non-negative real number, and for all `m`, the series `a m` sums to `z m`, and the series `z` sums to `l`, then there exists a function `s` such that for all `n`, the series `\m. a m n` sums to `s n` and the series `s` sums to `l`.

### Informal sketch
The proof demonstrates that under the given conditions, we can swap the order of summation for a double series of non-negative real numbers. 

- First, establish bounds: Show that `sum(0,n) (a m)` is less than or equal to `z m`, and `0 <= z m`. Also, `sum(0,n) z <= l` and `0 <= l`. These are obtained by using `SEQ_GE_CONST`, `REAL_LE_TRANS`, and properties of `SUM_POS`.
- Prove that for any `e > 0`, there exist `M` and `N` such that for all `m >= M` and `n >= N`, `l - e <= sum(0,m) (\i. sum(0,n) (\j. a i j)) <= l`. This is done by exploiting the convergence of `z` to `l` and `a m` to `z m`, using `sums` and `SEQ`. Real number arithmetic and properties of the sum are used extensively including `REAL_LT_DIV`, `REAL_OF_NUM_LT`, `REAL_LT_MUL`, `ARITH`, `SUM_DIFF`, `SUM_POS`, `REAL_LE_TRANS`, `SUM_LE`, `SUM_ABS_LE`, and `ADD_CLAUSES`.
- Argue that for all `m` and `n`, `sum(0,m) (\i. a i n) <= l` utilizing the previous results and properties of sums such as `SUM_DIFF`, `SUM_POS` and `SUM_LE`.
- Show that for all `n`, there exists `s` such that the series `\m. a m n` sums to `s`. This relies on `sums` and the `convergent` condition and bounding properties (`SEQ_BOUNDED_2`) and monotonicity (`mono`).
- Prove the existence of `N` such that for all `n >= N`, `l - e <= sum (0,n) s <= l` for any `e > 0` by using the previous results and swapping the order of summations (`SUM_SWAP_0`), applying `SEQ_GE_CONST` and `SEQ_LE_CONST` with properties of double sums (`SUM_LE`).
- Finally, show that `s` sums to `l` using `sums` and `SEQ`, combined with the epsilon argument.

### Mathematical insight
This theorem formalizes the interchange of order of summation for non-negative double series. The condition of non-negativity is crucial to ensure that the double series converges unconditionally, which then guarantees that the iterated sums converge to the same limit.

### Dependencies
- `sums`
- `SEQ_GE_CONST`
- `REAL_LE_TRANS`
- `SUM_POS`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `REAL_LT_MUL`
- `ARITH`
- `SUM_DIFF`
- `SUM_LE`
- `SUM_ABS_LE`
- `ADD_CLAUSES`
- `convergent`
- `SEQ_BOUNDED_2`
- `mono`
- `SUM_SWAP_0`
- `SEQ_SUM`

### Porting notes (optional)
The core of this theorem lies in manipulating inequalities and limits, which may benefit from specific support for real analysis in other proof assistants. The tactics involving `REAL_ARITH` performs complex reasoning about inequalities in real numbers which may need to be replicated using different strategies in other systems. The tactic `ASM_MESON_TAC` may need an equivalent from Z3 or other existing solvers.


---

## COT_PARTIAL_FRACTIONS_FROM1

### Name of formal statement
COT_PARTIAL_FRACTIONS_FROM1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_PARTIAL_FRACTIONS_FROM1 = prove
 (`~integer x
    ==> (\n. (&2 * x pow 2) / (x pow 2 - &(n + 1) pow 2)) sums
        (pi * x) * cot (pi * x) - &1`,
  DISCH_TAC THEN
  SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(integer x)` THEN
    REWRITE_TAC[TAUT `(~b ==> ~a) <=> (a ==> b)`] THEN
    SIMP_TAC[integer; REAL_ABS_NUM; REAL_OF_NUM_EQ; GSYM EXISTS_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_PARTIAL_FRACTIONS) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SER_OFFSET) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b * b) * c = a * (b * b) * c`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ENTIRE; REAL_MUL_RID] THEN
  REAL_ARITH_TAC);;
```

### Informal statement
If `x` is not an integer, then the series with terms `(2 * x^2) / (x^2 - (n + 1)^2)` sums to `pi * x * cot(pi * x) - 1`.

### Informal sketch
The proof demonstrates that the infinite sum of a series involving `x` converges to an expression involving the cotangent function, given that `x` is not an integer.

- Assume `x` is not an integer, i.e., `~integer x`.
- Prove `x` is not zero `~(x = &0)`. This is done by contradiction using `integer`, `REAL_ABS_NUM`, `REAL_OF_NUM_EQ` and `EXISTS_REFL`.
- Use `COT_PARTIAL_FRACTIONS` to obtain that `pi * x * cot(pi * x) = 1 + sum (\n. (2 * x^2) / (x^2 - (n + 1)^2))`.
- Apply `SUM_SUMMABLE` to verify that the sum converges.
- Reindex the sum using `SER_OFFSET` with an offset of `1`.
- Use `SUM_UNIQ` to show that if two sums are equal and summable, their values are equal.
- Simplify using arithmetic identities such as `REAL_POW_2`, `REAL_MUL_LZERO`, `REAL_SUB_RZERO`, `real_div`, `REAL_MUL_RINV`, `REAL_ENTIRE`, `REAL_MUL_RID` until the goal is reached.

### Mathematical insight
This theorem provides a partial fraction expansion of the cotangent function, expressing `pi * x * cot(pi * x) - 1` as an infinite sum. This representation is useful in various areas of mathematics such as complex analysis, number theory, and special functions.

### Dependencies
- `COT_PARTIAL_FRACTIONS`
- `SUM_SUMMABLE`
- `SER_OFFSET`
- `SUM_UNIQ`
- `integer`
- `REAL_ABS_NUM`
- `REAL_OF_NUM_EQ`
- `REAL_POW_2`
- `REAL_MUL_LZERO`
- `REAL_SUB_RZERO`
- `real_div`
- `REAL_MUL_RINV`
- `REAL_ENTIRE`
- `REAL_MUL_RID`


---

## COT_ALT_POWSER

### Name of formal statement
COT_ALT_POWSER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_ALT_POWSER = prove
 (`!x. &0 < abs(x) /\ abs(x) < &1
       ==> ?s. (!n. (\m. &2 * (x pow 2 / &(m + 1) pow 2) pow (n + 1))
                    sums s n) /\
               s sums --((pi * x) * cot(pi * x) - &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SER_SWAPDOUBLE_POS THEN
  EXISTS_TAC `\n. (--(&2) * x pow 2) / (x pow 2 - &(n + 1) pow 2)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[REAL_POS; REAL_POW_LE; REAL_LE_MUL;
             REAL_POW_2; REAL_LE_DIV; REAL_LE_SQUARE];
    X_GEN_TAC `m:num` THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV)
     [GSYM REAL_NEG_NEG] THEN
    REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
    MATCH_MP_TAC SER_NEG THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC COT_PARTIAL_FRACTIONS_SUBTERM THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    REWRITE_TAC[real_div; REAL_MUL_LNEG] THEN
    MATCH_MP_TAC SER_NEG THEN
    REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC COT_PARTIAL_FRACTIONS_FROM1 THEN
    UNDISCH_TAC `&0 < abs x` THEN UNDISCH_TAC `abs x < &1` THEN
    ONCE_REWRITE_TAC[TAUT `a ==> b ==> ~c <=> c ==> ~(a /\ b)`] THEN
    SIMP_TAC[integer; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ARITH_TAC]);;
```

### Informal statement
For all real numbers `x`, if the absolute value of `x` is greater than 0 and the absolute value of `x` is less than 1, then there exists a real number `s` such that the series whose `n`-th term is given by the function mapping `m` to `2 * (x^2 / (m + 1)^2)^(n + 1)` sums to `s` for all n, and `s` equals `-(pi * x) * cot(pi * x) - 1`.

### Informal sketch
The proof demonstrates the existence of a limit `s` for a given series representation related to `cot(pi * x)`.

- The proof starts by stripping the quantifiers and assumption.
- It then applies `SER_SWAPDOUBLE_POS`, which likely rewrites the expression using properties related to infinite series and double summations of positive terms.
- It continues by introducing the witness function `\n. (--(&2) * x pow 2) / (x pow 2 - &(n + 1) pow 2)` which should be understood as the general term of a series representation of `-(pi * x) * cot(pi * x) - 1`.
- The goal is then rewritten using basic arithmetic properties with `REWRITE_TAC[]`. This step probably rearranges the terms to match the expected form for the series convergence proof. The proof now reduces to demonstrating pointwise convergence, by splitting the goal into multiple subgoals which are then attacked separately.
- Multiple subgoals are simplified utilizing lemmas about real numbers (`REAL_POS`, `REAL_POW_LE`, `REAL_LE_MUL`, `REAL_POW_2`, `REAL_LE_DIV`, `REAL_LE_SQUARE`, `REAL_NEG_NEG`, `real_div`, `REAL_MUL_LNEG`).
- The proof uses `COT_PARTIAL_FRACTIONS_SUBTERM` and `COT_PARTIAL_FRACTIONS_FROM1` which are likely lemmas that relate the partial fraction expansion of `cot(pi * x)` to the introduced series representation. Also `SER_NEG` is used, wich allows to show convergence of a series by showing convergence of its negated counterpart.
- Finally, some discharging of the hypothesis occurs to complete the proof.

### Mathematical insight
The theorem essentially states that in a certain range for x, `-(pi * x) * cot(pi * x) - 1` has a representation as an infinite series given by a specific term involving `x pow 2 / &(m + 1) pow 2`. This is useful in complex analysis and special function theory for expressing `cot(pi * x)` as an infinite sum of simpler terms.

### Dependencies
- `REAL_POS`
- `REAL_POW_LE`
- `REAL_LE_MUL`
- `REAL_POW_2`
- `REAL_LE_DIV`
- `REAL_LE_SQUARE`
- `GSYM REAL_NEG_NEG`
- `real_div`
- `REAL_MUL_LNEG`
- `SER_NEG`
- `COT_PARTIAL_FRACTIONS_SUBTERM`
- `REAL_LTE_TRANS`
- `REAL_OF_NUM_LE`
- `COT_PARTIAL_FRACTIONS_FROM1`
- `integer`
- `LEFT_IMP_EXISTS_THM`
- `REAL_OF_NUM_LT`
- `SER_SWAPDOUBLE_POS`

### Porting notes (optional)
The main challenge in other proof assistants would be establishing the series expansion for the cotangent function and the partial fraction decomposition (`COT_PARTIAL_FRACTIONS_SUBTERM`, `COT_PARTIAL_FRACTIONS_FROM1`). The manipulation of series convergence also might require some effort. The proof relies heavily on real number lemmas, so a good library for real analysis will be helpful.


---

## SER_INSERTZEROS

### Name of formal statement
SER_INSERTZEROS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SER_INSERTZEROS = prove
 (`(\n. c(2 * n)) sums l
   ==> (\n. if ODD n then &0 else c(n)) sums l`,
  REWRITE_TAC[sums; SEQ; GE] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `2 * N` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  DISJ_CASES_THEN MP_TAC (SPEC `n:num` EVEN_OR_ODD) THENL
   [REWRITE_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM SUM_GROUP)] THEN
    REWRITE_TAC[SUM_2; ODD_ADD; ODD_MULT; ARITH_ODD; REAL_ADD_RID] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `2 * N <= 2 * m` THEN ARITH_TAC;
    REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[GSYM ODD_EXISTS] THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] (GSYM SUM_GROUP)] THEN
    REWRITE_TAC[SUM_2; ODD_ADD; ODD_MULT; ARITH_ODD; REAL_ADD_RID] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `0 + 2 * m = 2 * (0 + m)`] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 sum)] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `2 * N <= SUC(2 * m)` THEN ARITH_TAC]);;
```
### Informal statement
If the series `c(2 * n)` sums to a limit `l`, then the series where odd-indexed terms are zero and even-indexed terms are `c(n)` sums to the same limit `l`. In other words, if `(\n. c(2 * n))` sums to `l`, then `(\n. if ODD n then &0 else c(n))` sums to `l`.

### Informal sketch
The proof proceeds by assuming that the series `c(2 * n)` sums to a limit `l`, and then showing that the series `if ODD n then &0 else c(n)` also sums to `l`.

- Assume `c(2 * n)` sums to `l`.
- Introduce a real number `e` and assume it is greater than zero (`e > 0`).
- From the assumption that `c(2 * N)` sums to `l`, apply the definition of convergence for series: for every `e > 0`, there exists a natural number `N` such that for all `n >= N`, the absolute value of the difference between `l` and the partial sum up to `n` of `c(2 * i)` is less than `e`.
- Apply the definition of `sums`.
- Choose `N` such that `abs(l - sum(0..N) (\i. c(2 * i))) < e`.
- Show that there exists a value `2 * N` such that if `n > 2 * N` then `abs(l - sum(0..n) (\i. if ODD i then &0 else c(i))) < e`.
- Perform a case split on whether `n` is odd or even.
  - If `n` is even, say `n = 2 * m` for some `m`. Rewrite using the fact that the sum from `0` to `2 * m` of the sequence `if ODD i then &0 else c(i)` is equal to the sum from `0` to `m` of `c(2 * i)`. Now show that if `2 * N <= 2 * m` that is `N <= m` then `abs(l - sum(0..m) (\i. c(2 * i))) < e`.
  - If `n` is odd, say `n = 2 * m + 1` for some `m`. Rewrite using the fact that the sum from `0` to `2 * m + 1` of the sequence `if ODD i then &0 else c(i)` is equal to the sum from `0` to `m` of `c(2 * i)` plus zero in last term. Now show that if `2 * N <= 2 * m + 1` then `abs(l - sum(0..m) (\i. c(2 * i))) < e`.

### Mathematical insight
The theorem states that if a series converges, inserting zeros between the terms does not change the limit. This is because the inserted zeros do not contribute to the partial sums, effectively keeping the sequence of partial sums the same (or a subsequence of it).

### Dependencies
- `sums`: Definition of the convergence of a series.
- `SEQ`: `n < SUC m` is equivalent to `n <= m`.
- `GE`: `n <= m` is equivalent to `m IN num_GE n`.
- `EVEN_EXISTS`: Theorem stating that `EVEN n` exists an `m` such that `n = 2 * m`.
- `ODD_EXISTS`: Theorem stating that `ODD n` exists an `m` such that `n = 2 * m + 1`.
- `LEFT_IMP_EXISTS_THM`: Theorem for existential quantification over LHS of implication.
- `MULT_SYM`: Symmetry of multiplication.
- `SUM_GROUP`: Group properties of `sum`.
- `SUM_2`: Theorem about splitting summation range up to 2.
- `ODD_ADD`: Parity property of addition with odd numbers.
- `ODD_MULT`: Parity property of multiplication with odd numbers.
- `ARITH_ODD`: Arithmetical property of odd numbers.
- `REAL_ADD_RID`: Right identity of addition of real numbers.
- `CONJUNCT2 sum`: conjuncted properties of sum.
- `EVEN_OR_ODD`: Theorem formalizing that every number is either even or odd.

### Porting notes (optional)
- The `REWRITE_TAC` tactics rely on the specific rewrite rules present in the HOL Light library. In other proof assistants, corresponding rewrite rules or lemmas need to be provided. Automation might be needed to handle the arithmetic reasoning instead of `ARITH_TAC`.
- The proof relies on discharging assumptions introduces by `DISCH_TAC` and similar tactics. The specific implementation of discharging assumptions and applying them later with (`FIRST_X_ASSUM(MP_TAC o SPEC `e:real`)`) might need adaptation based on how assumptions are handled in the target proof assistant.


---

## COT_POWSER_SQUARED_FORM

### Name of formal statement
COT_POWSER_SQUARED_FORM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_POWSER_SQUARED_FORM = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. &2 * (x / pi) pow (2 * (n + 1)) *
                suminf (\m. inv (&(m + 1) pow (2 * (n + 1)))))
           sums --(x * cot x - &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x / pi` COT_ALT_POWSER) THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  SIMP_TAC[real_abs; REAL_LT_IMP_LE; PI_POS] THEN
  REWRITE_TAC[GSYM real_abs] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ; PI_POS] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; PI_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `s sums --(x * cot(x) - &1)` THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SER_CMUL o SPEC `n:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2 * (x / pi) pow (2 * (n + 1)))`) THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ABS_CONV o
                   RAND_CONV o ONCE_DEPTH_CONV)
      [REAL_POW_DIV] THEN
  REWRITE_TAC[REAL_POW_POW] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ABS_CONV o
                   RAND_CONV o ONCE_DEPTH_CONV)
      [real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `a * &2 * b * c = c * ((&2 * b) * a)`] THEN
  SUBGOAL_THEN
   `~(&2 * (x / pi) pow (2 * (n + 1)) = &0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ; REAL_POW_EQ_0] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN DISJ1_TAC THEN
    REWRITE_TAC[real_div; REAL_ENTIRE; REAL_INV_EQ_0] THEN
    ASM_SIMP_TAC[PI_POS; REAL_LT_IMP_NZ;
                 snd(EQ_IMP_RULE(SPEC_ALL REAL_ABS_NZ))];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_UNIQ) THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (&2 * (x / pi) pow (2 * (n + 1)))`) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
   [AC REAL_MUL_AC `a * b * c = (a * b) * c`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC]);;
```

### Informal statement
For all real numbers `x`, if the absolute value of `x` is greater than 0 and the absolute value of `x` is less than pi, then the infinite series whose `n`-th term is `2 * (x / pi) ^ (2 * (n + 1)) * suminf (\m. inv (&(m + 1) pow (2 * (n + 1))))` sums to `-(x * cot x - &1)`.

### Informal sketch
The proof establishes that the given power series sums to `-(x * cot x - &1)` under the condition that `0 < abs x < pi`.

- Start by specializing the alternating power series representation of `cot x`, namely `COT_ALT_POWSER`, with `x / pi`.
- Simplify the absolute value expression `abs (x / pi)` using properties of real absolute values.
- Apply the condition `0 < abs x < pi` to obtain `abs (x / pi) < 1` and `0 < abs(x / pi)`.
- Perform algebraic manipulations to align the summations and apply the equality `EQ_IMP` and `AP_THM_TAC`, `AP_TERM_TAC` to equate the two sides of `sums`.
- Show that the series is uniquely summable `SUM_UNIQ`.
- Manipulate the series using `SER_CMUL` to factor constants out of the summation.
- Simplify the expression by multiplying both sides by the inverse of `2 * (x / pi) pow (2 * (n + 1))`.
- Justify the multiplication by demonstrating that `2 * (x / pi) pow (2 * (n + 1))` is not equal to zero by showing that `x/pi` is non-zero using assumptions `PI_POS` and `REAL_LT_IMP_NZ` and `REAL_ABS_NZ`.
- Rearrange the terms using associativity and commutativity of real multiplication.
- Further simplify the expression by canceling multiplicative inverses.

### Mathematical insight
This theorem provides a specific power series representation for `x * cot x - 1`. This representation is crucial for analytic manipulations involving the cotangent function. The condition `0 < abs x < pi` ensures the convergence of the power series and the validity of the representation.

### Dependencies
- `COT_ALT_POWSER`
- `real_abs`
- `REAL_LT_IMP_LE`
- `PI_POS`
- `GSYM real_abs`
- `REAL_LT_RDIV_EQ`
- `REAL_LT_LDIV_EQ`
- `REAL_MUL_LZERO`
- `REAL_MUL_LID`
- `REAL_DIV_LMUL`
- `REAL_LT_IMP_NZ`
- `FUN_EQ_THM`
- `REAL_POW_DIV`
- `REAL_POW_POW`
- `real_div`
- `REAL_ARITH`
- `REAL_ENTIRE`
- `REAL_OF_NUM_EQ`
- `ARITH_EQ`
- `REAL_POW_EQ_0`
- `DE_MORGAN_THM`
- `REAL_INV_EQ_0`
- `REAL_MUL_RINV`
- `REAL_MUL_RID`
- `SUM_UNIQ`
- `REAL_MUL_ASSOC`

### Porting notes (optional)
When porting this theorem, pay close attention to the handling of infinite series (`suminf`). The target proof assistant must have adequate support for defining and manipulating infinite sums, including convergence criteria and term-by-term operations like multiplication by a constant. Also, ensure the real number library provides similar theorems for absolute value, division, and exponentiation for real numbers. The automation may need to be adjusted, especially for rewriting associativity and commutativity of multiplication.


---

## COT_POWSER_SQUAREDAGAIN

### Name of formal statement
COT_POWSER_SQUAREDAGAIN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_POWSER_SQUAREDAGAIN = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1
                 else --(&2) *
                      suminf (\m. inv (&(m + 1) pow (2 * n))) /
                      pi pow (2 * n)) *
                x pow (2 * n))
           sums (x * cot(x))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_POWSER_SQUARED_FORM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\n. if n = 0 then &1 else
         --(&2 * (x / pi) pow (2 * n) *
                 suminf (\m. inv (&(m + 1) pow (2 * n)))))
    sums (sum(0,1) (\n. if n = 0 then &1 else
                        --(&2 * (x / pi) pow (2 * n) *
                           suminf (\m. inv (&(m + 1) pow (2 * n))))) +
          suminf (\n. if n + 1 = 0 then &1 else
                        --(&2 * (x / pi) pow (2 * (n + 1)) *
                           suminf (\m. inv (&(m + 1) pow (2 * (n + 1)))))))`
  MP_TAC THENL
   [MATCH_MP_TAC SER_OFFSET_REV THEN
    REWRITE_TAC[ARITH_RULE `~(n + 1 = 0)`] THEN
    REWRITE_TAC[summable] THEN
    EXISTS_TAC `x * cot(x) - &1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_1; ARITH_RULE `~(n + 1 = 0)`] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[REAL_ARITH `&1 + x - &1 = x`] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; real_pow; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_MUL_LNEG] THEN AP_TERM_TAC THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_AC]);;
```
### Informal statement
For all real numbers `x`, if the absolute value of `x` is greater than 0 and the absolute value of `x` is less than pi, then the series defined by the function that maps `n` to `1` if `n` equals `0`, and to `-2` times the infinite sum of `1 / ((m + 1) ^ (2 * n))` over all `m`, divided by `pi ^ (2 * n)` otherwise, all multiplied by `x ^ (2 * n)`, sums to `x * cot(x)`.

### Informal sketch
The proof shows that the power series representation of `x * cot(x)` is valid within the given interval.

- Start with the assumption that `0 < abs(x) < pi`.
- Apply `COT_POWSER_SQUARED_FORM` to relate `x * cot(x)` to a negated series expression.
- Apply `SER_NEG` to distribute the negation within the series.
- Simplify using `REAL_NEG_NEG` to remove double negations.
- The main goal involves showing that a specific series, namely `(\n. if n = 0 then &1 else --(&2 * (x / pi) pow (2 * n) * suminf (\m. inv (&(m + 1) pow (2 * n)))))` sums to `sum(0,1) (\n. if n = 0 then &1 else --(&2 * (x / pi) pow (2 * n) *suminf (\m. inv (&(m + 1) pow (2 * n))))) + suminf (\n. if n + 1 = 0 then &1 else --(&2 * (x / pi) pow (2 * (n + 1)) * suminf (\m. inv (&(m + 1) pow (2 * (n + 1)))))`.
- Use `SER_OFFSET_REV` to shift the summation index.
- Simplify using the fact that `~(n + 1 = 0)`.
- Use the definition `summable` and rewrite and simplify the expression.
- Use `SUM_1` to resolve the sum from 0 to 1.
- Apply `SUM_UNIQ` and simplify the real arithmetic.
- Apply a series of rewriting tactics, applying `EQ_IMP`, create function equalities and then `X_GEN_TAC` to generate a number variable.
- Consider cases when `n = 0` and `n <> 0`, and simplify the expression using arithmetic rules to complete the proof.

### Mathematical insight
This theorem provides the power series expansion of `x * cot(x)`. This expansion is fundamental in complex analysis and calculus and is used for analyzing the behavior of the cotangent function near the origin and for computing certain series and integrals.

### Dependencies
- `COT_POWSER_SQUARED_FORM`
- `SER_NEG`
- `SER_OFFSET_REV`
- `SUM_UNIQ`
- `EQ_IMP`
- `SUM_1`
- `summable`
- `REAL_NEG_NEG`
- `ARITH_RULE`
- `MULT_CLAUSES`
- `real_pow`
- `REAL_MUL_LID`
- `REAL_POW_DIV`
- `REAL_MUL_LNEG`
- `real_div`
- `REAL_INV_MUL`
- `REAL_INV_INV`
- `REAL_MUL_AC`

### Porting notes (optional)
- The critical aspect to porting this theorem lies in the definitions of series summation (`suminf` and `sum`), convergence (`summable`), and the real number arithmetic properties. Ensure that the target proof assistant has equivalent definitions and sufficient automation for handling real number arithmetic and series manipulation.
- The `GEN_TAC` and `DISCH_TAC` are common tactics. The `FIRST_ASSUM`, `MP_TAC`, `MATCH_MP_TAC`, and `SUBST1_TAC` are related to applying modus ponens and substitution. The `REWRITE_TAC` depends on the database being rewritten. The `COND_CASES_TAC` is very powerful for splitting conditions.


---

## COT_X_POWSER

### Name of formal statement
COT_X_POWSER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COT_X_POWSER = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1 else if ODD n then &0 else
                 --(&2) * suminf (\m. inv (&(m + 1) pow n)) / pi pow n) *
                x pow n)
           sums (x * cot(x))`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COT_POWSER_SQUAREDAGAIN) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [ARITH_RULE `(n = 0) <=> (2 * n = 0)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_INSERTZEROS) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO]);;
```

### Informal statement
For all real numbers `x`, if the absolute value of `x` is greater than 0 and less than pi, then the series defined by the function that maps each natural number `n` to (if `n` is 0 then 1, else if `n` is odd then 0, else -2 times the infinite sum of `1 / (m + 1)^n `for `m` from 0 to infinity, divided by pi to the power of `n`) times `x` to the power of `n`, sums to `x * cot(x)`.

### Informal sketch
The proof demonstrates that the power series representation of `x * cot(x)` converges to `x * cot(x)` for `0 < abs(x) < pi`. The main steps are:

- Start with assuming `0 < abs(x) /\ abs(x) < pi`.
- Use `COT_POWSER_SQUAREDAGAIN` to relate the power series to a squared term.
- Apply several rewrite rules and theorems to simplify the expression, including arithmetic rules (e.g., `(n = 0) <=> (2 * n = 0)`).
- Insert zeros into the series using `SER_INSERTZEROS`.
- Use theorems like `EQ_IMP` and `FUN_EQ_THM` to manipulate equality and function equality.
- Perform case analysis on `n = 0` and simplify based on whether `n` is 0 or not.
- Apply conditional cases and rewrite with `REAL_MUL_LZERO` to handle cases concerning multiplication by 0.

### Mathematical insight
This theorem provides the power series expansion of the function `x * cot(x)` within a specific interval. This representation is useful for analyzing the behavior of `cot(x)` near the origin and for various applications in complex analysis and numerical computations. Understanding the power series allows approximations and facilitates computations involving cotangent function.

### Dependencies
- `COT_POWSER_SQUAREDAGAIN`
- `SER_INSERTZEROS`
- `EQ_IMP`
- `FUN_EQ_THM`
- `ARITH`
- `REAL_MUL_LZERO`


---

## TAN_COT_DOUBLE

### Name of formal statement
TAN_COT_DOUBLE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAN_COT_DOUBLE = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi / &2
        ==> (tan(x) = cot(x) - &2 * cot(&2 * x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(sin x = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[SIN_ZERO] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; REAL_LT_REFL] THEN
    DISJ1_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
    SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(cos x = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[COS_ZERO] THEN
    MAP_EVERY UNDISCH_TAC [`abs x < pi / &2`; `&0 < abs x`] THEN
    REWRITE_TAC[IMP_IMP] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM; NOT_EVEN] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    DISJ2_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
    SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(sin(&2 * x) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[SIN_ZERO] THEN
    MAP_EVERY UNDISCH_TAC [`abs x < pi / &2`; `&0 < abs x`] THEN
    REWRITE_TAC[IMP_IMP] THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
    SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_EQ_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
    ASM_CASES_TAC `m = 0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; REAL_MUL_LZERO; REAL_LT_REFL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISJ2_TAC THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = b * a * c`] THEN
    SIMP_TAC[REAL_LT_DIV2_EQ; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH;
             REAL_OF_NUM_LT] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
    SIMP_TAC[REAL_LT_RMUL_EQ; PI_POS; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[tan; cot] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
  EXISTS_TAC `sin(&2 * x)` THEN ASM_REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(d * e - &2 * f * g) * h = h * d * e - &2 * f * (h * g)`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `sin(x)` THEN
  ASM_SIMP_TAC[REAL_SUB_RDISTRIB; GSYM REAL_MUL_ASSOC;
               REAL_MUL_LINV; REAL_MUL_RID] THEN
  GEN_REWRITE_TAC LAND_CONV
   [AC REAL_MUL_AC `a * b * c * d = a * c * d * b`] THEN
  MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `cos(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RID] THEN
  REWRITE_TAC[SIN_DOUBLE; COS_DOUBLE; REAL_POW_2] THEN
  REWRITE_TAC[REAL_ARITH
   `((&2 * s * c) * c - &2 * (c * c - s * s) * s) * c =
    &2 * c * s * s * s`] THEN
  REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
For all real numbers `x`, if `0 < |x|` and `|x| < pi / 2`, then `tan(x) = cot(x) - 2 * cot(2 * x)`.

### Informal sketch
The proof establishes the trigonometric identity `tan(x) = cot(x) - 2 * cot(2 * x)` under the condition that `0 < |x| < pi / 2`. The conditions `sin(x) != 0`, `cos(x) != 0`, and `sin(2 * x) != 0` are established first. The main steps are:
- Show `sin(x) != 0` under the assumptions `0 < abs(x) /\ abs(x) < pi / &2`. This proceeds by contradiction: Assume `sin x = 0`, then `x = n * pi` for some integer `n`.  Using the assumption `abs(x) < pi / 2` it is shown that then `n = 0` and hence `abs(x) = 0`, which is a contradiction
- Similarly show `cos(x) != 0`. Assume `cos x = 0`, then `x = (2 * n + 1) * pi / 2`. Using the assumption `abs(x) < pi / 2` it is shown that `n = 0` and hence `abs(x) = pi / 2` which is a contradiction
- Similarly show `sin(2 * x) != 0`. Assume `sin(2 * x) = 0`, then `2 * x = n * pi` for some integer `n`.  Using the assumption `abs(x) < pi / 2` it is shown that then `n = 0` and hence `abs(x) = 0`, which is a contradiction.
- Rewrite `tan` and `cot` in terms of `sin` and `cos`.
- Simplify the right-hand side `cot(x) - 2 * cot(2 * x)` using the double angle formulas for `sin` and `cos` until it is equal to `tan(x)`.

### Mathematical insight
This theorem relates the tangent and cotangent functions at `x` and `2x`. It is a standard trigonometric identity, useful for deriving series expansions and simplifying trigonometric expressions.

### Dependencies
- `tan`
- `cot`
- `SIN_ZERO`
- `DE_MORGAN_THM`
- `OR_EXISTS_THM`
- `REAL_ARITH`
- `REAL_LE_MUL`
- `REAL_LE_DIV`
- `REAL_LT_IMP_LE`
- `PI_POS`
- `REAL_POS`
- `EVEN_EXISTS`
- `MULT_CLAUSES`
- `REAL_MUL_LZERO`
- `REAL_LT_REFL`
- `REAL_LT_RMUL_EQ`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`
- `COS_ZERO`
- `IMP_IMP`
- `NOT_EVEN`
- `ODD_EXISTS`
- `REAL_ABS_MUL`
- `REAL_ABS_NUM`
- `REAL_MUL_SYM`
- `GSYM REAL_EQ_RDIV_EQ`
- `REAL_LT_DIV2_EQ`
- `REAL_DIV_LMUL`
- `REAL_OF_NUM_EQ`
- `SIN_DOUBLE`
- `COS_DOUBLE`
- `REAL_POW_2`
- `real_div`
- `REAL_MUL_RINV`
- `REAL_MUL_RID`
- `REAL_SUB_RDISTRIB`
- `GSYM REAL_MUL_ASSOC`
- `REAL_MUL_LINV`


---

## TAN_POWSER_WEAK

### Name of formal statement
TAN_POWSER_WEAK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAN_POWSER_WEAK = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi / &2
       ==> (\n. (if EVEN n then &0 else
                 &2 * (&2 pow (n + 1) - &1) *
                 suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1)) *
                x pow n)
           sums (tan x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` COT_X_POWSER) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `pi / &2` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(x)` o MATCH_MP SER_CMUL) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ABS_NZ; REAL_MUL_LID] THEN
  MP_TAC(SPEC `&2 * x` COT_X_POWSER) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_NUM;
                 REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(x)` o MATCH_MP SER_CMUL) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
   [AC REAL_MUL_AC `a * (b * c) * d = (a * c) * b * d`] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ABS_NZ; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_SUB) THEN
  ASM_SIMP_TAC[GSYM TAN_COT_DOUBLE] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ASSUME_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SER_OFFSET) THEN
  ASM_REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[real_pow; REAL_MUL_RID; REAL_SUB_REFL; REAL_SUB_RZERO] THEN
  REWRITE_TAC[ODD_ADD; ARITH_ODD; ADD_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[NOT_ODD] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_SUB_REFL] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x' * m2 * s * xp * x - x' * m2 * s * pn * t * xp * x =
    (x' * x) * --m2 * (t * pn - &1) * s * xp`] THEN
  ASM_SIMP_TAC[REAL_NEG_NEG; REAL_MUL_LINV; REAL_ABS_NZ; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_MUL_AC]);;
```

### Informal statement
For all real numbers `x`, if `0 < abs(x)` and `abs(x) < pi / 2`, then the series defined by the function mapping `n` to:
if `n` is even then `0`, else `2 * (2^(n+1) - 1) * (sum over m of 1/((m+1)^(n+1))) / pi^(n+1) * x^n`
sums to `tan x`.

### Informal sketch
The proof establishes the power series expansion for `tan x` under the given constraints.
- The proof starts with the power series expansion of `cot x` (`COT_X_POWSER`).
- It manipulates the power series of `cot x` to derive the power series for `tan x`.
- Using `SER_CMUL`, the theorem applies scalar multiplication to the power series and then simplifies using identities like `REAL_MUL_LINV` and `REAL_MUL_LID`.
- It uses `SER_SUB` to represent `tan x` as a difference of two cotangent series involving `x` and `2 * x` and simplify using `TAN_COT_DOUBLE` identity to eliminate explicit cotangents.
- It uses `SUM_UNIQ` to obtain equality when sums are over the same index and summable in the same range.
- It uses `SER_OFFSET` to shift indices.
- The series `SUM_1` is evaluated.
- Simplification steps involve rewriting with `real_pow` and distribution.
- Case splitting on whether `n` is even or odd reduces the series to the desired form.

### Mathematical insight
The theorem `TAN_POWSER_WEAK` provides a power series representation for the tangent function, valid within a specific interval around zero. This representation is useful for approximating the tangent function, studying its analytic properties, and for various other applications in mathematics and physics.

### Dependencies
- `COT_X_POWSER`
- `REAL_LT_TRANS`
- `REAL_LT_LDIV_EQ`
- `REAL_OF_NUM_LT`
- `PI_POS`
- `SER_CMUL`
- `REAL_MUL_ASSOC`
- `REAL_MUL_LINV`
- `REAL_ABS_NZ`
- `REAL_MUL_LID`
- `REAL_ABS_MUL`
- `REAL_ABS_NUM`
- `REAL_LT_MUL`
- `REAL_LT_RDIV_EQ`
- `TAN_COT_DOUBLE`
- `SUM_UNIQ`
- `SUM_SUMMABLE`
- `SER_OFFSET`
- `SUM_1`
- `real_pow`
- `REAL_MUL_RID`
- `REAL_SUB_REFL`
- `REAL_SUB_RZERO`
- `ODD_ADD`
- `ARITH_ODD`
- `ADD_EQ_0`
- `ARITH_EQ`
- `FUN_EQ_THM`
- `NOT_ODD`
- `REAL_MUL_LZERO`
- `REAL_MUL_RZERO`
- `REAL_POW_ADD`
- `REAL_POW_1`
- `REAL_POW_MUL`
- `REAL_MUL_ASSOC`
- `REAL_NEG_NEG`

### Porting notes (optional)
- The proof uses `suminf` and power series expansions, which may require corresponding libraries or definitions in other proof assistants.
- Tactics such as `ASM_SIMP_TAC` rely heavily on the simplifier which may have to be re-implemented using appropriate simplification rules or decision procedures in other proof assistants.
- The `AC REAL_MUL_AC` tactic utilizes associativity and commutativity of real multiplication, this may need to be re-implemented using equational reasoning.


---

## TAN_POWSER

### Name of formal statement
TAN_POWSER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAN_POWSER = prove
 (`!x. abs(x) < pi / &2
       ==> (\n. (if EVEN n then &0 else
                 &2 * (&2 pow (n + 1) - &1) *
                 suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1)) *
                x pow n)
           sums (tan x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 < abs(x)` THEN ASM_SIMP_TAC[TAN_POWSER_WEAK] THEN
  DISCH_THEN(K ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TAN_0] THEN
  W(fun (asl,w) -> MP_TAC(SPECL [lhand w; `0`] SER_0)) THEN
  REWRITE_TAC[sum] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  UNDISCH_TAC `~(EVEN n)` THEN
  REWRITE_TAC[NOT_EVEN; ODD_EXISTS; real_pow; LEFT_IMP_EXISTS_THM] THEN
  SIMP_TAC[real_pow; REAL_MUL_LZERO; REAL_MUL_RZERO]);;
```
### Informal statement
For all real numbers `x`, if the absolute value of `x` is less than `pi / 2`, then the infinite series with terms given by the function that maps `n` to `(if n is even then 0 else 2 * (2^(n+1) - 1) * (sum of `inv ((m + 1)^(n + 1))` from `m = 0` to infinity) / (pi^(n + 1))) * (x^n)` sums to `tan x`.

### Informal sketch
The proof demonstrates that the Taylor series for `tan x` converges to `tan x` when `abs(x) < pi / 2`.

- First, the proof handles the case when `abs(x)` is not equal to zero. This is achieved with `ASM_CASES_TAC \`&0 < abs(x)\``. Then, `TAN_POWSER_WEAK` is used to establish the implication.
- The statement is then specialized with `lhand w` and `0` to handle the scenario when x is 0.
- After that, it introduces a natural number `n` via `X_GEN_TAC \`n:num\`` before distinguishing cases about it being even or odd with `ASM_CASES_TAC \`EVEN n\``, and the case when n is even is simplified with `REAL_MUL_LZERO`.
- Finally, `NOT_EVEN`, `ODD_EXISTS`, `real_pow` and `LEFT_IMP_EXISTS_THM` are rewritten on the goal, the proof concludes by simplifying with `real_pow`, `REAL_MUL_LZERO` and `REAL_MUL_RZERO`.

### Mathematical insight
This theorem provides the Taylor series expansion of the tangent function around zero. It expresses `tan x` as an infinite sum involving powers of `x` and coefficients that depend on whether the power is even or odd. The theorem also specifies the interval of convergence for this series, which is `abs(x) < pi / 2`. The coefficients of this series are closely related to the values of the Riemann zeta function at even positive integers.

### Dependencies
- `TAN_POWSER_WEAK`
- `REAL_ABS_NZ`
- `TAN_0`
- `SER_0`
- `sum`
- `NOT_EVEN`
- `ODD_EXISTS`
- `real_pow`
- `LEFT_IMP_EXISTS_THM`
- `REAL_MUL_LZERO`
- `REAL_MUL_RZERO`


---

## th

### Name of formal statement
th

### Type of the formal statement
theorem

### Formal Content
```ocaml
let th = prove
 (`(f diffl l)(x) ==>
    ((\x. poly p (f x)) diffl (l * poly (poly_diff p) (f x)))(x)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MP_TAC(SPECL [`\x. poly p x`; `f:real->real`;
                `poly (poly_diff p) (f(x:real))`;
                `l:real`; `x:real`] DIFF_CHAIN) THEN
  ASM_REWRITE_TAC[POLY_DIFF]) in
add_to_diff_net th;;
```
### Informal statement
If the function `f` is differentiable at `x` with derivative `l`, then the function `\x. poly p (f x)` is differentiable at `x` with derivative `l * poly (poly_diff p) (f x)`, where `poly p x` represents the polynomial `p` evaluated at `x`, and `poly_diff p` is the derivative of the polynomial `p`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the implication.
- Rewrite using the commutativity of real multiplication (`REAL_MUL_SYM`).
- Apply the chain rule for differentiation (`DIFF_CHAIN`), instantiating it for the specific functions involved: outer function `\x. poly p x`, inner function `f x`, derivative of the inner function `l`, and point `x`.
- Rewrite using the theorem `POLY_DIFF` which gives the derivative of a polynomial.
- These steps together discharge the theorem automatically.

### Mathematical insight
This theorem provides a differentiation rule for the composition of a polynomial function with another differentiable function. It's an instance of the chain rule, but specialized for when the outer function is a polynomial. It leverages the fact that polynomials are differentiable and their derivatives can be computed symbolically.

### Dependencies
- Theorems:
  - `REAL_MUL_SYM`
  - `DIFF_CHAIN`
  - `POLY_DIFF`


---

## DIFF_CHAIN_TAN

### Name of formal statement
DIFF_CHAIN_TAN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIFF_CHAIN_TAN = prove
 (`~(cos x = &0)
   ==> ((\x. poly p (tan x)) diffl
        (poly ([&1; &0; &1] ** poly_diff p) (tan x))) (x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tan] THEN
  W(MP_TAC o SPEC `x:real` o DIFF_CONV o lhand o rator o snd) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[POLY_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[poly; REAL_MUL_RID; REAL_MUL_RZERO; REAL_ADD_RID;
              REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_ARITH `a - --s * s = (s * s + a)`] THEN
  REWRITE_TAC[GSYM REAL_POW_2; SIN_CIRCLE] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW2_ABS] THEN
  ASM_SIMP_TAC[REAL_POW_LT; GSYM REAL_ABS_NZ; REAL_EQ_LDIV_EQ] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_POW_MUL] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN REWRITE_TAC[SIN_CIRCLE]);;
```

### Informal statement
Given that `cos x` is not equal to 0, then the derivative of the polynomial `p` evaluated at `tan x`, with respect to `x`, is equal to the evaluation at `x` of the polynomial `[1; 0; 1] ** poly_diff p` evaluated at `tan x`, where `poly_diff p` is the derivative of polynomial `p`.

### Informal sketch
The proof proceeds as follows:
- Start by stripping the implication.
- Rewrite `tan x` as `sin x / cos x`.
- Apply the differentiation rule (`DIFF_CONV`) to the left-hand side of the equation, substituting `x` with the given `x`.
- Simplify the resulting expression using assumptions.
- Apply theorems to manipulate the equation.
- Apply the derivative of the polynomial expansion.
- Simplify the expression by expanding the polynomial multiplication `POLY_MUL`.
- Further simplify by applying theorems and rewriting rules related to real arithmetic, such as identities for multiplication, addition, and powers (`REAL_MUL_RID`, `REAL_MUL_RZERO`, `REAL_ADD_RID`, `REAL_ADD_LID`).
- Use arithmetic identities for real numbers to rearrange terms (`REAL_ARITH`).
- Apply trigonometric identities, specifically `SIN_CIRCLE` (`sin x ^ 2 + cos x ^ 2 = 1`) and rewrite `REAL_POW_2`.
- Apply rewriting to handle absolute values and powers (`REAL_POW2_ABS`).
- Use lemmas concerning inequalities, absolute values and division (`REAL_POW_LT`, `REAL_ABS_NZ`, `REAL_EQ_LDIV_EQ`).
- Distribute and simplify using properties of real numbers, like distribution of multiplication over addition (`REAL_ADD_RDISTRIB`) and properties of powers (`REAL_POW_MUL`).
- More simplification lemmas are applied based on multiplicative and additive identities (`REAL_DIV_RMUL`, `REAL_MUL_LID`).
- Rearrange terms using commutativity of addition (`REAL_ADD_SYM`) and apply the `SIN_CIRCLE` identity again.

### Mathematical insight
This theorem establishes the chain rule for differentiating a polynomial evaluated at the tangent function. The condition `~(cos x = &0)` ensures that `tan x` is well-defined. The derivative of `poly p (tan x)` with respect to `x` is expressed in terms of the derivative of the polynomial `p` and the square of the secant function (represented by `[1; 0; 1]` which polynomial `1 + x^2`).

### Dependencies
- `tan`
- `DIFF_CONV`
- `POLY_MUL`
- `poly`
- `REAL_MUL_RID`
- `REAL_MUL_RZERO`
- `REAL_ADD_RID`
- `REAL_ADD_LID`
- `REAL_ARITH`
- `REAL_POW_2`
- `SIN_CIRCLE`
- `REAL_POW2_ABS`
- `REAL_POW_LT`
- `REAL_ABS_NZ`
- `REAL_EQ_LDIV_EQ`
- `REAL_ADD_RDISTRIB`
- `REAL_POW_MUL`
- `REAL_DIV_RMUL`
- `REAL_MUL_LID`
- `REAL_ADD_SYM`


---

## tanpoly

### Name of formal statement
- tanpoly

### Type of the formal statement
- new_recursive_definition

### Formal Content
- Placeholder: 
```ocaml
let tanpoly = new_recursive_definition num_RECURSION
  `(tanpoly 0 = [&0; &1]) /\
   (!n. tanpoly (SUC n) = [&1; &0; &1] ** poly_diff(tanpoly n))`;;
```

### Informal statement
- Define `tanpoly` recursively over the natural numbers such that:
  - `tanpoly 0` is equal to the polynomial `[&0; &1]`.
  - For all natural numbers `n`, `tanpoly (SUC n)` is equal to the polynomial `[&1; &0; &1]` convolved with the derivative of `tanpoly n`.

### Informal sketch
- This is a recursive definition of tangent polynomials.
- Base case: The tangent polynomial of 0, `tanpoly 0`, is defined to be `[&0; &1]` (representing the polynomial `x`).
- Recursive step: For any natural number `n`, `tanpoly (SUC n)` (that is `tanpoly (n+1)`) is defined as the convolution (polynomial multiplication) of the polynomial `[&1; &0; &1]` (representing `1 + x^2`) with the derivative of the polynomial `tanpoly n`.
- The recursion is registered with the HOL Light recursion package `num_RECURSION`, which automates proof of termination by showing that arguments decrease.

### Mathematical insight
- The tangent polynomials are a sequence of polynomials whose coefficients are related to tangent numbers. The definition computes `tanpoly (n+1)` based on `tanpoly n` and its derivative, capturing this relationship. The convolution with `[&1; &0; &1]` is a key part of forming the next tangent polynomial from the derivative of the previous one.

### Dependencies
- `num_RECURSION`
- `poly_diff`


---

## TANPOLYS_RULE

### Name of formal statement
TANPOLYS_RULE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TANPOLYS_RULE =
  let pth1,pth2 = CONJ_PAIR tanpoly in
  let base = [pth1]
  and rule = GEN_REWRITE_RULE LAND_CONV [GSYM pth2] in
  let poly_diff_tm = `poly_diff`
  and poly_mul_tm = `( ** ) [&1; &0; &1]` in
  let rec tanpolys n =
    if n < 0 then []
    else if n = 0 then base else
    let thl = tanpolys (n - 1) in
    let th1 = AP_TERM poly_diff_tm (hd thl) in
    let th2 = TRANS th1 (POLY_DIFF_CONV (rand(concl th1))) in
    let th3 = AP_TERM poly_mul_tm th2 in
    let th4 = TRANS th3 (POLY_MUL_CONV (rand(concl th3))) in
    let th5 = rule th4 in
    let th6 = CONV_RULE (LAND_CONV(RAND_CONV NUM_SUC_CONV)) th5 in
    th6::thl in
  rev o tanpolys;;
```

### Informal statement
The theorem `TANPOLYS_RULE` constructs a list of theorems. This list contains theorems proving that the Taylor coefficients of the `tan` function at 0 can be expressed as polynomials. The theorem uses a recursive function `tanpolys` to build the list. The base case for `n=0` uses a theorem extracted from `tanpoly`. For `n > 0`, it extends this list by:
1. Taking the head `thl` of the list obtained for `n-1`.
2. Applying the term `poly_diff` to the head `thl`.
3. Applying `POLY_DIFF_CONV` to the right-hand-side of the conclusion of the resulting theorem, to calculate the derivative of the polynomial.
4. Applying the term `( ** ) [&1; &0; &1]` (which represents polynomial multiplication by `x^2 + 1`) to the result.
5. Applying `POLY_MUL_CONV` to the right-hand-side of the conclusion of the resulting theorem, to compute the polynomial multiplication.
6. Applying a rewrite rule `rule` derived from `tanpoly` to simplify the expression.
7. Applying a conversion that simplifies a conjunction using `NUM_SUC_CONV`.
Finally, it reverses the list.

### Informal sketch
The theorem is proved by constructing a list of theorems, each proving that a certain term is equal to a polynomial. The construction is done recursively:

- First, define the base case for n=0 by using `tanpoly` to extract a suitable initial theorem.
- The rewrite rule `rule` is built using `tanpoly`, and will be used to rewrite expressions.
- For the inductive step:
    - Take the theorem corresponding to `n-1`.
    - Apply `poly_diff` to the polynomial on the right-hand side.
    - Apply `( ** ) [&1; &0; &1]` to the result. This corresponds to multiplication by `1 + x^2`.
    - Rewrite using `rule`.
    - Simplify using `NUM_SUC_CONV`.
- Finally, reverse the results to match the desired polynomial order.

### Mathematical insight
The theorem leverages the fact that the Taylor series coefficients of `tan(x)` satisfy a recurrence relation that can be expressed in terms of polynomial differentiation and multiplication. The theorem proves these polynomial identities formally. This result is useful for formalizing facts about special functions.

### Dependencies
- Constant: `tanpoly`
- Theorem: `POLY_DIFF_CONV`, `POLY_MUL_CONV`, `NUM_SUC_CONV`
- Conversion: `LAND_CONV`, `RAND_CONV`


---

## TANPOLY_CONV

### Name of formal statement
TANPOLY_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let TANPOLY_CONV =
  let tanpoly_tm = `tanpoly` in
  fun tm ->
    let l,r = dest_comb tm in
    if l <> tanpoly_tm then failwith "TANPOLY_CONV"
    else last(TANPOLYS_RULE(dest_small_numeral r));;
```

### Informal statement
The conversion `TANPOLY_CONV` takes a term `tm` as input.
If `tm` is not of the form `tanpoly n`, where `n` is a small numeral, then the conversion fails.
Otherwise, it applies `TANPOLYS_RULE` to the small numeral `n` and returns the last element of the resulting list.

### Informal sketch
- Check if the input term `tm` is an application of the term `tanpoly` to a small numeral `n`.
- If it is, extract the numeral `n`.
- Apply the tactic `TANPOLYS_RULE` to `n`. `TANPOLYS_RULE` probably generates a list of rewrites.
- Return the right-hand side of the last rewrite rule generates by `TANPOLYS_RULE`.

### Mathematical insight
This conversion likely expands a tangent polynomial `tanpoly n` by applying `TANPOLYS_RULE` to the numeral `n`, generating a list of rewrite rules (presumably corresponding to the expansion steps). The last rule in the list represents the fully expanded form of the tangent polynomial, which is then returned.

### Dependencies
- Term: `tanpoly`
- Function: `dest_comb`
- Function: `dest_small_numeral`
- Conversion: `TANPOLYS_RULE`
- Function: `last`


---

## tannumber

### Name of formal statement
- tannumber

### Type of the formal statement
- new_definition

### Formal Content
- The full HOL Light statement will be inserted here **after generation**.
```ocaml
let tannumber = new_definition
  `tannumber n = poly (tanpoly n) (&0)`;;
```

### Informal statement
- The tangent number `tannumber n` is defined to be the value of the polynomial `tanpoly n` evaluated at 0, where `tanpoly n` is a polynomial.

### Informal sketch
- The definition introduces the term `tannumber n` as the evaluation of the polynomial `tanpoly n` at the real number zero.
- The definition relies on prior definitions of `poly` (polynomial evaluation) and `tanpoly` (tangent polynomial).
- There is no proof involved, as it is a direct definition.

### Mathematical insight
- The definition of `tannumber` connects tangent polynomials with tangent numbers, which are coefficients in the Taylor series expansion of the tangent function.
- Evaluating the tangent polynomial at 0 extracts the constant term of `tanpoly n`, which, by the definition of `tanpoly`, is related to the nth tangent number.

### Dependencies
- Definitions: `poly`, `tanpoly`

### Porting notes (optional)
- Porting this definition requires having appropriate definitions of polynomial evaluation and tangent polynomials in the target proof assistant. The polynomial evaluation function (`poly` in HOL Light) should allow for evaluation of polynomials at real number values.


---

## TANNUMBERS_RULE,TANNUMBER_CONV

### Name of formal statement
TANNUMBERS_RULE,TANNUMBER_CONV

### Type of the formal statement
Theorem (derived rule and conversion)

### Formal Content
```ocaml
let TANNUMBERS_RULE,TANNUMBER_CONV =
  let POLY_0_THM = prove
   (`(poly [] (&0) = &0) /\
     (poly (CONS h t) (&0) = h)`,
    REWRITE_TAC[poly; REAL_MUL_LZERO; REAL_ADD_RID]) in
  let poly_tm = `poly`
  and zero_tm = `&0`
  and tannumber_tm = `tannumber`
  and depoly_conv = GEN_REWRITE_CONV I [POLY_0_THM]
  and tannumber_rule = GEN_REWRITE_RULE LAND_CONV [GSYM tannumber] in
  let process th =
    let th1 = AP_THM (AP_TERM poly_tm th) zero_tm in
    let th2 = TRANS th1 (depoly_conv (rand(concl th1))) in
    let th3 = tannumber_rule th2 in
    th3 in
  let TANNUMBERS_RULE = map process o TANPOLYS_RULE
  and TANNUMBER_CONV tm =
    let l,r = dest_comb tm in
    if l <> tannumber_tm then failwith "TANNUMBER_CONV" else
    process(last(TANPOLYS_RULE(dest_small_numeral r))) in
  TANNUMBERS_RULE,TANNUMBER_CONV;;
```
### Informal statement
Let `POLY_0_THM` be the theorem that states that for any list of real numbers `l` and real number `x`, if `x = 0`, then `poly l x = 0` if and only if the list `l` is empty and `poly` of a nonempty list `CONS h t` evaluates to `h`. Let `poly_tm` be the term `poly`, `zero_tm` be the term `&0`, and `tannumber_tm` be the term `tannumber`. Let `depoly_conv` be a conversion that generally rewrites with the theorem `POLY_0_THM`. Let `tannumber_rule` be a rule that generally rewrites using the symmetric version of the theorem `tannumber`.

Define a function `process` that takes a theorem `th` as input:
1. Apply the term `poly_tm` to the theorem `th`, then apply this to `zero_tm`, resulting in theorem `th1`.
2. Transform `th1` by rewriting the right-hand side of its conclusion using the conversion `depoly_conv`, yielding theorem `th2`.
3. Transform `th2` using `tannumber_rule` to get `th3`. The function returns `th3`.
`TANNUMBERS_RULE` is defined as the result of mapping the `process` function over the result of `TANPOLYS_RULE`.

`TANNUMBER_CONV` is defined as a conversion that takes a term `tm` as input:
1. Deconstruct the term `tm` into function part `l` and argument part `r`.
2. If `l` is not equal to `tannumber_tm`, then fail.
3. Otherwise, apply `process` to the last element of the result from `TANPOLYS_RULE(dest_small_numeral r)`.

Return `TANNUMBERS_RULE` and `TANNUMBER_CONV`.

### Informal sketch
- `POLY_0_THM` simplifies the polynomial evaluation at zero.
- The `process` function takes a theorem about a polynomial, evaluates the polynomial at zero, simplifies using `POLY_0_THM`, and then applies `tannumber_rule`.
- `TANNUMBERS_RULE` applies `process` to each theorem obtained by applying `TANPOLYS_RULE`.

- `TANNUMBER_CONV` takes a term `tannumber r`, preprocesses `r` with `TANPOLYS_RULE`, and applies the `process` function to the last theorem resulting from `TANPOLYS_RULE`. `dest_small_numeral` converts `r` into primitive natural number.

### Mathematical insight
These definitions aim to manipulate theorems related to polynomials within the context of `tannumber`, likely to simplify or transform expressions involving trigonometric tangent functions.

### Dependencies
- `poly`
- `TANPOLYS_RULE`
- `tannumber`
- `dest_small_numeral`

### Porting notes (optional)
The main challenge is porting relevant rewriting tactics that automatically apply needed simplification steps.
Rewriting tactics might have different calling conventions.
Ensure that the dependencies exist in the target system, especially `TANPOLYS_RULE` since the process uses `last`, potentially needing additional proof if the output of `TANPOLYS_RULE` can be empty.


---

## DIFF_CHAIN_TAN_TANPOLYS

### Name of formal statement
DIFF_CHAIN_TAN_TANPOLYS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DIFF_CHAIN_TAN_TANPOLYS = prove
 (`~(cos x = &0)
   ==> ((\x. poly (tanpoly n) (tan x)) diffl
        (poly (tanpoly(SUC n)) (tan x))) (x)`,
  REWRITE_TAC[tanpoly; DIFF_CHAIN_TAN]);;
```
### Informal statement
For all real numbers `x`, if `cos x` is not equal to 0, then the derivative with respect to `x` of the function that maps `x` to the polynomial evaluated at `tan x` (where the polynomial's coefficients are given by `tanpoly n`) is equal to the polynomial evaluated at `tan x` (where the polynomial's coefficients are given by `tanpoly(SUC n)`).

### Informal sketch
- The theorem establishes a chain rule for differentiating a composite function involving polynomial `poly` and tangent function `tan`.
- It uses `tanpoly n` to denote a polynomial of degree `n` related to the tangent function.
- The proof relies on rewriting using the definition of `tanpoly` and applying the general `DIFF_CHAIN_TAN` rule.
- The premise `~(cos x = &0)` ensures that `tan x` is well-defined.

### Mathematical insight
This theorem provides a specific chain rule tailored to functions constructed from tangent polynomials. It formalizes the relationship between the derivative of the composite function `poly (tanpoly n) (tan x)` and another related polynomial `poly (tanpoly(SUC n)) (tan x)`. This type of result is useful for symbolic differentiation within a formal system, especially when dealing with trigonometric functions.

### Dependencies
- Definitions: `tanpoly`
- Theorems: `DIFF_CHAIN_TAN`


---

## th

### Name of formal statement
th

### Type of the formal statement
theorem

### Formal Content
```ocaml
let th = prove
 (`(f diffl l)(x) /\ ~(cos(f x) = &0)
   ==> ((\x. poly (tanpoly n) (tan(f x))) diffl
        (l * poly (tanpoly(SUC n)) (tan(f x))))(x)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MP_TAC(SPECL [`\x. poly (tanpoly n) (tan x)`; `f:real->real`;
                `poly (tanpoly(SUC n)) (tan(f(x:real)))`;
                `l:real`; `x:real`] DIFF_CHAIN) THEN
  ASM_SIMP_TAC[DIFF_CHAIN_TAN_TANPOLYS]) in
add_to_diff_net th;;
```
### Informal statement
For any real-valued function `f`, real number `l`, natural number `n`, and real number `x`, if `f` is differentiable at `x` with derivative `l`, and `cos(f x)` is not equal to 0, then the function `\x. poly (tanpoly n) (tan(f x))` is differentiable at `x` with derivative `l * poly (tanpoly(SUC n)) (tan(f x))`.

### Informal sketch
The proof proceeds as follows:
- Strip the goal, introducing the assumptions into the assumptions list.
- Rewrite using the commutativity of real multiplication (`REAL_MUL_SYM`).
- Apply the chain rule (`DIFF_CHAIN`) with appropriate specializations to the terms including `\x. poly (tanpoly n) (tan x)`, `f`, `poly (tanpoly(SUC n)) (tan(f(x)))`, `l`, and `x`.
- Simplify using the theorem `DIFF_CHAIN_TAN_TANPOLYS` and assumptions in the assumption list.

### Mathematical insight
This theorem establishes the differentiability of a composite function involving the tangent function and tangent polynomials. It's a specific instance of the chain rule applied to a composition of `f`, `tan`, and `poly (tanpoly n)`. The condition `~(cos(f x) = &0)` ensures that `tan(f x)` is defined.

### Dependencies
- `DIFF_CHAIN`
- `REAL_MUL_SYM`
- `DIFF_CHAIN_TAN_TANPOLYS`


---

## TERMDIFF_ALT

### Name of formal statement
TERMDIFF_ALT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TERMDIFF_ALT = prove
 (`!f f' c k.
        (!x. abs(x) < k ==> (\n. c(n) * x pow n) sums f(x))
        ==> (!x. abs(x) < k ==> (f diffl f'(x))(x))
            ==> (!x. abs(x) < k ==> (\n. (diffs c)(n) * x pow n) sums f'(x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `summable (\n. diffs c n * x pow n) /\
    (f'(x) = suminf (\n. diffs c n * x pow n))`
  MP_TAC THENL
   [ALL_TAC; SIMP_TAC[SUMMABLE_SUM]] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `abs(x) < k` THEN SPEC_TAC(`x:real`,`x:real`) THEN
    MATCH_MP_TAC TERMDIFF_CONVERGES THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[summable] THEN
    EXISTS_TAC `(f:real->real) x` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC DIFF_LCONST THEN
  EXISTS_TAC `\x. f x - suminf (\n. c(n) * x pow n)` THEN
  EXISTS_TAC `x:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIFF_SUB THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC TERMDIFF_STRONG THEN
    EXISTS_TAC `(abs(x) + k) / &2` THEN CONJ_TAC THENL
     [REWRITE_TAC[summable] THEN
      EXISTS_TAC `(f:real->real)((abs(x) + k) / &2)` THEN
      FIRST_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LT_LDIV_EQ;
             REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `abs(x) < k` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `k - abs(x)` THEN ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `(a = b) /\ (c = d) ==> (a - b = c - d)`) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_UNIQ THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `abs(x - y) < k - abs(x)` THEN REAL_ARITH_TAC);;
```

### Informal statement
If for all x such that the absolute value of x is less than k, the series defined by the function that maps n to `c(n) * x pow n` sums to `f(x)`, and for all x such that the absolute value of x is less than k, `f` is differentiable at x with derivative `f'(x)`, then for all x such that the absolute value of x is less than k, the series defined by the function that maps n to `(diffs c)(n) * x pow n` sums to `f'(x)`.

### Informal sketch
The proof proceeds as follows:
- First, we set a subgoal to prove that the power series `\n. diffs c n * x pow n` is summable and that its sum is equal to `f'(x)`.
- The goal is then split into two parts: proving the summability and then proving the equality of the sum with `f'(x)`. The `SUMMABLE_SUM` theorem is used.
- To show summability, we use `TERMDIFF_CONVERGES` after instantiating it with `x`.
- It is shown that the derivative of the series is equal to the term-by-term derivatives. To show the equality of `f'(x)` with the sum of `\n. diffs c n * x pow n`, we exploit the uniqueness of the limit of the sum. This requires showing that the series `\n. c(n) * x pow n` is differentiable and then using `TERMDIFF_STRONG` with an argument slightly larger than `abs(x)` but still less than `k`.

### Mathematical insight
This theorem provides conditions under which we can differentiate a power series term by term. It is a crucial result in real analysis and is used extensively in applications involving power series expansions. The summability condition ensures that the term-by-term differentiation is valid within the radius of convergence.

### Dependencies
- `TERMDIFF_CONVERGES`
- `SUMMABLE_SUM`
- `GSYM REAL_SUB_0`
- `DIFF_LCONST`
- `DIFF_SUB`
- `TERMDIFF_STRONG`
- `REAL_ABS_DIV`
- `REAL_ABS_NUM`
- `REAL_LT_LDIV_EQ`
- `REAL_LT_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `REAL_SUB_LT`
- `SUM_UNIQ`

Definitions:
- `summable`

### Porting notes (optional)
- The definitions of `sums` and `diffl` will need to be carefully examined to ensure that they are compatible with the target proof assistant's real analysis libraries.
- The tactic `REAL_ARITH_TAC` is a powerful automation tactic specific to HOL Light that may need significant adaptation.


---

## TAN_DERIV_POWSER

### Name of formal statement
TAN_DERIV_POWSER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAN_DERIV_POWSER = prove
 (`!n x. abs(x) < pi / &2
         ==> (\m. ITER n diffs
                   (\i. if EVEN i
                        then &0
                        else &2 *
                             (&2 pow (i + 1) - &1) *
                             suminf (\m. inv (&(m + 1) pow (i + 1))) /
                             pi pow (i + 1)) m *
                  x pow m)
             sums (poly (tanpoly n) (tan x))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ITER; tanpoly; poly] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RZERO; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[TAN_POWSER]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TERMDIFF_ALT) THEN
  REWRITE_TAC[ITER] THEN CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC DIFF_CHAIN_TAN_TANPOLYS THEN
  REWRITE_TAC[COS_ZERO] THEN
  UNDISCH_TAC `abs x < pi / &2` THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[OR_EXISTS_THM; NOT_EVEN] THEN
  REWRITE_TAC[TAUT `a /\ b \/ a /\ c <=> a /\ (b \/ c)`] THEN
  DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`)) THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_DIV; REAL_LT_IMP_LE; PI_POS; REAL_POS] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_ARITH `x = &1 * x`] THEN
  SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
  ARITH_TAC);;
```

### Informal statement
For all natural numbers `n` and real numbers `x`, if the absolute value of `x` is less than `pi / 2`, then the `n`-th derivative of the function that maps `x` to the Taylor polynomial of degree `n` of the tangent function `tan x` evaluated at `x`, is equal to the summation from `m = 0` to infinity of the term: the `n`-fold iteration of the `diffs` operator applied to the function that maps `i` to `0` if `i` is even, and `2 * (2^(i+1) - 1) * suminf (\m. inv (&(m + 1) pow (i + 1))) / (pi pow (i + 1))` otherwise applied to `m`, multiplied by `x pow m`.

### Informal sketch
The theorem states an equality between the `n`-th derivative of the Taylor polynomial of degree `n` of the tangent function, `poly (tanpoly n) (tan x)`, and an infinite summation involving the derivatives of a series representation. The proof proceeds by induction on `n`.

- **Base Case:** Prove the statement for `n = 0`. This involves rewriting the statement using definitions `ITER`, `tanpoly`, `poly`, `REAL_ADD_LID`, `REAL_ADD_RID`, `REAL_MUL_RZERO`, `REAL_MUL_RID`, and applying `TAN_POWSER`.
- **Inductive Step:** Assuming the statement holds for `n`, prove it for `n + 1`.
    - Apply `TERMDIFF_ALT` to express the derivative of the summation.
    - Rewrite using `ITER`.
    - Convert to eta-normal form using `ETA_CONV`.
    - Discharge the assumption from the goal.
    - Introduce the real variable `x`.
    - Apply the chain rule for differentiation using `DIFF_CHAIN_TAN_TANPOLYS`.
    - Simplify using `COS_ZERO`.
    - Discharge the assumption `abs x < pi / &2`.
    - Apply contraposition and De Morgan's laws to rewrite the goal.
    - Simplify using `OR_EXISTS_THM`, `NOT_EVEN`, and a tautology.
    - Eliminate an existential quantifier via choice and decompose a conjunction.
    - Use an arithmetic fact `(x = a) \/ (x = --a) ==> &0 <= a ==> (abs(x) = a)`.
    - Simplify using real number inequalities (`REAL_LE_MUL`, `REAL_LE_DIV`, `REAL_LT_IMP_LE`, `PI_POS`, `REAL_POS`).
    - Eliminate an existential quantifier using `ODD_EXISTS` and substitution.
    - Simplify the goal.
    - Simplify again using real number inequalities and arithmetic facts.

### Mathematical insight
This theorem provides a formula for computing the derivatives of the Taylor polynomial of the tangent function. It connects the Taylor polynomial to an infinite series representation involving the derivatives of a specific function. The inequality `abs(x) < pi / 2` ensures that `x` lies within the interval of convergence of the Taylor series for the tangent function. This is important for relating the Taylor polynomial to actual derivatives of the tangent function.

### Dependencies
- `ITER`
- `tanpoly`
- `poly`
- `REAL_ADD_LID`
- `REAL_ADD_RID`
- `REAL_MUL_RZERO`
- `REAL_MUL_RID`
- `TAN_POWSER`
- `TERMDIFF_ALT`
- `DIFF_CHAIN_TAN_TANPOLYS`
- `COS_ZERO`
- `DE_MORGAN_THM`
- `OR_EXISTS_THM`
- `NOT_EVEN`
- `REAL_ARITH`
- `REAL_LE_MUL`
- `REAL_LE_DIV`
- `REAL_LT_IMP_LE`
- `PI_POS`
- `REAL_POS`
- `ODD_EXISTS`
- `REAL_LT_RMUL_EQ`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`

### Porting notes (optional)
- The proof relies heavily on rewriting and arithmetic simplification. Other proof assistants may require more manual guidance in these steps.
- The handling of real analysis concepts (differentiation, Taylor series) might differ between proof assistants. Ensure that the corresponding theorems and definitions are available.
- The tactic `ARITH_TAC` is HOL Light-specific. Other proof assistants will have different methods for discharging arithmetic goals.


---

## ITER_DIFFS_LEMMA

### Name of formal statement
ITER_DIFFS_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ITER_DIFFS_LEMMA = prove
 (`!n c. ITER n diffs c 0 = &(FACT n) * c(n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER_ALT; diffs; FACT; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_AC]);;
```
### Informal statement
For all natural numbers `n` and all functions `c` from natural numbers to real numbers, `ITER n diffs c 0` is equal to `&(FACT n) * c(n)`.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case: When `n = 0`, `ITER 0 diffs c 0` is equal to `c(0)`, and `&(FACT 0) * c(0)` is equal to `1 * c(0)`, which simplifies to `c(0)`.
- Inductive step: Assume that `ITER n diffs c 0 = &(FACT n) * c(n)` holds. We need to show that `ITER (SUC n) diffs c 0 = &(FACT (SUC n)) * c(SUC n)`.

  The left-hand side `ITER (SUC n) diffs c 0` can be rewritten using `ITER_ALT` and the definition of `diffs` as `&(SUC n) * ITER n diffs c 0`. By the inductive hypothesis, this is equal to `&(SUC n) * (&(FACT n) * c(n))`.

  The right-hand side `&(FACT (SUC n)) * c(SUC n)` can be rewritten as `&((SUC n) * FACT n) * c(SUC n)`, which is equal to `(&(SUC n) * &(FACT n)) * c(SUC n)` using `REAL_OF_NUM_MUL`. Rearranging this expression uses `REAL_MUL_AC` and concludes the proof.

### Mathematical insight
This theorem provides a closed-form expression for the `n`-th iteration of the `diffs` function applied to a function `c` at 0. The `diffs` function computes `(n+1) * f(n)` on input `n`, and this lemma connects this to the factorial function.

### Dependencies
- `ITER_ALT`
- `diffs`
- `FACT`
- `REAL_MUL_LID`
- `REAL_OF_NUM_MUL`
- `REAL_MUL_AC`


---

## TANNUMBER_HARMONICSUMS

### Name of formal statement
TANNUMBER_HARMONICSUMS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TANNUMBER_HARMONICSUMS = prove
 (`!n. ODD n
       ==> (&2 * (&2 pow (n + 1) - &1) * &(FACT n) *
            suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1) =
            tannumber n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `&0`] TAN_DERIV_POWSER) THEN
  SIMP_TAC[REAL_ABS_NUM; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; PI_POS] THEN
  REWRITE_TAC[TAN_0; GSYM tannumber] THEN
  MP_TAC(SPECL
   [`\m. ITER n diffs
      (\i. if EVEN i
           then &0
           else &2 *
                (&2 pow (i + 1) - &1) *
                suminf (\m. inv (&(m + 1) pow (i + 1))) / pi pow (i + 1))
      m *
      &0 pow m`;
    `1`] SER_0) THEN
  REWRITE_TAC[SUM_1] THEN
  SIMP_TAC[snd(EQ_IMP_RULE(SPEC_ALL REAL_POW_EQ_0));
           ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  REWRITE_TAC[REAL_MUL_RZERO; real_pow] THEN
  ONCE_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_UNIQ) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ITER_DIFFS_LEMMA; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[GSYM NOT_ODD] THEN REWRITE_TAC[REAL_MUL_AC]);;
```
### Informal statement
For all natural numbers `n`, `n` is odd if and only if the following equality holds: `&2 * (&2 pow (n + 1) - &1) * &(FACT n) * suminf (\m. inv (&(m + 1) pow (n + 1))) / pi pow (n + 1) = tannumber n`, where `tannumber n` represents the `n`-th tangent number.

### Informal sketch
The proof proceeds by induction and simplifies the equality using properties of tangent numbers, infinite sums, and real number arithmetic.

- The proof starts by stripping the goal and applying `TAN_DERIV_POWSER` with specialized instances for `n` and `&0`.
- Then, it simplifies using real number arithmetic facts related to absolute values, division, inequalities, and the positivity of `pi`. Specific theorems used are `REAL_ABS_NUM`, `REAL_LT_DIV`, `REAL_OF_NUM_LT`, `ARITH`, and `PI_POS`.
- It rewrites using `TAN_0` and the symmetric form of `tannumber`.
- It applies `SER_0` with specific inputs to eliminate some terms of power series.
- It rewrites using `SUM_1`, then simplifies with `REAL_POW_EQ_0` and an arithmetic rule that states `1 <= n ==> ~(n = 0)`.
- Next, it rewrites using `REAL_MUL_RZERO` and `real_pow`.
- It rewrites once using `IMP_IMP` and then applies `SER_UNIQ` after discharging and substituting.
- It rewrites using `ITER_DIFFS_LEMMA` and `REAL_MUL_RID`.
- Finally, it rewrites using `NOT_ODD` and then rearranges the multiplication using `REAL_MUL_AC`.

### Mathematical insight
This theorem establishes a direct relationship between tangent numbers (`tannumber n`) and an infinite sum involving powers of natural numbers divided by powers of pi, specifically when `n` is an odd number. This result connects special numbers (tangent numbers) to values of the Riemann zeta function at odd integers. The `tannumber` is related to the Maclaurin series expansion of the tangent function.

### Dependencies
- `TAN_DERIV_POWSER`
- `REAL_ABS_NUM`
- `REAL_LT_DIV`
- `REAL_OF_NUM_LT`
- `ARITH`
- `PI_POS`
- `TAN_0`
- `tannumber`
- `SER_0`
- `SUM_1`
- `REAL_POW_EQ_0`
- `real_pow`
- `SER_UNIQ`
- `ITER_DIFFS_LEMMA`
- `REAL_MUL_RID`
- `NOT_ODD`
- `REAL_MUL_AC`


---

## HARMONICSUMS_TANNUMBER

### Name of formal statement
HARMONICSUMS_TANNUMBER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HARMONICSUMS_TANNUMBER = prove
 (`!n. EVEN n /\ ~(n = 0)
       ==> (suminf (\m. inv (&(m + 1) pow n)) / pi pow n =
            tannumber(n - 1) / (&2 * &(FACT(n - 1)) * (&2 pow n - &1)))`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; EVEN; NOT_EVEN] THEN
  REWRITE_TAC[SUC_SUB1] THEN SIMP_TAC[GSYM TANNUMBER_HARMONICSUMS] THEN
  REWRITE_TAC[ADD1] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = (a * c * b) * d`] THEN
  REWRITE_TAC[real_div] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b * c) * d = a * (b * c) * d`] THEN
  REWRITE_TAC[GSYM real_div] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC REAL_DIV_LMUL THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; FACT_LT] THEN
  REWRITE_TAC[REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_POW2_CLAUSES; ADD_EQ_0; ARITH_EQ]);;
```

### Informal statement
For all natural numbers `n`, if `n` is even and `n` is not equal to `0`, then the infinite sum of `1 / (m + 1)^n` (where `m` ranges from `0` to infinity) divided by `pi^n` is equal to `tannumber(n - 1)` divided by `(2 * (n - 1)! * (2^n - 1))`.

### Informal sketch
The proof proceeds by induction on `n`.

- The base case is handled by rewriting with `NOT_SUC`, `EVEN`, `NOT_EVEN`, `SUC_SUB1`, `TANNUMBER_HARMONICSUMS`, `ADD1`. Then some algebraic simplifications and rewriting with `real_div` is needed. After discharging the assumption, rewrite with `real_div` again.
- The proof uses the following steps to show the inductive step: `REAL_DIV_LMUL`, `REAL_LT_IMP_NZ`, `REAL_LT_MUL`, `REAL_OF_NUM_LT`, `FACT_LT`, `REAL_SUB_LT`, `REAL_POW2_CLAUSES`, `ADD_EQ_0`, and `ARITH_EQ`.

### Mathematical insight
This theorem relates the infinite sum of reciprocals of powers of natural numbers (specifically, `suminf (\m. inv (&(m + 1) pow n))`) for even powers `n` to the `tannumber` function, which is related to tangent numbers.

### Dependencies
- `EVEN`
- `NOT_SUC`
- `NOT_EVEN`
- `SUC_SUB1`
- `TANNUMBER_HARMONICSUMS`
- `ADD1`
- `REAL_DIV_LMUL`
- `REAL_LT_IMP_NZ`
- `REAL_LT_MUL`
- `REAL_OF_NUM_LT`
- `FACT_LT`
- `REAL_SUB_LT`
- `REAL_POW2_CLAUSES`
- `ADD_EQ_0`
- `ARITH_EQ`
- `FACT`
- `real_div`
- `REAL_MUL_AC`
- `REAL_POW2_CLAUSES`


---

## ODD_POLY_DIFF

### Name of formal statement
ODD_POLY_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ODD_POLY_DIFF = prove
 (`(!x. poly p (--x) = poly p x)
   ==> (!x. poly (poly_diff p) (--x) = --(poly(poly_diff p) x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC `\x. poly p (--x)` THEN EXISTS_TAC `--x` THEN CONJ_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o HALF_MK_ABS o GSYM) THEN
    REWRITE_TAC[CONV_RULE(ONCE_DEPTH_CONV ETA_CONV) POLY_DIFF];
    MP_TAC(SPECL [`\x. poly p x`; `\x. --x`; `poly (poly_diff p) x`;
                  `--(&1)`; `--x`]
           DIFF_CHAIN) THEN
    REWRITE_TAC[POLY_DIFF; REAL_MUL_RNEG; REAL_MUL_RID; REAL_NEG_NEG] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    W(MP_TAC o SPEC `--x` o DIFF_CONV o lhand o rator o snd) THEN
    REWRITE_TAC[]]);;
```

### Informal statement
If for all x, `p(-x) = p(x)` (i.e., `p` is an even polynomial), then for all x, `(poly_diff p)(-x) = -(poly_diff p)(x)` (i.e., the derivative of `p` is an odd polynomial).

### Informal sketch
The proof proceeds by the following steps:
- Assume `poly p (--x) = poly p x` for all `x`.
- Show that `poly (poly_diff p) (--x) = --(poly(poly_diff p) x)` for all `x`.
- Specialize the assumption and perform substitutions to rewrite the goal in terms of the assumption.
- The proof uses `DIFF_UNIQ` to deal with differentiation of unique polynomials.
- Apply `DIFF_CHAIN` and `POLY_DIFF` to simplify the expression.
- Use properties of real numbers to complete the proof.

### Mathematical insight
The theorem states that the derivative of an even polynomial is an odd polynomial. This is a standard result in calculus, and this theorem formalizes the result within HOL Light. The even polynomial property `p(-x) = p(x)` signifies symmetry around the y-axis, and its derivative being odd means it satisfies `f(-x) = -f(x)`, a symmetry about the origin, as expected.

### Dependencies
- Theorems:
  - `DIFF_UNIQ`
  - `DIFF_CHAIN`
  - `DIFF_CONV`
- Definitions:
  - `POLY_DIFF`
- Other:
  - `REAL_MUL_RNEG`
  - `REAL_MUL_RID`
  - `REAL_NEG_NEG`
  - `lhand`
  - `rator`
  - `snd`


---

## EVEN_POLY_DIFF

### Name of formal statement
EVEN_POLY_DIFF

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EVEN_POLY_DIFF = prove
 (`(!x. poly p (--x) = --(poly p x))
   ==> (!x. poly (poly_diff p) (--x) = poly(poly_diff p) x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC `\x. poly p x` THEN EXISTS_TAC `--x` THEN
  REWRITE_TAC[POLY_DIFF] THEN
  FIRST_ASSUM(MP_TAC o
    ONCE_REWRITE_RULE[REAL_ARITH `(a = --b) <=> (--a = b)`]) THEN
  DISCH_THEN(SUBST1_TAC o HALF_MK_ABS o GSYM) THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_NEG_NEG] THEN
  MATCH_MP_TAC DIFF_NEG THEN
  MP_TAC(SPECL [`\x. poly p x`; `\x. --x`; `poly (poly_diff p) x`;
                  `--(&1)`; `--x`]
           DIFF_CHAIN) THEN
  REWRITE_TAC[POLY_DIFF; REAL_MUL_RNEG; REAL_MUL_RID; REAL_NEG_NEG] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  W(MP_TAC o SPEC `--x` o DIFF_CONV o lhand o rator o snd) THEN
  REWRITE_TAC[]);;
```

### Informal statement
If for all `x`, `poly p (--x)` equals `-- (poly p x)`, then for all `x`, `poly (poly_diff p) (--x)` equals `poly (poly_diff p) x`.

### Informal sketch
The proof proceeds as follows:
- Assume `poly p (--x) = -- (poly p x)` for all `x`.
- We aim to show `poly (poly_diff p) (--x) = poly (poly_diff p) x` for all `x`.
- Apply `DIFF_UNIQ`, which probably states uniqueness of differentiation.
- Existentially quantify intermediate terms using `EXISTS_TAC` to introduce a `poly p x` for `x` and `--x`.
- Rewrite with `POLY_DIFF` to expand the polynomial derivative.
- Use the assumption `poly p (--x) = -- (poly p x)` allowing substitutions.
- Use real arithmetic to rewrite `a = --b` to `--a = b`.
- Use the rule to commute the abstraction.
- Simplify using the properties of real negation (`REAL_NEG_NEG`) i.e., `--(--a) = --a`.
- Apply `DIFF_NEG` that probably states the derivative of a negative function.
- Chain rule application using `DIFF_CHAIN`.
- Simplify using `POLY_DIFF`, `REAL_MUL_RNEG`, `REAL_MUL_RID`, and `REAL_NEG_NEG`.
- Differentiate some constants using `DIFF_CONV`.
- Simplify by rewriting.

### Mathematical insight
The theorem `EVEN_POLY_DIFF` establishes that if a polynomial `p` satisfies `p(-x) = -p(x)` for all `x` (i.e., `p` is an odd polynomial), then the derivative of `p`, denoted by `poly_diff p`, will be an even polynomial and satisfy `poly (poly_diff p) (--x) = poly (poly_diff p) x` for all `x`.

### Dependencies
- Theorems: `DIFF_UNIQ`, `DIFF_CHAIN`, `DIFF_NEG`, `DIFF_CONV`
- Definitions: `POLY_DIFF`
- Real arithmetic: `REAL_ARITH`, `REAL_NEG_NEG`, `REAL_MUL_RNEG`, `REAL_MUL_RID`

### Porting notes (optional)
- The proof makes heavy use of rewriting and simplification tactics. When porting, ensure the target proof assistant has similarly powerful automation for these tasks, especially for real arithmetic and polynomial simplification.
- The tactic `DIFF_UNIQ` is likely a wrapper over theorems establishing uniqueness of differentiation in HOL Light. A similar theorem is needed in other provers.
- Special care might be required with the tactic `HALF_MK_ABS o GSYM`.


---

## TANPOLY_ODD_EVEN

### Name of formal statement
TANPOLY_ODD_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TANPOLY_ODD_EVEN = prove
 (`!n x. (poly (tanpoly n) (--x) =
          if EVEN n then --(poly (tanpoly n) x) else poly (tanpoly n) x)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[EVEN; tanpoly] THEN
    CONV_TAC(ONCE_DEPTH_CONV POLY_DIFF_CONV) THEN
    REWRITE_TAC[poly] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[EVEN] THEN
  ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[tanpoly; POLY_MUL; ODD_POLY_DIFF; EVEN_POLY_DIFF] THEN
  REWRITE_TAC[REAL_MUL_RNEG] THEN TRY AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[poly] THEN REAL_ARITH_TAC);;
```
### Informal statement
For any natural number `n` and any real number `x`, the polynomial `poly (tanpoly n)` evaluated at `-x` equals `- (poly (tanpoly n) x)` if `n` is even, and equals `poly (tanpoly n) x` otherwise.

### Informal sketch
The proof proceeds by induction on `n`.

- Base case (`n = 0`): Reduce using the definitions of `EVEN` and `tanpoly`; simplify the resulting polynomial using `POLY_DIFF_CONV` and `poly`; and then use real arithmetic.
- Inductive step:
  - Assume the theorem holds for `n`.
  - Perform case distinction on whether `n` is even.
  - Simplify using the inductive hypothesis, the definitions of `tanpoly`, `POLY_MUL`, `ODD_POLY_DIFF`, `EVEN_POLY_DIFF`, and `REAL_MUL_RNEG`.
  - Apply `AP_TERM_TAC` and `AP_THM_TAC` several times and then simplify using the definition of `poly` before using real arithmetic axioms to conclude.

### Mathematical insight
This theorem states that the Taylor expansion of the tangent function, represented by the polynomial `tanpoly n`, is an odd function when `n` is even, and an even function times `x` when `n` is odd, which reflects the well-known parity properties of the tangent function.

### Dependencies
- Definitions: `EVEN`, `tanpoly`
- Theorems/Lemmas: `POLY_MUL`, `ODD_POLY_DIFF`, `EVEN_POLY_DIFF`, `REAL_MUL_RNEG`
- Tactics: `INDUCT_TAC`, `REWRITE_TAC`, `CONV_TAC`, `ONCE_DEPTH_CONV`, `POLY_DIFF_CONV`, `REAL_ARITH_TAC`, `POP_ASSUM MP_TAC`, `ASM_CASES_TAC`, `ASM_REWRITE_TAC`, `REPEAT STRIP_TAC`, `ASM_SIMP_TAC`, `TRY AP_TERM_TAC`, `AP_THM_TAC`

### Porting notes (optional)
- The proof relies heavily on algebraic simplification and real arithmetic. Porting to another system will require either similar automation or manual rewriting.
- The tactics `AP_TERM_TAC` and `AP_THM_TAC` are used to apply theorems to terms, ensure that your destination proof assistant can make this kind of application.


---

## TANNUMBER_EVEN

### Name of formal statement
TANNUMBER_EVEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TANNUMBER_EVEN = prove
 (`!n. EVEN n ==> (tannumber n = &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tannumber] THEN
  MATCH_MP_TAC(REAL_ARITH `(x = --x) ==> (x = &0)`) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_NEG_0] THEN
  ASM_SIMP_TAC[TANPOLY_ODD_EVEN]);;
```

### Informal statement
For all natural numbers `n`, if `n` is even, then `tannumber n` is equal to 0.

### Informal sketch
The proof proceeds as follows:
- Assume `EVEN n` for some natural number `n`.
- Expand `tannumber n` using its definition. This reveals that `tannumber n = tanpoly n &0`, the tangent polynomial evaluated at 0.
- Apply the theorem `(x = --x) ==> (x = &0)` with `x = tanpoly n &0`.
- Rewrite using `GSYM REAL_NEG_0` and `LAND_CONV o RAND_CONV`.
- Simplify using the fact that if `n` is even then `tanpoly n` is an odd polynomial, as stated in `TANPOLY_ODD_EVEN` and thus `tanpoly n &0 = &0`.

### Mathematical insight
This theorem states a property of the tangent numbers; namely, that the tangent number of an even index is always zero.  This stems from the fact that the tangent function is an odd function, and its Maclaurin series only involves odd powers. Therefore, when the index `n` is even, the `tannumber n`, which is related to the `n`-th derivative of the tangent function evaluated at 0, will evaluate to 0.

### Dependencies
- Definitions: `tannumber`
- Theorems: `REAL_NEG_0`, `TANPOLY_ODD_EVEN`
- Tactics: `REPEAT STRIP_TAC`, `REWRITE_TAC`, `MATCH_MP_TAC`, `GEN_REWRITE_TAC`, `ASM_SIMP_TAC`, `LAND_CONV`, `RAND_CONV`, `GSYM`


---

## TAYLOR_TAN_CONVERGES

### Name of formal statement
TAYLOR_TAN_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_TAN_CONVERGES = prove
 (`!x. abs(x) < pi / &2
       ==> (\n. tannumber n / &(FACT n) * x pow n) sums (tan x)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP TAN_POWSER) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[real_div; TANNUMBER_EVEN; REAL_MUL_LZERO; REAL_MUL_RZERO];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HARMONICSUMS_TANNUMBER; EVEN_ADD; ARITH; ADD_EQ_0] THEN
  REWRITE_TAC[ADD_SUB; real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `a * b * c * a' * d * b' * e = (c * d * e) * ((a * a') * (b * b'))`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN AP_TERM_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_MUL_RINV THEN
  SIMP_TAC[REAL_ARITH `&1 < x ==> ~(x - &1 = &0)`;
           REAL_POW2_CLAUSES; ADD_EQ_0; ARITH_EQ]);;
```

### Informal statement
For all real numbers `x`, if the absolute value of `x` is less than `pi / 2`, then the series defined by the sequence whose `n`-th term is `tannumber n / (FACT n) * x pow n` sums to `tan x`.

### Informal sketch
The proof demonstrates the convergence of the Taylor series for the tangent function.
- The proof starts by discharging the assumption `abs(x) < pi / 2` and applying the `TAN_POWSER` theorem.
- Then, equality implications and function application are used to set up the goal.
- Simplification with `FUN_EQ_THM` is performed, followed by introducing a natural number variable `n`.
- Cases are split based on whether `n` is even or odd.
   - The even case is handled by simplifying with `real_div`, `TANNUMBER_EVEN`, `REAL_MUL_LZERO`, and `REAL_MUL_RZERO`, which reduces to a trivial goal.
   - The odd case proceeds with further simplification.
- An involved simplification is done using the identity `HARMONICSUMS_TANNUMBER` along with arithmetic facts.
- The proof involves rewriting with associative and commutative properties of real multiplication to rearrange and simplify the terms.
- Then, the goal is simplified using `REAL_RAT_REDUCE_CONV` which rewrites to reduce the rational numbers.
- The proof concludes by using remaining arithmetic facts and identities.

### Mathematical insight
The theorem establishes the convergence of the Taylor series for the tangent function within the interval (-pi/2, pi/2). This is a fundamental result in real analysis and provides a way to approximate the tangent function using a polynomial series within its radius of convergence. The theorem is important as the taylor series expansion is used in various approximations of functions and this particular one is important for the tangent function which is a very fundamental function in mathematics.

### Dependencies
- `TAN_POWSER`
- `real_div`
- `TANNUMBER_EVEN`
- `REAL_MUL_LZERO`
- `REAL_MUL_RZERO`
- `HARMONICSUMS_TANNUMBER`
- `EVEN_ADD`
- `ARITH`
- `ADD_EQ_0`
- `ADD_SUB`
- `REAL_INV_MUL`
- `REAL_MUL_ASSOC`
- `REAL_MUL_RID`
- `REAL_RAT_REDUCE_CONV`
- `REAL_MUL_LID`
- `REAL_MUL_RINV`
- `REAL_ARITH`
- `REAL_POW2_CLAUSES`
- `FACT`
- `tannumber`
- `sums`

### Porting notes (optional)
- The `GEN_TAC` and `DISCH_THEN` tactics are common for discharging assumptions.
- `MATCH_MP_TAC` and `AP_THM_TAC` are used extensively to apply theorems and equalities.
- `REWRITE_TAC` is used to simplify with given equations.
- Tactics like `COND_CASES_TAC` and `ASM_SIMP_TAC` handle case splitting and assumption simplification, respectively.
- `CONV_TAC` applies conversions to terms.
- The careful manipulation of real arithmetic, especially associativity and commutativity (`AC REAL_MUL_AC`), needs to be reproduced accurately.
- Porting to Coq/Lean/Isabelle - will require establishing the tannumber and associated theorems. In addition, the convergence theorems are required and would need to be properly discharged.


---

## TAYLOR_X_COT_CONVERGES

### Name of formal statement
TAYLOR_X_COT_CONVERGES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_X_COT_CONVERGES = prove
 (`!x. &0 < abs(x) /\ abs(x) < pi
       ==> (\n. (if n = 0 then &1 else
                 tannumber (n - 1) / ((&1 - &2 pow n) * &(FACT(n - 1)))) *
                x pow n)
           sums (x * cot(x))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP COT_X_POWSER) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `tannumber(n - 1) = &0`
     (fun th -> SIMP_TAC[th; real_div; REAL_MUL_LZERO; REAL_MUL_RZERO]) THEN
    MATCH_MP_TAC TANNUMBER_EVEN THEN
    UNDISCH_TAC `ODD n` THEN
    SUBGOAL_THEN `n = SUC(n - 1)` MP_TAC THENL
     [UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[ODD; NOT_ODD]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[HARMONICSUMS_TANNUMBER; GSYM NOT_ODD] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `--(&2) * x * y * z * a = (&2 * y) * x * --a * z`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_INV_NEG; REAL_NEG_SUB; REAL_MUL_LID]);;
```

### Informal statement
For all real numbers `x`, if the absolute value of `x` is greater than 0 and less than `pi`, then the series whose `n`-th term is given by (if `n` is 0 then 1 else `tannumber(n - 1) / ((1 - 2^n) * FACT(n - 1)) * x^n`) sums to `x * cot(x)`.

### Informal sketch
The proof demonstrates that the given power series converges to `x * cot(x)` for `0 < |x| < pi`.
- Start with the power series representation of `cot(x)` from `COT_X_POWSER`
- Manipulate and simplify this known series to match the desired form by:
  - Expanding the series definition
  - Applying properties of functions and rewriting identities using theorems such as `FUN_EQ_THM` to handle function equality.
  - Splitting the proof into cases based on whether `n = 0` using `ASM_CASES_TAC` and rewriting accordingly.
  - Splitting the proof into the cases where `n` is Odd, and using rewrite rules accordingly.
  - If `n` is odd, proving that `tannumber(n - 1) = 0` using `TANNUMBER_EVEN`, and simplifying. Proving `n = SUC(n - 1)` given `~(n = 0)`.
  - Applying theorems and simplifying the resulting expressions.
  - Rewriting based on the properties of `tannumber` and whether `n` is odd using `HARMONICSUMS_TANNUMBER` and `NOT_ODD`.
  - Applying real arithmetic rules for division, multiplication, and negation.
  - Reducing rational expressions using `REAL_RAT_REDUCE_CONV`.

### Mathematical insight
This theorem establishes the convergence of a specific power series to the function `x * cot(x)` within the interval `(0, pi)`. The coefficients of the power series involve the `tannumber` function, which is related to tangent numbers. This result connects special functions (cotangent, tangent numbers) with power series representations. Understanding the convergence of such series is crucial in complex analysis and numerical computations.

### Dependencies

**Theorems:**
- `COT_X_POWSER`
- `FUN_EQ_THM`
- `TANNUMBER_EVEN`
- `HARMONICSUMS_TANNUMBER`
- `ODD`
- `NOT_ODD`

**Definitions:**
- `real_div`
- `REAL_MUL_LZERO`
- `REAL_MUL_RZERO`
- `REAL_INV_MUL`
- `REAL_MUL_ASSOC`
- `REAL_INV_NEG`
- `REAL_NEG_SUB`
- `REAL_MUL_LID`
- `FACT` (presumably)
- `tannumber` (presumably)
- `sums` (presumably)

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification with real arithmetic, so a proof assistant with strong automation in this area will be beneficial.
- The custom tactic `ONCE_REWRITE_TAC` used with `REAL_ARITH` might need to be emulated using other rewriting tactics in different proof assistants.
- The `tannumber` function will need a definition and potentially relevant lemmas in the target system.


---

## TANNUMBER_BOUND

### Name of formal statement
TANNUMBER_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TANNUMBER_BOUND = prove
 (`!n. abs(tannumber n) <= &4 * &(FACT n) * (&2 / pi) pow (n + 1)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THEN
  ASM_SIMP_TAC[TANNUMBER_EVEN; GSYM TANNUMBER_HARMONICSUMS] THEN
  (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
    [REAL_ABS_NUM; REAL_LE_MUL; REAL_POW_LE; REAL_POS; REAL_LE_DIV;
     PI_POS; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `a * b * c * d * e = (a * d) * c * b * e`] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_ARITH `&2 * x <= &4 <=> x <= &2`] THEN
    MP_TAC(SPEC `\m. inv (&(m + 1) pow (n + 1))` SER_ABS) THEN
    REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM; REAL_ABS_POW] THEN
    W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
     [MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN
      UNDISCH_TAC `ODD n` THEN
      SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
      REPEAT STRIP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `suminf (\m. inv(&(m + 1) pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SER_LE THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `ODD n` THEN
        SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
        REPEAT STRIP_TAC THEN ARITH_TAC;
        MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN
        UNDISCH_TAC `ODD n` THEN
        SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
        REPEAT STRIP_TAC THEN ARITH_TAC;
        MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN REWRITE_TAC[LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0,1) (\n. inv(&(n + 1) pow 2)) +
                suminf (\n. inv(&((n + 1) + 1) pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `(y = x) ==> x <= y`) THEN
      MATCH_MP_TAC SUM_UNIQ THEN
      MATCH_MP_TAC SER_OFFSET_REV THEN
      REWRITE_TAC[summable] THEN
      EXISTS_TAC
       `suminf (\n. inv(&(n + 1) pow 2)) -
       sum(0,1) (\n. inv(&(n + 1) pow 2))` THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] SER_OFFSET) THEN
      MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN REWRITE_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_1; ADD_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 + x <= &2 <=> x <= &1`] THEN
    SUBST1_TAC(MATCH_MP SUM_UNIQ SUMMABLE_INVERSE_SQUARES_LEMMA) THEN
    MATCH_MP_TAC SER_LE THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN REWRITE_TAC[REAL_POW_2] THEN
      REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
      REWRITE_TAC[REAL_POW_2; REAL_INV_MUL; REAL_ABS_INV; REAL_ABS_NUM;
                  REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
      REWRITE_TAC[summable] THEN
      EXISTS_TAC
       `suminf (\n. inv(&(n + 1) pow 2)) -
       sum(0,1) (\n. inv(&(n + 1) pow 2))` THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] SER_OFFSET) THEN
      MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN REWRITE_TAC[LE_REFL];
      REWRITE_TAC[summable] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[SUMMABLE_INVERSE_SQUARES_LEMMA]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN REWRITE_TAC[REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW] THEN
  SIMP_TAC[real_abs; PI_POS; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM real_abs] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LT; REAL_LT_IMP_LE; PI_POS] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&1 <= x ==> abs(x - &1) <= x`) THEN
  REWRITE_TAC[REAL_POW2_CLAUSES]);;
```

### Informal statement
For all natural numbers `n`, the absolute value of `tannumber n` is less than or equal to `4` times the factorial of `n` times `(2 / pi)` raised to the power of `(n + 1)`.

### Informal sketch
The proof proceeds by induction on the natural number `n`, splitting into two cases: `n` is even or `n` is odd.

- The case where `n` is even relies on `TANNUMBER_EVEN` and the symmetry of `TANNUMBER_HARMONICSUMS`. A series of simplifications using real arithmetic lemmas (`REAL_ABS_NUM`, `REAL_LE_MUL`, `REAL_POW_LE`, etc.) is performed to establish the bound.
- For the odd case, further simplification is needed, leading to inequalities involving infinite sums. The proof involves showing that `suminf (\m. inv (&(m + 1) pow (n + 1)))` satisfies certain bounds. The `SUMMABLE_INVERSE_POWERS` lemma is used. Several arithmetic manipulations of real-valued expressions, in conjunction with lemmas about summable series (`SER_LE`, `SER_OFFSET`), are applied to ultimately show that the tannumber is bounded.

### Mathematical insight
This theorem provides an upper bound on the absolute value of the `tannumber` function for a given natural number `n`. The bound is expressed in terms of the factorial function, the ratio `2/pi`, and powers. This is a standard estimate in analysis to determine convergence rates and error bounds.

### Dependencies
- `TANNUMBER_EVEN`
- `TANNUMBER_HARMONICSUMS`
- `REAL_ABS_NUM`
- `REAL_LE_MUL`
- `REAL_POW_LE`
- `REAL_POS`
- `REAL_LE_DIV`
- `PI_POS`
- `REAL_LT_IMP_LE`
- `real_div`
- `REAL_MUL_ASSOC`
- `AC REAL_MUL_AC`
- `REAL_ABS_MUL`
- `REAL_LE_MUL2`
- `REAL_ABS_POS`
- `REAL_ARITH`
- `SER_ABS`
- `REAL_ABS_INV`
- `REAL_ABS_POW`
- `SUMMABLE_INVERSE_POWERS`
- `ODD_EXISTS`
- `LEFT_IMP_EXISTS_THM`
- `REAL_LE_TRANS`
- `SER_LE`
- `REAL_POW_LT`
- `REAL_OF_NUM_LT`
- `REAL_OF_NUM_LE`
- `LE_REFL`
- `SUM_UNIQ`
- `SER_OFFSET_REV`
- `summable`
- `SER_OFFSET`
- `SUM_1`
- `ADD_CLAUSES`
- `SUMMABLE_INVERSE_SQUARES_LEMMA`
- `REAL_POW_2`
- `REAL_INV_MUL`
- `REAL_LE_RMUL`
- `REAL_LE_INV_EQ`
- `REAL_LE_INV2`
- `real_abs`
- `REAL_POW_MUL`
- `REAL_POW_INV`
- `REAL_POW2_CLAUSES`


---

## HARMONIC_SUMS

### Name of formal statement
HARMONIC_SUMS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let HARMONIC_SUMS = prove
 (`!n. (\m. inv (&(m + 1) pow (2 * (n + 1))))
       sums (pi pow (2 * (n + 1)) *
             tannumber(2 * n + 1) /
             (&2 * (&2 pow (2 * (n + 1)) - &1) * &(FACT(2 * n + 1))))`,
  GEN_TAC THEN
  SUBGOAL_THEN `summable (\m. inv (&(m + 1) pow (2 * (n + 1))))` MP_TAC THENL
   [MATCH_MP_TAC SUMMABLE_INVERSE_POWERS THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_SUM) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_EQ_LDIV_EQ; REAL_POW_LT; PI_POS] THEN
  REWRITE_TAC[ARITH_RULE `2 * n + 1 = 2 * (n + 1) - 1`] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c = a * c * b`] THEN
  MATCH_MP_TAC HARMONICSUMS_TANNUMBER THEN
  REWRITE_TAC[MULT_EQ_0; ADD_EQ_0; ARITH; EVEN_MULT]);;
```

### Informal statement
For all natural numbers `n`, the infinite sum of `1 / (m+1)^(2*(n+1))` (where `m` ranges from 0 to infinity) is equal to `(pi^(2*(n+1)) * tannumber(2*n+1)) / (2 * (2^(2*(n+1)) - 1) * FACT(2*n+1))`.

### Informal sketch
The proof proceeds as follows:
- First, prove that the series `summable (\m. inv (&(m + 1) pow (2 * (n + 1))))` is summable. This is achieved by using `SUMMABLE_INVERSE_POWERS`.
- Then, discharge the assumption that the series is summable and use `SUMMABLE_SUM` to work with the sum.
- Next, simplify the equation using `EQ_IMP` and `AP_TERM_TAC`.
- Rewrite using `REAL_MUL_SYM`.
- Simplify using theorems such as `GSYM REAL_EQ_LDIV_EQ`, `REAL_POW_LT`, and `PI_POS`.
- Rewrite the expression `2 * n + 1` as `2 * (n + 1) - 1`.
- Rearrange the multiplication using `AC REAL_MUL_AC a * b * c = a * c * b`.
- Apply `HARMONICSUMS_TANNUMBER`.
- Finally, rewrite using `MULT_EQ_0`, `ADD_EQ_0`, `ARITH`, and `EVEN_MULT` to complete the proof.

### Mathematical insight
This theorem establishes a closed-form expression for the infinite sum of inverse powers of integers, specifically where the powers are even numbers related to `n`. This result connects harmonic sums to powers of `pi` and the `tannumber` function, demonstrating a relationship between analysis and number theory. It is a classic and important result in the study of special functions and series.

### Dependencies
- `SUMMABLE_INVERSE_POWERS`
- `SUMMABLE_SUM`
- `REAL_MUL_SYM`
- `REAL_EQ_LDIV_EQ`
- `REAL_POW_LT`
- `PI_POS`
- `HARMONICSUMS_TANNUMBER`
- `MULT_EQ_0`
- `ADD_EQ_0`
- `FACT`
- `tannumber`


---

## mk_harmonic

### Name of formal statement
mk_harmonic

### Type of the formal statement
Definition

### Formal Content
```ocaml
let mk_harmonic =
  let pth = prove
   (`x * &1 / n = x / n`,
    REWRITE_TAC[real_div; REAL_MUL_LID]) in
  let final_RULE = CONV_RULE(TRY_CONV(GEN_REWRITE_CONV RAND_CONV [pth])) in
  fun n ->
    let th1 = SPEC(mk_small_numeral((n-1)/2)) HARMONIC_SUMS in
    let th2 = CONV_RULE NUM_REDUCE_CONV th1 in
    let th3 = CONV_RULE(ONCE_DEPTH_CONV TANNUMBER_CONV) th2 in
    let th4 = CONV_RULE REAL_RAT_REDUCE_CONV th3 in
    final_RULE th4;;
```

### Informal statement
The function `mk_harmonic` takes a natural number `n` as input and returns a theorem. The theorem states a simplified form of the harmonic sum up to the `n`-th term, derived from a general theorem about harmonic sums. The simplification involves rewriting the sum and performing arithmetic reductions.

### Informal sketch
The function `mk_harmonic` simplifies a general harmonic sum theorem for a given `n`.

- First, a lemma `x * &1 / n = x / n` is proved by rewriting with `real_div` and `REAL_MUL_LID`. This lemma will be used later for simplification.
- A conversion rule `final_RULE` is created that attempts to rewrite using the lemma `x * &1 / n = x / n`.
- For a given input `n`, a specific instance of a general theorem named `HARMONIC_SUMS` is created by specializing it with `(n-1)/2`.
- The resulting theorem undergoes a series of simplifications:
  - Arithmetic reduction using `NUM_REDUCE_CONV`.
  - Simplification of tangent numbers using `TANNUMBER_CONV`.
  - Reduction of real rational expressions using `REAL_RAT_REDUCE_CONV`.
- Finally, `final_RULE` applies the conversion rule based on rewriting `x * &1 / n = x / n`.

### Mathematical insight
This function automates the simplification of harmonic sum identities. It starts with a general form of the harmonic sum and, by specializing and simplifying, derives more specific identities depending on the value of `n`. The key idea is to pre-prove the `x * &1 / n = x / n` rewriting lemma and use it in a conversion to simplify the form.

### Dependencies
- Theorems: `HARMONIC_SUMS`

- Definitions: `real_div`, `REAL_MUL_LID`, `mk_small_numeral`, `NUM_REDUCE_CONV`, `TANNUMBER_CONV`, `REAL_RAT_REDUCE_CONV`

### Porting notes (optional)
The porting process will involve defining suitable rewriting rules corresponding to `real_div`, `REAL_MUL_LID`, `NUM_REDUCE_CONV`, `TANNUMBER_CONV`, and `REAL_RAT_REDUCE_CONV` in the target proof assistant. The tactic `ONCE_DEPTH_CONV` will need an equivalent to ensure the rewriting of tangent numbers is performed only once at a given depth. The `mk_small_numeral` function likely constructs a numeral term from an integer; ensure this construction exists in the target system.


---

## EULER_HARMONIC_SUM

### Name of formal statement
EULER_HARMONIC_SUM

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULER_HARMONIC_SUM = mk_harmonic 2;;
```

### Informal statement
The theorem `EULER_HARMONIC_SUM` states that the result of `mk_harmonic 2` is assigned to it.

### Informal sketch
- Call function `mk_harmonic` with value `2`.

### Mathematical insight
This theorem isolates the special case of the computation performed by the function `mk_harmonic` when applied to the value 2. The surrounding code appears to be related to testing `mk_harmonic` and measuring its runtime.

### Dependencies
- `mk_harmonic`


---

## TAYLOR_TAN_BOUND_GENERAL

### Name of formal statement
TAYLOR_TAN_BOUND_GENERAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_TAN_BOUND_GENERAL = prove
 (`!x n. abs(x) <= &1
         ==> abs(tan x - sum (0,n) (\m. tannumber m / &(FACT m) * x pow m))
             <= &12 * (&2 / &3) pow (n + 1) * abs(x) pow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(x) < pi / &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP TAYLOR_TAN_CONVERGES) THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC th THEN MP_TAC(MATCH_MP SUM_SUMMABLE th)) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP SER_OFFSET) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[sums] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_ABS_IMP) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC SEQ_LE_CONST THEN
  EXISTS_TAC `\r. abs(sum(0,r) (\m. (tannumber(m + n) / &(FACT(m + n))) *
                                    x pow (m + n)))` THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
  W(MP_TAC o PART_MATCH lhand SUM_ABS_LE o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0,m) (\r. &4 * (&2 / pi) pow (r + n + 1) * abs(x pow (r + n)))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM;
             REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    MP_TAC(SPEC `r + n:num` TANNUMBER_BOUND) THEN
    REWRITE_TAC[REAL_MUL_AC; GSYM ADD_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES] THEN
  REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ABS_POW; GSYM REAL_POW_MUL] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC] THEN
  REWRITE_TAC[SUM_CMUL] THEN
  SUBGOAL_THEN `&2 / pi * abs(x) < &2 / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 / pi * &1` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE;
                   PI_POS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; PI_POS] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `~(&2 / pi * abs(x) = &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 / pi * abs x < &2 / &3` THEN
    ONCE_REWRITE_TAC[TAUT `a ==> ~b <=> b ==> ~a`] THEN
    SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_ABS_POW;
                REAL_ABS_MUL; REAL_ABS_ABS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_MUL; real_div; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= abs p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[REAL_ARITH
   `&4 * x * y <= &12 * z <=> x * y <= z * &3`] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; real_div; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= abs p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[GP_FINITE] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  REWRITE_TAC[real_div; GSYM REAL_ABS_INV] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> abs(&1 - x) <= &1`) THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
       [REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
        REAL_ABS_POS; PI_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
       [REAL_POW_LE; REAL_LE_DIV; REAL_LE_MUL; REAL_POS;
        REAL_ABS_POS; PI_POS; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 / pi * &1` THEN
    ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_DIV; REAL_POS;
                 REAL_LT_IMP_LE; PI_POS] THEN
    SIMP_TAC[REAL_MUL_RID; REAL_LE_LDIV_EQ; PI_POS] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= &1 * p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= (&1 - a) * &1 ==> a <= abs(&1 - x)`) THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; PI_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
  MP_TAC PI_APPROX_25_BITS THEN
  MATCH_MP_TAC(REAL_ARITH
   `b + e <= a ==> abs(p - a) <= e ==> b <= p`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all real numbers `x` and natural numbers `n`, if the absolute value of `x` is less than or equal to 1, then the absolute value of the difference between the tangent of `x` and the sum from 0 to `n` of (`tannumber m` divided by the factorial of `m` multiplied by `x` raised to the power of `m`) is less than or equal to 12 times (`2/3`) raised to the power of (`n + 1`) times the absolute value of `x` raised to the power of `n`.

### Informal sketch
The proof establishes a bound on the truncation error of the Taylor series for the tangent function. The proof proceeds as follows:
- It starts by showing that `abs(x) < pi / 2`, which is necessary for the convergence of the Taylor series. This implication is proven using `REAL_LET_TRANS`, `PI_APPROX_25_BITS`, and real arithmetic.
- It applies `TAYLOR_TAN_CONVERGES` to establish that the Taylor series of `tan x` converges.
- Uses `SER_OFFSET` to offset the index of the summation.
- Applies `SUM_UNIQ` to show that the limit of the sum is unique.
- Rewrites using `sums` to relate the limit of the partial sums to the infinite sum.
- Applies `SEQ_ABS_IMP` and `SEQ_LE_CONST`.
- Bounding the absolute value of the remaining terms using `SUM_ABS_LE` and `TANNUMBER_BOUND`, which bounds the tangent numbers.
- Uses real arithmetic and inequalities with `PI_APPROX_25_BITS` to bound the infinite sum.
- Uses `SUM_LE` to relate the sums with inequalities.
- Manipulates the expression to obtain the final bound using real arithmetic and inequality relations

### Mathematical insight
This theorem provides a quantitative bound on the error when approximating the tangent function using a truncated Taylor series. This is essential in numerical analysis and computer arithmetic. The bound depends on the number of terms `n` used in the Taylor expansion and the magnitude of `x`.

### Dependencies
- `REAL_LET_TRANS`
- `REAL_LT_RDIV_EQ`
- `REAL_OF_NUM_LT`
- `ARITH`
- `PI_APPROX_25_BITS`
- `REAL_ARITH`
- `REAL_RAT_REDUCE_CONV`
- `TAYLOR_TAN_CONVERGES`
- `SUM_SUMMABLE`
- `SER_OFFSET`
- `SUM_UNIQ`
- `sums`
- `SEQ_ABS_IMP`
- `SEQ_LE_CONST`
- `SUM_ABS_LE`
- `REAL_LE_TRANS`
- `SUM_LE`
- `ADD_CLAUSES`
- `REAL_ABS_MUL`
- `REAL_ABS_DIV`
- `REAL_ABS_NUM`
- `REAL_MUL_ASSOC`
- `REAL_LE_RMUL`
- `REAL_ABS_POS`
- `REAL_LE_LDIV_EQ`
- `FACT_LT`
- `TANNUMBER_BOUND`
- `REAL_MUL_AC`
- `ADD_ASSOC`
- `ADD1`
- `real_pow`
- `REAL_POW_MUL`
- `REAL_POW_ADD`
- `SUM_CMUL`
- `REAL_LE_LMUL`
- `PI_POS`
- `REAL_LT_IMP_LE`
- `REAL_MUL_RID`
- `REAL_LT_LDIV_EQ`
- `REAL_LT_DIV`
- `TAUT`
- `abs`
- `REAL_LE_MUL2`
- `REAL_ABS_POW`
- `REAL_ABS_ABS`
- `real_div`
- `REAL_POS`
- `REAL_ABS_INV`
- `REAL_LE_INV2`
- `GP_FINITE`
- `REAL_ABS_SUB`
- `REAL_MUL_LID`
- `REAL_INV_INV`
- `REAL_POW_LE`
- `REAL_LE_DIV`
- `REAL_LE_MUL`
- `REAL_POW_1_LE`

### Porting notes (optional)
- The theorem relies heavily on real arithmetic and inequality reasoning, which may require some tuning in other proof assistants. Specifically, `PI_APPROX_25_BITS` may present difficulties if the target system does not have the same approximation of Pi.
- The use of `TANNUMBER_BOUND` will require porting that result.
- The handling of summations (`sums`, `SER_OFFSET`, `SUM_UNIQ`, `SUM_ABS_LE`, `SUM_LE`, `SUM_CMUL`) can vary significantly across proof assistants; it will be necessary to adapt the tactics accordingly while preserving the mathematical structure of the proof.


---

## TAYLOR_TAN_BOUND

### Name of formal statement
TAYLOR_TAN_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_TAN_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k)
           ==> abs(tan x -
                   sum (0,n) (\m. tannumber(m) / &(FACT(m)) * x pow m))
               <= &12 * (&2 / &3) pow (n + 1) * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&12 * (&2 / &3) pow (n + 1) * abs(x) pow n` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TAYLOR_TAN_BOUND_GENERAL THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LE_DIV; REAL_POS] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]]);;
```

### Informal statement
For all real numbers `x`, natural numbers `n`, and natural numbers `k`, if the absolute value of `x` is less than or equal to the inverse of 2 raised to the power of `k`, then the absolute value of the difference between the tangent of `x` and the sum from 0 to `n` of `tannumber(m) / FACT(m) * x pow m` is less than or equal to `12 * (2 / 3) pow (n + 1) * inv(2 pow (k * n))`.

### Informal sketch
The proof proceeds as follows:
- First strip the quantifiers from the goal.
- Then, use `REAL_LE_TRANS` to reduce the goal to proving the existence of a term `&12 * (&2 / &3) pow (n + 1) * abs(x) pow n`, and two inequalities.
- The first inequality follows from the theorem `TAYLOR_TAN_BOUND_GENERAL`.
- Then, the goal is reduced by `REAL_LE_TRANS` to proving `inv(&2 pow k)` allows rewriting and simplification using theorems relating to real numbers and powers.
- The second inequality is tackled by rewriting and simplification using theorems on real numbers, powers, and division.

### Mathematical insight
This theorem provides a bound on the error when approximating the tangent function `tan(x)` using its Taylor series expansion. The error bound is expressed in terms of `n` (the number of terms in the Taylor series), `x` (the point at which the tangent function is being approximated), and `k` (the factor that constrains the x value). This result is crucial for numerical analysis, giving guarantees on the accuracy of Taylor approximations.

### Dependencies
- `REAL_LE_TRANS`
- `TAYLOR_TAN_BOUND_GENERAL`
- `REAL_POW2_THM`
- `LE_0`
- `REAL_MUL_ASSOC`
- `REAL_LE_LMUL`
- `REAL_LE_MUL`
- `REAL_POW_LE`
- `REAL_LE_DIV`
- `REAL_POS`
- `REAL_POW_POW`
- `REAL_POW_INV`
- `REAL_POW_LE2`
- `REAL_ABS_POS`


---

## TAYLOR_TANX_BOUND

### Name of formal statement
TAYLOR_TANX_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_TANX_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs(tan x / x -
                   sum (0,n) (\m. tannumber(m+1) / &(FACT(m+1)) * x pow m))
               <= &12 * (&2 / &3) pow (n + 2) * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * b * c = b * (a * c)`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[ADD1; SPECL [`f:num->real`; `n:num`; `1`] SUM_OFFSET] THEN
  REWRITE_TAC[SUM_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV TANNUMBER_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&12 * (&2 / &3) pow ((n + 1) + 1) * abs(x) pow (n + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TAYLOR_TAN_BOUND_GENERAL THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
  REWRITE_TAC[GSYM ADD1; real_pow] THEN
  GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC
   `(a * b * c) * d = (a * b * d) * c`] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
    [REAL_LE_MUL; REAL_POW_LE; REAL_ABS_POS; REAL_LE_DIV; REAL_POS] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;
```

### Informal statement
For all real numbers `x`, natural numbers `n`, and natural numbers `k`, if the absolute value of `x` is less than or equal to the inverse of 2 raised to the power of `k`, and `x` is not equal to 0, then the absolute value of the difference between `tan x / x` and the sum from 0 to `n` of `tannumber(m+1) / FACT(m+1) * x pow m` is less than or equal to `12 * (2/3) pow (n+2) * inv(2 pow (k * n))`.

### Informal sketch
The proof demonstrates an upper bound on the error term when approximating `tan x / x` by its Taylor series.

- The proof begins by stripping the quantifiers and assumptions.
- It then applies `REAL_LE_RCANCEL_IMP` which is probably a theorem that allows cancellation on inequalities.
- It introduces `abs(x)` using `EXISTS_TAC`.
- Simplifies using assumptions, rewriting with `REAL_ABS_NZ` (absolute value is not zero), `REAL_ABS_MUL` (absolute value of a product), and `REAL_SUB_RDISTRIB` (distribution over subtraction).
- Rewrites with `REAL_DIV_RMUL` (division as multiplication), `REAL_MUL_SYM` (commutativity of multiplication), `SUM_CMUL` (scalar multiplication over sums), `REAL_MUL_AC` (associativity and commutativity of multiplication), `real_pow` (real power).
- Applies an offset to the summation using `ADD1` and `SUM_OFFSET`.
- Applies `SUM_1`.
- Evaluates `TANNUMBER_CONV` and uses reduction and simplification tactics (`NUM_REDUCE_CONV`, `REAL_RAT_REDUCE_CONV`, `REAL_SUB_RZERO`).
- Applies `REAL_LE_TRANS` (transitivity of less than or equal) and introduces `&12 * (&2 / &3) pow ((n + 1) + 1) * abs(x) pow (n + 1)` using `EXISTS_TAC`.
- Proves a first conjunct by applying `TAYLOR_TAN_BOUND_GENERAL` and `REAL_LE_TRANS` with introduced `inv(&2 pow k)`. After some simplification steps and rewriting, it uses `LE_0`.
- Rewrites using arithmetic (`ARITH_RULE`, `ADD1`) and applies simplification (`real_pow`).
- Rearranges terms and simplifies the inequality using theorems about multiplication, powers, and absolute values. Uses `REAL_LE_MUL` (multiplication and inequalities), `REAL_POW_LE` (power and inequalities), `REAL_ABS_POS` (absolute value is positive), `REAL_LE_DIV` (division and inequalities), and `REAL_POS` to remove variables.
- Rewrites using `REAL_POW_POW` and `REAL_POW_INV`.
- Concludes by applying `REAL_POW_LE2` and simplifying with `REAL_ABS_POS`.

### Mathematical insight
This theorem provides an error bound for the Taylor series approximation of the function `tan(x)/x`. The bound depends on `n` (the number of terms in the series), `x` (the point at which the function is evaluated), and `k` (a parameter controlling how close `x` is to 0), and can be used to estimate the accuracy of the Taylor approximation within a specified interval around 0.

### Dependencies
- `REAL_LE_RCANCEL_IMP`
- `REAL_ABS_NZ`
- `REAL_ABS_MUL`
- `REAL_SUB_RDISTRIB`
- `REAL_DIV_RMUL`
- `REAL_MUL_SYM`
- `SUM_CMUL`
- `REAL_MUL_AC`
- `real_pow`
- `ADD1`
- `SUM_OFFSET`
- `SUM_1`
- `TANNUMBER_CONV`
- `REAL_RAT_REDUCE_CONV`
- `REAL_SUB_RZERO`
- `REAL_LE_TRANS`
- `TAYLOR_TAN_BOUND_GENERAL`
- `LE_0`
- `REAL_POW2_THM`
- `REAL_LE_MUL`
- `REAL_POW_LE`
- `REAL_ABS_POS`
- `REAL_LE_DIV`
- `REAL_POS`
- `REAL_POW_POW`
- `REAL_POW_INV`
- `REAL_POW_LE2`


---

## TAYLOR_TANX_SQRT_BOUND

### Name of formal statement
TAYLOR_TANX_SQRT_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_TANX_SQRT_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ &0 < x
           ==> abs(tan (sqrt x) / sqrt(x) -
                   sum(0,n) (\m. tannumber(2 * m + 1) / &(FACT(2 * m + 1)) *
                                 x pow m))
               <= &12 * (&2 / &3) pow (2 * n + 2) *
                  inv(&2 pow (k DIV 2 * 2 * n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sqrt x`; `2 * n`; `k DIV 2`] TAYLOR_TANX_BOUND) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ; DIV_EQ_0; ARITH_EQ; NOT_LT] THEN
    SUBGOAL_THEN `&2 pow (k DIV 2) = sqrt(&2 pow (2 * (k DIV 2)))`
    SUBST1_TAC THENL
     [SIMP_TAC[SQRT_EVEN_POW2; EVEN_MULT; ARITH_EVEN; DIV_MULT; ARITH_EQ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SQRT_INV; REAL_LT_IMP_LE; REAL_POW2_CLAUSES] THEN
    ASM_SIMP_TAC[real_abs; SQRT_POS_LT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN SIMP_TAC[REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    MESON_TAC[LE_ADD; DIVISION; NUM_EQ_CONV `2 = 0`; MULT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM SUM_GROUP] THEN
  SIMP_TAC[SUM_2; TANNUMBER_EVEN; ARITH_EVEN; EVEN_ADD; EVEN_MULT] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_POW; SQRT_POW_2; REAL_LT_IMP_LE]);;
```

### Informal statement
For all real numbers `x`, natural numbers `n`, and natural numbers `k`, if the absolute value of `x` is less than or equal to the inverse of 2 raised to the power of `k`, and `x` is greater than 0, then the absolute value of the difference between `tan(sqrt(x)) / sqrt(x)` and the sum from 0 to `n` of the function `tannumber(2 * m + 1) / FACT(2 * m + 1) * x pow m` (where the function is applied to `m`) is less than or equal to  `12 * (2/3)^(2 * n + 2) * inv(2^(k DIV 2 * 2 * n))`.

### Informal sketch
The proof proceeds by:
- Applying `TAYLOR_TANX_BOUND` with appropriate specializations: `sqrt x` for `x`, `2 * n` for `n`, and `k DIV 2` for `k`.
- Rewriting the goal using the specialized `TAYLOR_TANX_BOUND`.
- Proving that `2 pow (k DIV 2) = sqrt(2 pow (2 * (k DIV 2)))`.
- Simplifying using assumptions about `x` and `k`, including `SQRT_POS_LT`, `REAL_LT_IMP_NZ`, `DIV_EQ_0`, `ARITH_EQ` and `NOT_LT`.
- Using monotonicity lemmas such as `SQRT_MONO_LE` and arithmetic lemmas to establish the inequalities.
- Applying simplification and rewriting rules for `SUM`, `TANNUMBER_EVEN`, and real number arithmetic.
- The proof manipulates the summation using `SUM_GROUP` and simplifies the expression to obtain the desired bound.

### Mathematical insight
The theorem provides a bound on the error when approximating `tan(sqrt(x)) / sqrt(x)` using its Taylor series expansion. The bound depends on `n` (the number of terms in the Taylor approximation) and `k` (related to the size of `x`). This result is important in numerical analysis for estimating the accuracy of Taylor series approximations.

### Dependencies
- `TAYLOR_TANX_BOUND`
- `SQRT_POS_LT`
- `REAL_LT_IMP_NZ`
- `DIV_EQ_0`
- `ARITH_EQ`
- `NOT_LT`
- `SQRT_EVEN_POW2`
- `EVEN_MULT`
- `ARITH_EVEN`
- `DIV_MULT`
- `GSYM SQRT_INV`
- `REAL_LT_IMP_LE`
- `REAL_POW2_CLAUSES`
- `real_abs`
- `SQRT_POS_LT`
- `REAL_LT_IMP_LE`
- `SQRT_MONO_LE`
- `REAL_ARITH`
- `REAL_LE_TRANS`
- `REAL_LE_INV2`
- `REAL_POW_MONO`
- `REAL_OF_NUM_LE`
- `LE_ADD`
- `DIVISION`
- `NUM_EQ_CONV`
- `MULT_SYM`
- `EQ_IMP`
- `GSYM MULT_ASSOC`
- `SUM_GROUP`
- `SUM_2`
- `TANNUMBER_EVEN`
- `ARITH_EVEN`
- `EVEN_ADD`
- `EVEN_MULT`
- `real_div`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`
- `GSYM REAL_POW_POW`
- `SQRT_POW_2`

### Porting notes (optional)
- The handling of real numbers and their properties (monotonicity, inequalities) should be carefully considered when porting to other proof assistants.
- The `DIV` operator and the tactics `DIV_EQ_0` would require special attention; often the division properties varies across provers.
- HOL Light's automation (e.g. `MESON_TAC`) may need to be replaced by more explicit proof steps in other systems.


---

## TAYLOR_COT_BOUND_GENERAL

### Name of formal statement
TAYLOR_COT_BOUND_GENERAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_COT_BOUND_GENERAL = prove
 (`!x n. abs(x) <= &1 /\ ~(x = &0)
         ==> abs((&1 / x - cot x) -
                 sum (0,n) (\m. (tannumber m /
                                 ((&2 pow (m+1) - &1) * &(FACT(m)))) *
                                x pow m))
             <= &4 * (abs(x) / &3) pow n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL] THEN REWRITE_TAC[GSYM SUM_CMUL] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `x * a * y = a * x * y`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN REWRITE_TAC[ADD1] THEN
  REWRITE_TAC[SUM_1; REAL_MUL_LZERO; REAL_SUB_RZERO; real_pow] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `abs(x) < pi` MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ABS_NZ]) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP TAYLOR_X_COT_CONVERGES) THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(ASSUME_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUM_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o SPEC `1` o MATCH_MP SER_OFFSET) THEN
  ASM_REWRITE_TAC[SUM_1; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SER_NEG) THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
  REWRITE_TAC[GSYM REAL_INV_NEG] THEN
  REWRITE_TAC[GSYM real_div] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN REWRITE_TAC[ADD_SUB] THEN
  DISCH_THEN(fun th ->
    ASSUME_TAC th THEN MP_TAC(MATCH_MP SUM_SUMMABLE th)) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP SER_OFFSET) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP SUM_UNIQ) THEN
  REWRITE_TAC[sums] THEN DISCH_THEN(MP_TAC o MATCH_MP SEQ_ABS_IMP) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC SEQ_LE_CONST THEN
  FIRST_ASSUM(fun th ->
   EXISTS_TAC(lhand(concl th)) THEN EXISTS_TAC `0` THEN
   CONJ_TAC THENL [ALL_TAC; ACCEPT_TAC th]) THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH lhand SUM_ABS_LE o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0,m) (\r. &4 *
                  (&2 / pi) pow (r + n + 1) / (&2 pow (r + n + 1) - &1) *
                  abs(x pow (r + n + 1)))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC `a * b * c = (c * a) * b`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; real_abs; REAL_SUB_LE] THEN
    REWRITE_TAC[REAL_POW2_CLAUSES] THEN REWRITE_TAC[GSYM real_abs] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_SUB_LE; REAL_POW2_CLAUSES] THEN
    SIMP_TAC[GSYM real_div; REAL_ABS_DIV; REAL_ABS_NUM;
             REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    MP_TAC(SPEC `r + n:num` TANNUMBER_BOUND) THEN
    REWRITE_TAC[REAL_MUL_AC; GSYM ADD_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * (b * c) * d = a * c * (b * d)`] THEN
  REWRITE_TAC[REAL_ABS_POW; GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum(0,m) (\r. &8 * inv(&2 pow (r + n + 1)) *
                       ((&2 * inv pi) * abs x) pow (r + n + 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&4 * x <= &8 * y <=> x <= &2 * y`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
      [REAL_POW_LE; REAL_LE_MUL; REAL_ABS_POS; REAL_POS;
       REAL_LT_IMP_LE; PI_POS; REAL_LE_INV_EQ] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM REAL_INV_INV] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT;
             ARITH; REAL_POW_LT] THEN
    REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; real_pow] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `&1 * x <= &2 * x - &1 <=> &1 <= x`] THEN
    REWRITE_TAC[REAL_POW2_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_INV; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `(&1 * x) * y = y * x`] THEN
  REWRITE_TAC[GSYM real_div] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_POW_ADD] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * b * c = (a * c) * b`] THEN
  REWRITE_TAC[SUM_CMUL] THEN
  SUBGOAL_THEN
   `(&4 * abs x) * (abs x * &1 / &3) pow n =
    &12 * (abs x / &3) pow (n + 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV
     [AC REAL_MUL_AC `a * b * c * d * e = (a * e) * d * b * c`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&8 * &3 / &2`)) THEN
  GEN_REWRITE_TAC RAND_CONV [AC REAL_MUL_AC
   `(a * b) * c = (a * c) * b`] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
  ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[REAL_ABS_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[real_div; REAL_ABS_MUL; REAL_ABS_ABS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= abs p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `abs(x) / pi < &1 / &3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&1 / pi` THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; PI_POS] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LT_INV2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e < a ==> abs(p - a) <= e ==> b < p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `~(abs(x) / pi = &1)` ASSUME_TAC THENL
   [UNDISCH_TAC `abs x / pi < &1 / &3` THEN
    ONCE_REWRITE_TAC[TAUT `a ==> ~b <=> b ==> ~a`] THEN
    SIMP_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[GP_FINITE] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x - &1 = --(&1 - x)`] THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> abs(&1 - x) <= &1`) THEN
    SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_LE_INV_EQ; REAL_ABS_POS;
             REAL_LT_IMP_LE; PI_POS] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN
    SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_LE_INV_EQ;
             REAL_LT_IMP_LE; PI_POS] THEN
    SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; PI_POS] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC PI_APPROX_25_BITS THEN
    MATCH_MP_TAC(REAL_ARITH
     `b + e <= a ==> abs(p - a) <= e ==> b <= &1 * p`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM real_div] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> b <= &1 - a ==> b <= abs(&1 - x)`)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all real numbers `x` and natural numbers `n`, if the absolute value of `x` is less than or equal to 1 and `x` is not equal to 0, then the absolute value of the difference between (`1 / x - cot x`) and the sum from 0 to `n` of the sequence defined by `(tannumber m / ((2 pow (m+1) - 1) * FACT(m))) * x pow m` is less than or equal to `4 * (abs(x) / 3) pow n`.

### Informal sketch
The proof establishes a bound on the error term when approximating `1/x - cot x` using a truncated Taylor series.

- The proof begins by simplifying the expression, leveraging properties of absolute values and sums.
- It's shown that `abs(x) < pi`.
- The convergence of the Taylor series for `x cot x` (specifically `TAYLOR_X_COT_CONVERGES`) is utilized, along with properties of infinite sums (`SER_OFFSET`, `SER_NEG`).
- Summation transformations (`SUM_UNIQ`, `SUM_SUMMABLE`) are applied to manipulate the series.
- The absolute value of the difference between the function and its truncated Taylor series is bounded by considering the absolute values of the terms in the infinite sum and using `SUM_ABS_LE`.
- The absolute value of the error is bounded using a geometric series argument to arrive at the inequality `abs((&1 / x - cot x) - sum (0,n) (\m. (tannumber m / ((&2 pow (m+1) - &1) * &(FACT(m)))) * x pow m)) <= &4 * (abs(x) / &3) pow n`.

### Mathematical insight
This theorem provides an explicit error bound for a Taylor series approximation of the function `1/x - cot x`. This is useful for numerical computations and analysis where approximations with known error bounds are essential. The `tannumber` sequence is critical, arising from the Taylor series expansion of `x / tan x`.

### Dependencies
*   `REAL_LE_LCANCEL_IMP`
*   `REAL_ABS_NZ`
*   `REAL_ABS_MUL`
*   `REAL_SUB_LDISTRIB`
*   `REAL_DIV_LMUL`
*   `SUM_CMUL`
*   `CONJUNCT2 real_pow`
*   `ADD1`
*   `SUM_1`
*   `REAL_MUL_LZERO`
*   `REAL_SUB_RZERO`
*   `real_pow`
*   `PI_APPROX_25_BITS`
*   `REAL_LET_TRANS`
*   `REAL_ARITH`
*   `TAYLOR_X_COT_CONVERGES`
*   `SUM_UNIQ`
*   `SUM_SUMMABLE`
*   `SER_OFFSET`
*   `SER_NEG`
*   `real_div`
*   `SEQ_ABS_IMP`
*   `SEQ_LE_CONST`
*   `SUM_ABS_LE`
*   `SUM_LE`
*   `ADD_CLAUSES`
*   `REAL_ABS_DIV`
*   `REAL_ABS_NUM`
*   `REAL_MUL_ASSOC`
*   `REAL_LE_RMUL`
*   `REAL_ABS_POS`
*   `REAL_INV_MUL`
*   `REAL_POW2_CLAUSES`
*   `REAL_LE_LDIV_EQ`
*   `REAL_OF_NUM_LT`
*   `FACT_LT`
*   `TANNUMBER_BOUND`
*   `REAL_POW_MUL`
*   `REAL_SUB_LE`
*   `REAL_LE_INV_EQ`
*   `REAL_POW_LE`
*   `REAL_LT_IMP_LE`
*   `PI_POS`
*   `REAL_LE_MUL`
*   `REAL_LT_MUL`
*   `REAL_LT_INV_EQ`
*   `ARITH`
*   `REAL_POW_LT`
*   `GP_FINITE`
*   `REAL_POW_ADD`
*   `REAL_POW_1`
*   `REAL_ABS_ABS`
*   `REAL_ABS_INV`
*   `REAL_MUL_LID`
*   `REAL_ABS_POW`
*   `REAL_LE_MUL2`
*   `REAL_POW_LE2`

### Porting notes (optional)
*   The theorem relies heavily on real number arithmetic and inequalities. Ensure the target proof assistant has comparable libraries.
*   The `tannumber` sequence and `FACT` (factorial) function need to be defined or available.
*   Porting this theorem might be challenging due to the extensive use of real analysis and series manipulation. Automation might be helpful but is not a substitute for understanding the underlying proof structure.


---

## TAYLOR_COT_BOUND

### Name of formal statement
TAYLOR_COT_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_COT_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 / x - cot x) -
                   sum (0,n) (\m. (tannumber m /
                                   ((&2 pow (m+1) - &1) * &(FACT(m)))) *
                                  x pow m))
               <= &4 / &3 pow n * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(x) <= &1 /\ ~(x = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP TAYLOR_COT_BOUND_GENERAL) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[real_div; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[GSYM REAL_POW_INV; GSYM REAL_POW_POW] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POS; REAL_ABS_POS] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[real_div; REAL_MUL_LID; REAL_POW_INV]);;
```

### Informal statement
For all real numbers `x` and natural numbers `n` and `k`, if the absolute value of `x` is less than or equal to the inverse of 2 raised to the power of `k`, and `x` is not equal to 0, then the absolute value of the difference between (1 divided by `x` minus the cotangent of `x`) and the sum from 0 to `n` of the terms ( `tannumber m` divided by (`2` raised to the power of `m+1` minus 1, all multiplied by the factorial of `m`), all multiplied by `x` raised to the power of `m`) is less than or equal to (4 divided by 3 raised to the power of `n`, all multiplied by the inverse of 2 raised to the power of `k` times `n`).

### Informal sketch
The proof proceeds as follows:
- First, reduce the goal to the case where `abs(x) <= 1` and `x != 0`. This is done by assuming the antecedent `abs(x) <= inv(&2 pow k) /\ ~(x = &0)` and showing that this implies `abs(x) <= &1 /\ ~(x = &0)`. This involves rewriting `inv(&2 pow 0)` to `&1` and using properties of real powers and inequalities.
- Next, instantiate the theorem `TAYLOR_COT_BOUND_GENERAL` with `n`.
- Apply a transitivity argument using `REAL_ARITH` to combine the inequality from the instantiation of `TAYLOR_COT_BOUND_GENERAL` with the current goal.
- Manipulate the resulting expression using properties of real division, multiplication, and exponentiation. Rewriting steps include simplification using `real_div`, `REAL_POW_MUL`, `REAL_MUL_ASSOC`, `REAL_POW_INV`, and `REAL_POW_POW`.
- Apply a lemma for inequalities involving real multiplication (`REAL_LE_LMUL`).
- Simplify further, using the properties of real numbers, including the positivity of real numbers and the absolute value of real numbers.
- Apply rewriting tactics to deal with the ordering of multiplication.
- Apply `REAL_LE_LMUL` again, and then simplify using `REAL_RAT_REDUCE_CONV`.

### Mathematical insight
This theorem provides a bound on the error when approximating `1/x - cot(x)` using a truncated Taylor series. The Taylor series involves `tannumber m`, which represents the tangent numbers. The bound is expressed in terms of `n` (the number of terms in the series), `k` (related to the upper bound on `abs(x)`), and `x` itself. This result is useful in numerical analysis and approximation theory for estimating the accuracy of Taylor approximations of the cotangent function.

### Dependencies
- `REAL_LE_TRANS`
- `REAL_LE_MUL`
- `REAL_LE_INV_EQ`
- `REAL_POS`
- `REAL_ABS_POS`
- `REAL_MUL_SYM`
- `REAL_LE_LMUL`
- `REAL_RAT_REDUCE_CONV`
- `REAL_DIV`
- `REAL_POW_MUL`
- `REAL_MUL_ASSOC`
- `REAL_POW_INV`
- `REAL_POW_POW`
- `REAL_POW_LE2`
- `REAL_MUL_LID`
- `TAYLOR_COT_BOUND_GENERAL`
- `REAL_ARITH`
- `REAL_POW2_THM`
- `LE_0`
- `FACT`
- `tannumber`

### Porting notes (optional)
- Porting this theorem requires that the target proof assistant has similar definitions and theorems about real numbers, including inequalities, powers, factorials, and tangent numbers.
- Ensuring that `TAYLOR_COT_BOUND_GENERAL` is ported correctly is very important, as it contains the crux of the core expansion bound.
- Pay close attention to the handling of real arithmetic and the simplification strategies used in HOL Light.


---

## TAYLOR_COTX_BOUND

### Name of formal statement
TAYLOR_COTX_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_COTX_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 / x - cot x) / x -
                   sum (0,n) (\m. (tannumber(m+1) /
                                   ((&2 pow (m+2) - &1) * &(FACT(m+1)))) *
                                  x pow m))
               <= (&4 / &3) / &3 pow n * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `abs(x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [AC REAL_MUL_AC `a * b * c = b * (a * c)`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[ARITH_RULE `n + 2 = (n + 1) + 1`] THEN
  REWRITE_TAC[ADD1; SPECL [`f:num->real`; `n:num`; `1`] SUM_OFFSET] THEN
  REWRITE_TAC[SUM_1] THEN
  CONV_TAC(ONCE_DEPTH_CONV TANNUMBER_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN `abs(x) <= &1 /\ ~(x = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n + 1` o MATCH_MP TAYLOR_COT_BOUND_GENERAL) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
  REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c * d = ((a * d) * b) * c`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_POW_MUL; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM REAL_POW_POW; GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
  SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_LE_DIV; REAL_POS] THEN
  REWRITE_TAC[REAL_INV_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;
```

### Informal statement
For all real numbers `x`, natural numbers `n`, and natural numbers `k`, if the absolute value of `x` is less than or equal to the inverse of 2 raised to the power of `k`, and `x` is not equal to 0, then the absolute value of the expression `(1/x - cot(x))/x - sum(m=0 to n, (tannumber(m+1) / ((2^(m+2) - 1) * FACT(m+1))) * x^m)` is less than or equal to `(4/3) / (3^n) * inv(2^(k*n))`.

### Informal sketch
The proof aims to establish a bound on the error term of the Taylor series approximation of `(1/x - cot x) / x`.

- Start by stripping the goal and canceling `REAL_LE_RCANCEL_IMP`.
- Simplify using the assumption `abs(x) <= inv(&2 pow k)` and the fact that `x` is non-zero.
- Rewrite the expression using properties of real numbers, such as distributivity, commutativity, and associativity.
- Manipulate the summation using `SUM_CMUL`, `SUM_OFFSET`, and reducing `SUM_1` to adjust the index and simplify the expression.
- Apply the `TAYLOR_COT_BOUND_GENERAL` theorem (after establishing `abs(x) <= 1 /\ ~(x = &0)`) and transitivity of real inequality.
- Simplify the expression using power rules, division, and associativity.
- Use inequalities involving multiplication and division, and simplify the constants to derive the desired bound.

### Mathematical insight
This theorem provides a quantitative bound on the error when approximating the function `(1/x - cot x)/x` by its Taylor series expansion up to the `n`-th term. The `tannumber` function provides the Taylor coefficients. This is useful for numerical analysis where one needs to control the approximation error.

### Dependencies
- `REAL_LE_RCANCEL_IMP`
- `REAL_ABS_NZ`
- `REAL_ABS_MUL`
- `REAL_SUB_RDISTRIB`
- `REAL_DIV_RMUL`
- `REAL_MUL_SYM`
- `SUM_CMUL`
- `real_pow`
- `ADD1`
- `SUM_OFFSET`
- `SUM_1`
- `TAYLOR_COT_BOUND_GENERAL`
- `REAL_POW_ADD`
- `REAL_POW_1`
- `real_div`
- `REAL_LE_RMUL`
- `REAL_ABS_POS`
- `REAL_MUL_ASSOC`
- `REAL_POW_MUL`
- `REAL_INV_MUL`
- `REAL_POW_POW`
- `REAL_INV_MUL`
- `REAL_LE_LMUL`
- `REAL_LE_DIV`
- `REAL_POS`
- `REAL_INV_MUL`
- `REAL_POW_INV`
- `REAL_POW_LE2`
- `REAL_LE_MUL`
### Porting notes (optional)
The main difficulty in porting this theorem might come from the presence of `tannumber` which is likely to be defined in HOL Light. If it is not available, one will need to define it first. The extensive use of real arithmetic and inequalities requires robust automation for real number reasoning. The `GSYM` tactic is used to rewrite with the symmetric version of an equation which can be replicated using appropriate rewrite tactics in other systems.


---

## TAYLOR_COTXX_BOUND

### Name of formal statement
TAYLOR_COTXX_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_COTXX_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ ~(x = &0)
           ==> abs((&1 - x * cot(x)) -
                   sum(0,n) (\m. (tannumber (m-1) /
                                  ((&2 pow m - &1) * &(FACT(m-1)))) *
                                 x pow m))
               <= &12 / &3 pow n * inv(&2 pow (k * n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `abs(inv x)` THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_INV_EQ_0] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_RDISTRIB] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
   [AC REAL_MUL_AC `(a * b) * c = b * a * c`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID] THEN
  REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  SUBGOAL_THEN `abs(x) <= &1 /\ ~(x = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `inv(&2 pow 0)`)) THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `n - 1` o MATCH_MP TAYLOR_COT_BOUND_GENERAL) THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[real_pow; real_div; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC; MULT_CLAUSES; REAL_INV_MUL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_DIV] THEN
    REWRITE_TAC[REAL_ABS_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow k)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&2 pow 0)` THEN
    REWRITE_TAC[REAL_POW2_THM; LE_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN `n = (n - 1) + 1` MP_TAC THENL
   [UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
   (RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_EQ_SUB_LADD] SUM_OFFSET)] THEN
  REWRITE_TAC[SUB_0; ADD_SUB; SUM_1] THEN
  SIMP_TAC[TANNUMBER_EVEN; EVEN] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
        [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)
        [REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(s1 = s2) /\ a <= b ==> s1 <= a ==> s2 <= b`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_RID] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_MUL_ASSOC] THEN
    REPEAT AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_RID]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL; REAL_MUL_ASSOC; real_div] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_ABS_INV; GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM REAL_ABS_NZ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN
  REWRITE_TAC[GSYM REAL_POW_INV] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD1] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; REAL_POW_INV]);;
```
### Informal statement
For all real numbers `x`, natural numbers `n`, and natural numbers `k`, if the absolute value of `x` is less than or equal to the inverse of 2 raised to the power of `k`, and `x` is not equal to 0, then the absolute value of the difference between (1 minus `x` times the cotangent of `x`) and (the sum from 0 to `n` of the function that maps `m` to `(tannumber (m-1) / ((2 to the power of m minus 1) * factorial(m-1))) * x to the power of m`) is less than or equal to (12 / 3 to the power of `n`) times the inverse of 2 to the power of (`k` times `n`).

### Informal sketch
The proof establishes a bound on the error term for the Taylor series approximation of `1 - x * cot(x)`.

- It proceeds by induction on `n`.
- Base case (`n = 0`): directly simplifies the sum to 0 and verifies the inequality using real arithmetic, `REAL_ARITH`, properties of inverses, and the fact that `abs(x) <= inv(&2 pow k)`.
- Inductive step:
  - Assumes the theorem holds for `n-1`.
  - Uses `TAYLOR_COT_BOUND_GENERAL` (the general form of the Taylor remainder bound for `cot(x)`) after a conditional case split to handle the restriction regarding the series index starting from `1` in `TAYLOR_COT_BOUND_GENERAL`, in combination with `SUM_OFFSET`.
  - After offsetting the index and extracting the first term and appealing to  `TANNUMBER_EVEN` and basic arithmetic simplifications, an intermediate goal is established to compare the LHS against the inductive hypothesis.
  - Rewrites and rearranges terms, exploiting properties of sums, multiplication, division, and exponentiation for real numbers.
  - Simplifies powers and inverses using lemmas like `REAL_POW_ADD`,`REAL_INV_MUL`, and `REAL_POW_MUL`.
  - Uses several derived simplification tactics, mainly based on `REAL_ARITH` and associativity/ commutativity of multiplication.
  - Establishes that a certain term is less than or equal to 1 using properties of real numbers, establishing intermediate goals, and appealing to exponentiation.

### Mathematical insight
The theorem gives a quantitative bound on the accuracy of approximating the function `1 - x * cot(x)` by its Taylor polynomial. The expression `tannumber (m-1)` refers to the tangent numbers (related to Bernoulli numbers), and the formula represents the coefficients in the Taylor series of `1 - x * cot(x)`. The bound is expressed in terms of `n` (the degree of the polynomial) and `k` (which controls the size of the interval around 0 where the approximation is valid).

### Dependencies
- `REAL_LE_RCANCEL_IMP`
- `GSYM REAL_ABS_NZ`
- `REAL_INV_EQ_0`
- `GSYM REAL_ABS_MUL`
- `REAL_SUB_RDISTRIB`
- `AC REAL_MUL_AC`
- `REAL_MUL_RINV`
- `REAL_MUL_RID`
- `GSYM real_div`
- `REAL_LE_TRANS`
- `REAL_RAT_REDUCE_CONV`
- `REAL_POW2_THM`
- `LE_0`
- `TAYLOR_COT_BOUND_GENERAL`
- `real_pow`
- `MULT_CLAUSES`
- `REAL_INV_MUL`
- `REAL_OF_NUM_LT`
- `ARITH`
- `GSYM REAL_LE_LDIV_EQ`
- `GSYM REAL_INV_DIV`
- `REAL_ABS_INV`
- `REAL_LE_INV2`
- `ADD_SUB`
- `TANNUMBER_EVEN`
- `EVEN`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`
- `GSYM SUM_CMUL`
- `REAL_MUL_LID`
- `FUN_EQ_THM`
- `REAL_POW_ADD`
- `REAL_POW_1`
- `GSYM REAL_MUL_ASSOC`
- `REAL_POW_ADD`
- `REAL_LE_LMUL`
- `REAL_POS`
- `REAL_LE_INV_EQ`
- `REAL_POW_LE`
- `REAL_ABS_POS`
- `REAL_POW_INV`
- `ADD1`

### Porting notes (optional)
- The proof relies heavily on real arithmetic tactics and simplification rules in HOL Light. In other proof assistants, it might be necessary to manually expand these tactics or to have comparable automation for real number reasoning.
- The use of `MATCH_MP_TAC` and similar tactics suggests that higher-order matching is used to apply existing theorems. Replicating this in other systems may require some care to ensure the matching behaves as expected.
- The tactic `GEN_REWRITE_TAC` applies a conversion repeatedly, and its behavior should be carefully checked during porting.


---

## TAYLOR_COTXX_SQRT_BOUND

### Name of formal statement
TAYLOR_COTXX_SQRT_BOUND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TAYLOR_COTXX_SQRT_BOUND = prove
 (`!x n k. abs(x) <= inv(&2 pow k) /\ &0 < x
           ==> abs((&1 - sqrt(x) * cot(sqrt(x))) -
                   sum(0,n) (\m. (tannumber (2*m-1) /
                                  ((&2 pow (2*m) - &1) * &(FACT(2*m-1)))) *
                                 x pow m))
               <= &12 / &3 pow (2 * n) * inv(&2 pow (k DIV 2 * 2 * n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`sqrt x`; `2 * n`; `k DIV 2`] TAYLOR_COTXX_BOUND) THEN
  W(C SUBGOAL_THEN (fun th -> REWRITE_TAC[th]) o funpow 2 lhand o snd) THENL
   [ASM_SIMP_TAC[SQRT_POS_LT; REAL_LT_IMP_NZ; DIV_EQ_0; ARITH_EQ; NOT_LT] THEN
    SUBGOAL_THEN `&2 pow (k DIV 2) = sqrt(&2 pow (2 * (k DIV 2)))`
    SUBST1_TAC THENL
     [SIMP_TAC[SQRT_EVEN_POW2; EVEN_MULT; ARITH_EVEN; DIV_MULT; ARITH_EQ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM SQRT_INV; REAL_LT_IMP_LE; REAL_POW2_CLAUSES] THEN
    ASM_SIMP_TAC[real_abs; SQRT_POS_LT; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2 pow k)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN SIMP_TAC[REAL_POW2_CLAUSES] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH] THEN
    MESON_TAC[LE_ADD; DIVISION; NUM_EQ_CONV `2 = 0`; MULT_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM SUM_GROUP] THEN
  SUBGOAL_THEN `!n. EVEN(((n * 2) + 1) - 1)` ASSUME_TAC THENL
   [INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; SUC_SUB1; SUB_0;
                MULT_CLAUSES; SUB_REFL; ADD_SUB] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_2; TANNUMBER_EVEN; ARITH_EVEN; EVEN_ADD; EVEN_MULT] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_POW; SQRT_POW_2; REAL_LT_IMP_LE]);;
```

### Informal statement
For all real numbers `x`, natural numbers `n`, and natural numbers `k`, if the absolute value of `x` is less than or equal to the inverse of 2 raised to the power of `k`, and `x` is strictly greater than 0, then the absolute value of the difference between (1 minus the square root of `x` times the cotangent of the square root of `x`) and the sum from 0 to `n` of the function that maps `m` to ((the `tannumber` of `2*m-1` divided by ((2 raised to the power of `2*m` minus 1) times the factorial of `2*m-1`)) times `x` raised to the power of `m`) is less than or equal to `12` divided by `3` raised to the power of `2*n` times the inverse of `2` raised to the power of `(k DIV 2 * 2 * n)`.

### Informal sketch
The theorem proves a bound on the error term when approximating `1 - sqrt(x) * cot(sqrt(x))` with the first `n` terms of its Taylor series. The proof proceeds as follows:

- First, the theorem `TAYLOR_COTXX_BOUND` is specialized with `sqrt x`, `2 * n`, and `k DIV 2`.
- Then the goal is transformed by rewriting it using the specialized `TAYLOR_COTXX_BOUND`.
- Several simplification steps are applied using theorems related to square roots, inequalities, and powers to manipulate the bound.These steps include:
  - Proving and substituting `&2 pow (k DIV 2) = sqrt(&2 pow (2 * (k DIV 2)))`.
  - Simplifying using theorems like `SQRT_INV`, `REAL_LT_IMP_LE`, `REAL_POW2_CLAUSES`, `real_abs`, `SQRT_POS_LT`.
  - Utilizing monotonicity lemmas for square roots and powers (`SQRT_MONO_LE`, `REAL_POW_MONO`).
  - Applying lemmas about inverses and performing arithmetic simplifications.
- Then `EQ_IMP` is used in conjuction with `MULT_ASSOC` and `SUM_GROUP` to bring the goal closer to the desired form.
- The statement `!n. EVEN(((n * 2) + 1) - 1)` is proven by induction.
- Several rewriting and arithmetic steps are then carried out to finish the proof.

### Mathematical insight
The theorem provides a quantitative bound on the approximation error, making it useful for numerical analysis and establishing the accuracy of approximations in specific ranges. It leverages the Taylor series expansion of a function related to the cotangent function.

### Dependencies
- `TAYLOR_COTXX_BOUND`
- `SQRT_POS_LT`
- `REAL_LT_IMP_NZ`
- `DIV_EQ_0`
- `ARITH_EQ`
- `NOT_LT`
- `SQRT_EVEN_POW2`
- `EVEN_MULT`
- `ARITH_EVEN`
- `DIV_MULT`
- `GSYM SQRT_INV`
- `REAL_LT_IMP_LE`
- `REAL_POW2_CLAUSES`
- `real_abs`
- `SQRT_POS_LT`
- `SQRT_MONO_LE`
- `REAL_ARITH`
- `REAL_LE_TRANS`
- `REAL_LE_INV2`
- `REAL_POW_MONO`
- `REAL_OF_NUM_LE`
- `ARITH`
- `LE_ADD`
- `DIVISION`
- `NUM_EQ_CONV`
- `MULT_SYM`
- `EQ_IMP`
- `GSYM MULT_ASSOC`
- `SUM_GROUP`
- `ADD_CLAUSES`
- `SUC_SUB1`
- `SUB_0`
- `MULT_CLAUSES`
- `SUB_REFL`
- `ADD_SUB`
- `EVEN_ADD`
- `EVEN_MULT`
- `SUM_2`
- `TANNUMBER_EVEN`
- `real_div`
- `REAL_MUL_LZERO`
- `REAL_ADD_RID`
- `GSYM REAL_POW_POW`
- `SQRT_POW_2`

### Porting notes (optional)
The use of tactics like `REPEAT STRIP_TAC` and `ASM_SIMP_TAC` indicates a heavy reliance on the simplifier. When porting, ensure the target proof assistant has a similarly powerful simplification engine with appropriate rewrite rules loaded. Special attention may be needed for definitions such as `tannumber` and `fact` and rules for divisibility.


---

