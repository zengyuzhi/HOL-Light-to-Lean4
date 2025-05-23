# lhopital.ml

## Overview

Number of statements: 3

`lhopital.ml` formalizes L'Hopital's rule within the HOL Light proof assistant. It resides within the `analysis` library and provides theorems related to evaluating limits of indeterminate forms using derivatives. The file likely contains definitions and proofs for various cases of L'Hopital's rule.


## MVT2

### Name of formal statement
MVT2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let MVT2 = prove
 (`!f g a b.
        a < b /\
        (!x. a <= x /\ x <= b ==> f contl x /\ g contl x) /\
        (!x. a < x /\ x < b ==> f differentiable x /\ g differentiable x)
        ==> ?z f' g'. a < z /\ z < b /\ (f diffl f') z /\ (g diffl g') z /\
                      (f b - f a) * g' = (g b - g a) * f'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) * (g(b) - g(a)) - g(x) * (f(b) - f(a))`;
                `a:real`; `b:real`] MVT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONT_SUB; CONT_MUL; CONT_CONST] THEN
    X_GEN_TAC `x:real` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    REWRITE_TAC[differentiable] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `f':real`) (X_CHOOSE_TAC `g':real`)) THEN
    EXISTS_TAC `f' * (g(b:real) - g a) - g' * (f b - f a)` THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] DIFF_CMUL; DIFF_SUB];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real` THEN
  REWRITE_TAC[REAL_ARITH
   `(fb * (gb - ga) - gb * (fb - fa)) -
    (fa * (gb - ga) - ga * (fb - fa)) = y <=> y = &0`] THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_SUB_0; REAL_LT_IMP_NE] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `l = &0` SUBST_ALL_TAC THEN
  UNDISCH_TAC
   `!x. a < x /\ x < b ==> f differentiable x /\ g differentiable x` THEN
  DISCH_THEN(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[differentiable] THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `f':real`) (X_CHOOSE_TAC `g':real`)) THEN
  MAP_EVERY EXISTS_TAC [`f':real`; `g':real`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC `\x:real. f(x) * (g(b) - g(a)) - g(x) * (f(b) - f(a))` THEN
  EXISTS_TAC `z:real` THEN
  ASM_SIMP_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] DIFF_CMUL; DIFF_SUB]);;
```

### Informal statement
For all real-valued functions `f` and `g`, and for all real numbers `a` and `b`, if `a` is less than `b`, and for all `x`, if `x` is between `a` and `b` (inclusive), then `f` and `g` are continuous from the left at `x`, and for all `x`, if `x` is strictly between `a` and `b`, then `f` and `g` are differentiable at `x`, then there exist real numbers `z`, `f'`, and `g'` such that `z` is strictly between `a` and `b`, `f` is differentiable at `z` with derivative `f'`, `g` is differentiable at `z` with derivative `g'`, and `(f b - f a) * g' = (g b - g a) * f'`.

### Informal sketch
The proof proceeds as follows:

- Start by stripping the quantifiers and assumptions.
- Apply the mean value theorem `MVT` to the function `\x. f x * (g b - g a) - g x * (f b - f a)` on the interval `[a, b]`. Assumptions of `MVT` are discharged by continuity and differentiability assumptions on `f` and `g` along with theorems `CONT_SUB`, `CONT_MUL`, and `CONT_CONST`. Also rewrite with `differentiable` to create assumptions of existence of derivatives of `f` and `g` which are then existentially chosen. We then perform a simplification with the differentiation theorems `DIFF_CMUL` and `DIFF_SUB` and `REAL_MUL_SYM`.
- Rearrange the existential quantifiers so that the `z` gets quantified last.
- Use assumption, that there exists a real `z` that satisfies `(f b - f a)*(g z)' - (g b - g a)*(f z)' = 0`.
- Use `REAL_ARITH` to show `(fb * (gb - ga) - gb * (fb - fa)) - (fa * (gb - ga) - ga * (fb - fa)) = y <=> y = &0`
- Apply `REAL_ENTIRE`, `REAL_SUB_0` and `REAL_LT_IMP_NE` to derive that `(g b - g a) != 0`.
- Supply witness for the `l` and then do variable substitution to replace l by 0.
- Discharge the differentiability assumptions and then use `DIFF_UNIQ` to equate derivative `f'` using the existence assumption.
- Existentially quantify the chosen derivatives and `z`.

### Mathematical insight
This theorem is the Cauchy mean value theorem, a generalization of the mean value theorem. It relates the difference of the values of two functions `f` and `g` at the endpoints of an interval to the derivatives of the functions at some point within the interval. This result is used in the proof of L'Hôpital's rule.

### Dependencies
- `Library/analysis.ml`
- `CONT_SUB`
- `CONT_MUL`
- `CONT_CONST`
- `differentiable`
- `DIFF_CMUL`
- `DIFF_SUB`
- `REAL_MUL_SYM`
- `SWAP_EXISTS_THM`
- `MONO_EXISTS`
- `REAL_ARITH`
- `REAL_ENTIRE`
- `REAL_SUB_0`
- `REAL_LT_IMP_NE`
- `DIFF_UNIQ`
- `MVT`
### Porting notes (optional)
The proof relies heavily on rewriting and simplification with real arithmetic. Special attention should be paid to the way the derivatives are handled and how the function is constructed to enable application of the standard mean value theorem `MVT`.


---

## LHOPITAL_WEAK

### Name of formal statement
LHOPITAL_WEAK

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LHOPITAL_WEAK = prove
 (`!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        f(c) = &0 /\ g(c) = &0 /\ (f --> &0) c /\ (g --> &0) c /\
        ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `!x. &0 < abs(x - c) /\ abs(x - c) < d
        ==> ?z. &0 < abs(z - c) /\ abs(z - c) < abs(x - c) /\
                f(x) * g'(z) = f'(z) * g(x)`
  (LABEL_TAC "*") THENL
   [X_GEN_TAC `x:real` THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `&0 < abs(x - c) /\ abs(x - c) < d
      ==> c < x /\ x < c + d \/ c - d < x /\ x < c`)) THEN
    STRIP_TAC THENL
     [MP_TAC(SPECL
       [`f:real->real`; `g:real->real`; `c:real`; `x:real`] MVT2) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o funpow 2 LAND_CONV)
          [REAL_LE_LT] THEN
        ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_IMP_LE; differentiable;
          REAL_ARITH
          `c < z /\ z <= x /\ x < c + d ==> &0 < abs(z - c) /\ abs(z - c) < d`];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN GEN_REWRITE_TAC (funpow 4 RAND_CONV) [REAL_MUL_SYM] THEN
      REPEAT STRIP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(fun th -> MP_TAC th THEN
          MATCH_MP_TAC EQ_IMP THEN BINOP_TAC) THEN
        ASM_MESON_TAC[DIFF_UNIQ; REAL_ARITH
         `c < z /\ z < x /\ x < c + d ==> &0 < abs(z - c) /\ abs(z - c) < d`]];
      MP_TAC(SPECL
       [`f:real->real`; `g:real->real`; `x:real`; `c:real`] MVT2) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV o RAND_CONV)
          [REAL_LE_LT] THEN
        ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_IMP_LE; differentiable;
          REAL_ARITH
          `c - d < x /\ x <= z /\ z < c ==> &0 < abs(z - c) /\ abs(z - c) < d`];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_LNEG; REAL_EQ_NEG2] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      GEN_REWRITE_TAC (funpow 4 RAND_CONV) [REAL_MUL_SYM] THEN
      REPEAT STRIP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(fun th -> MP_TAC th THEN
         MATCH_MP_TAC EQ_IMP THEN BINOP_TAC) THEN
        ASM_MESON_TAC[DIFF_UNIQ; REAL_ARITH
         `c - d < x /\ x < z /\ z < c
          ==> &0 < abs(z - c) /\ abs(z - c) < d`]]];
    ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `((\x. f' x / g' x) --> L) c` THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real`; `r:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  UNDISCH_TAC
   `!x. &0 < abs(x - c) /\ abs(x - c) < r ==> abs(f' x / g' x - L) < e` THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `z:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> abs(x - l) < e ==> abs(y - l) < e`) THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(gz = &0) /\ ~(gx = &0) /\ fx * gz = fz * gx ==> fz / gz = fx / gx`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  MP_TAC(ASSUME `&0 < abs(x - c)`) THEN DISCH_THEN(MP_TAC o MATCH_MP
   (REAL_ARITH `&0 < abs(x - c) ==> c < x \/ x < c`)) THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`g:real->real`; `c:real`; `x:real`] ROLLE) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC (funpow 2 LAND_CONV) [REAL_LE_LT] THEN
      ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_TRANS; REAL_ARITH
       `c < z /\ z <= x /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[differentiable; REAL_LT_TRANS; REAL_ARITH
       `c < z /\ z < x /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[DIFF_UNIQ];
    MP_TAC(SPECL [`g:real->real`; `x:real`; `c:real`] ROLLE) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_LE_LT] THEN
      ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_TRANS; REAL_ARITH
       `x <= z /\ z < c /\ z < c /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[differentiable; REAL_LT_TRANS; REAL_ARITH
       `x < z /\ z < c /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[DIFF_UNIQ]]);;
```

### Informal statement
For all real-valued functions `f` and `g`, their derivatives `f'` and `g'`, real numbers `c`, `L`, and `d`, if `0 < d` and for all `x`, if `0 < |x - c|` and `|x - c| < d`, then `f` is differentiable at `x` with derivative `f'(x)`, `g` is differentiable at `x` with derivative `g'(x)`, and `g'(x)` is not equal to `0`; and `f(c) = 0` and `g(c) = 0` and the limit of `f` as `x` approaches `c` is `0` and the limit of `g` as `x` approaches `c` is `0`, and the limit of `f'(x) / g'(x)` as `x` approaches `c` is `L`, then the limit of `f(x) / g(x)` as `x` approaches `c` is `L`.

### Informal sketch
The proof demonstrates a weak form of L'Hôpital's rule, specifically for the 0/0 indeterminate form.
- The initial goal is to prove that under the given conditions, if `f'/g'` approaches `L` as `x` approaches `c`, then `f/g` also approaches `L` as `x` approaches `c`.
- A key step involves showing the existence of a `z` between `x` and `c` such that `f(x) * g'(z) = f'(z) * g(x)`. This is achieved using the Mean Value Theorem (`MVT2`). Two cases are considered: `c < x` and `x < c`.
- The MVT2 is applied to both cases, with appropriate adjustments for the direction of the interval between `c` and `x`.
- The Mean Value Theorem requires establishing differentiability and continuity. This uses theorems such as `CONTL_LIM`, `DIFF_CONT`, and `differentiable`.
- After establishing the existence of such a `z`, the proof uses the assumption that `f'(x)/g'(x)` tends to `L` as `x` tends to `c`.
- Given `epsilon > 0`, there exists a `k > 0` such that if `0 < |x - c| < k` then `|f'(x)/g'(x) - L| < epsilon`.
- The proof then demonstrates (using the intermediate point `z`) that the same holds for `f(x)/g(x)`. Rolle's theorem is used to ensure denominators aren't zero.
- The theorem `REAL_FIELD` is used to rewrite `fx * gz = fz * gx` into `fz / gz = fx / gx`.

### Mathematical insight
This theorem provides a specific case of L'Hôpital's rule which is a powerful tool for evaluating limits of indeterminate forms. In this version we assume `f(c) = g(c) = 0` and the limits of `f` and `g` at `c` are `0`. The condition that `g'(x)` is non-zero in a neighborhood of `c` is crucial to avoid division by zero.

### Dependencies
- `CONTL_LIM`
- `DIFF_CONT`
- `REAL_LT_IMP_LE`
- `differentiable`
- `LIM`
- `REAL_DOWN2`
- `ROLLE`
- `REAL_FIELD`
- `NOT_IMP`
- `CONJ_ASSOC`
- `NOT_EXISTS_THM`

### Porting notes (optional)
- The proof relies heavily on real analysis theorems like the Mean Value Theorem and Rolle's Theorem, so ensure that the target proof assistant has these results available.
- Be mindful of differences in how differentiability and limits are defined and handled.
- The tactic `ASM_MESON_TAC` is used for automated theorem proving in real arithmetic; ensure that the target system has comparable automation.


---

## LHOPITAL

### Name of formal statement
LHOPITAL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LHOPITAL = prove
 (`!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        (f --> &0) c /\ (g --> &0) c /\ ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`\x:real. if x = c then &0 else f(x)`;
                `\x:real. if x = c then &0 else g(x)`;
                `f':real->real`; `g':real->real`;
                `c:real`; `L:real`; `d:real`] LHOPITAL_WEAK) THEN
  SIMP_TAC[LIM; REAL_ARITH `&0 < abs(x - c) ==> ~(x = c)`] THEN
  REWRITE_TAC[diffl] THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[diffl] THENL
   [MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC `\h. (f(x + h) - f x) / h`;
    MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC `\h. (g(x + h) - g x) / h`;
    ASM_MESON_TAC[]] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < abs(x - c) ==> ~(x = c)`] THEN
  REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `abs(x - c)` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < abs(x - c) /\ &0 < abs z /\ abs z < abs(x - c) ==> ~(x + z = c)`] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM]);;
```

### Informal statement
For all real-valued functions `f` and `g`, their derivatives `f'` and `g'`, real numbers `c`, `L`, and `d`, if `0 < d` and for all `x`, if `0 < |x - c|` and `|x - c| < d`, then `f` is differentiable at `x` with derivative `f'(x)`, `g` is differentiable at `x` with derivative `g'(x)`, and `g'(x)` is not equal to `0`, and `f(x)` approaches `0` as `x` approaches `c`, and `g(x)` approaches `0` as `x` approaches `c`, and `f'(x) / g'(x)` approaches `L` as `x` approaches `c`, then `f(x) / g(x)` approaches `L` as `x` approaches `c`.

### Informal sketch
The proof proceeds by:
- Generalizing the goal using `REPEAT GEN_TAC`, introducing the universally quantified variables.
- Applying `LHOPITAL_WEAK` with specific instantiations for `f`, `g`, `f'`, `g'`, `c`, `L`, and `d`. This likely relies on a weaker version of L'Hôpital's rule that might have stricter conditions or apply in a slightly different setting.
- Simplifying using `LIM` (limit definition) and real arithmetic to establish `&0 < abs(x - c) ==> ~(x = c)`.
- Rewriting with the definition of `diffl` (differentiability).
- Applying `STRIP_TAC` twice to break down the implications.
- Using assumptions to deduce facts with `FIRST_X_ASSUM MATCH_MP_TAC` and `ASM_REWRITE_TAC[]`.
- Repeatedly applying `STRIP_TAC` and simplifying with `ASM_SIMP_TAC[diffl]`.
- Applying `LIM_TRANSFORM` twice with the existence of the limits of `(f(x + h) - f x) / h` and `(g(x + h) - g x) / h`, instantiated via `EXISTS_TAC`.
- Resolving goals with `ASM_MESON_TAC[]`.
- Simplifying with real arithmetic to establish `&0 < abs(x - c) ==> ~(x = c)`.
- Rewriting with the limit definition (`LIM`).
- Introducing an epsilon (`e:real`) with `X_GEN_TAC` and discharging an assumption with `DISCH_TAC`.
- Asserting the existence of `abs(x - c)` with `EXISTS_TAC`.
- Rewriting using `REAL_SUB_RZERO`.
- Simplifying with real arithmetic regarding absolute values (`REAL_ARITH`).
- Rewriting using reflexivity and absolute value properties (`REAL_SUB_REFL; REAL_ABS_NUM`).

### Mathematical insight
This theorem states L'Hôpital's rule for the 0/0 indeterminate form. L'Hôpital's rule provides a method for evaluating limits of indeterminate forms by taking the ratio of the derivatives. The theorem formalizes the conditions under which the limit of the ratio of two functions is equal to the limit of the ratio of their derivatives, specifically when both functions approach zero. The condition `&0 < abs(x - c) /\ abs(x - c) < d` specifies a punctured neighborhood around `c`.

### Dependencies
- `LIM`: Definition of limit
- `REAL_ARITH`: Real number arithmetic rules.
- `diffl`: Definition of differentiability
- `LIM_TRANSFORM` : Theorem about transforming limits
- `REAL_SUB_RZERO`: Theorem that x - 0 = x
- `REAL_SUB_REFL`: Theorem that x - x = 0
- `REAL_ABS_NUM`: Theorems about absolute values
- `LHOPITAL_WEAK`: a variant (possibly weaker) version of L'Hopital's rule

### Porting notes (optional)
- The proof relies on a weaker version of L'Hôpital's rule (`LHOPITAL_WEAK`). Ensure that such a version or its equivalent is available or proven first.
- The extensive use of real arithmetic (`REAL_ARITH`) suggests that the target proof assistant needs strong automation for real number reasoning.
- The tactics involving limits (`LIM`, `LIM_TRANSFORM`) indicate that the target system should have good support for limit reasoning.


---

