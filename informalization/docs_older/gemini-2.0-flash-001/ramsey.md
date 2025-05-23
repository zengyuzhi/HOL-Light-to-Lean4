# ramsey.ml

## Overview

Number of statements: 186

The file `ramsey.ml` formalizes the Infinite Ramsey's Theorem in HOL Light. It represents a port of a previous proof done in HOL88. The primary goal is to provide a formalization of Ramsey's theorem within HOL Light.


## is_neg_imp

### Name of formal statement
is_neg_imp

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_neg_imp tm =
  is_neg tm || is_imp tm;;
```

### Informal statement
The term `tm` is `is_neg_imp` if and only if `tm` is a negation or `tm` is an implication.

### Informal sketch
The definition introduces a predicate `is_neg_imp` that checks if a term is either a negation (`is_neg`) or an implication (`is_imp`). It is a simple disjunction of two existing predicates.

### Mathematical insight
This definition provides a convenient way to check if a term falls into one of two important logical categories (negation or implication). Such predicates can be useful for structuring proofs by cases or for filtering terms based on their logical form.

### Dependencies
- `is_neg`
- `is_imp`


---

## dest_neg_imp

### Name of formal statement
dest_neg_imp

### Type of the formal statement
Definition

### Formal Content
```ocaml
let dest_neg_imp tm =
  try dest_imp tm with Failure _ ->
  try (dest_neg tm,mk_const("F",[]))
  with Failure _ -> failwith "dest_neg_imp";;
```

### Informal statement
The function `dest_neg_imp` takes a term `tm` as input. It attempts to decompose `tm` as an implication using `dest_imp`. If this fails, it attempts to decompose `tm` as a negation using `dest_neg` and pairs the result with the constant `F`. If both attempts fail, it raises the exception "dest_neg_imp".

### Informal sketch
The function `dest_neg_imp` attempts to deconstruct a term `tm` progressively.
- First, the function attempts to deconstruct the term `tm` as an implication. That is, it tries to find terms `p` and `q` such that `tm` is `p ==> q`.
- If the first step fails, the function attempts to deconstruct `tm` as a negation. That is, it tries to find a term `p` such that `tm` is `~p`. If this succeeds, the function returns the pair `(p, F)`, where `F` is a constant representing falsehood.
- If both attempts fail, an exception named `dest_neg_imp` is raised.

### Mathematical insight
This function provides a way to treat a negated term `~p` as an implication `p ==> F`, where `F` represents falsehood. This can be useful for normalizing logical expressions or for simplifying reasoning about negation in terms of implication.

### Dependencies
- `dest_imp`
- `dest_neg`
- `mk_const`
- `F` (Falsehood)


---

## PROVE

### Name of formal statement
PROVE

### Type of the formal statement
Definition

### Formal Content
```ocaml
let PROVE = prove;;
```

### Informal statement
Define `PROVE` as the function `prove`.

### Informal sketch
- The definition introduces `PROVE` as an alias for the `prove` function within HOL Light. This function is the core workhorse that drives **goal-directed theorem proving**, where a theorem is established by reducing it to simpler subgoals via tactics until each subgoal is trivially true by assumption or existing theorems. The specifics of the `prove` function's behavior are context-dependent, relying on the current subgoal stack and active theorems, modified by tactics.

### Mathematical insight
The mathematical insight is defining the connection to the `prove` tactic for later overwriting.

### Dependencies
None

### Porting notes
- `PROVE`'s behavior depends on the implementation details of HOL Light's proof environment. The equivalent in other systems (e.g., Coq's `Ltac`, Lean's `tactic`) involves setting up the proof state and applying corresponding tactics that reduce the initial goal to trivially provable subgoals. The exact structure will depend on which tactic framework or automation is being used.


---

## prove_thm((s:string),g,t)

### Name of formal statement
prove_thm

### Type of the formal statement
Theorem definition

### Formal Content
```ocaml
let prove_thm((s:string),g,t) = prove(g,t);;
```

### Informal statement
The function `prove_thm` takes a string `s`, a goal `g`, and a term `t` as input and attempts to prove `t` from the assumptions in `g`, by calling the primitive `prove` function.

### Informal sketch
The function `prove_thm` is defined simply by calling the `prove` function, which is responsible for conducting proof search based on the goal and term provided. The string `s` plays no role in the current definition, suggesting it may be used in other versions or for side effects such as debugging or logging in other `prove_thm` variations.

### Mathematical insight
The function effectively attempts to prove a theorem `t` given assumptions `g`. It encapsulates the core proof search functionality of HOL Light.

### Dependencies
- `prove`


---

## (CONV_OF_RCONV:

### Name of formal statement
CONV_OF_RCONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (CONV_OF_RCONV: conv -> conv) =
  let rec get_bv tm =
    if is_abs tm then bndvar tm
    else if is_comb tm then try get_bv (rand tm) with Failure _ -> get_bv (rator tm)
    else failwith "" in
  fun conv tm ->
  let v = get_bv tm in
  let th1 = conv tm in
  let th2 = ONCE_DEPTH_CONV (GEN_ALPHA_CONV v) (rhs(concl th1)) in
  TRANS th1 th2;;
```

### Informal statement
Define a function `CONV_OF_RCONV` that takes a conversion `conv` and a term `tm` as input. The function first finds the binding variable `v` within the term `tm`. It applies the given conversion `conv` to `tm`, resulting in a theorem `th1`. It then applies a conversion that alpha-renames the variable `v` on the right-hand side of the conclusion of `th1` to obtain a theorem `th2`. Finally, it returns the transitive combination (`TRANS`) of `th1` and `th2`.
The function `get_bv` finds the binding variable inside a term. If the term is an abstraction, it returns the bound variable. If it is a combination, it tries to find the binding variable in the right-hand side and, if that fails, it tries the left-hand side.

### Informal sketch
The function `CONV_OF_RCONV` takes a conversion `conv` and a term `tm` and performs the following steps:
- Determine the binding variable `v` within the term `tm` using the auxiliary function `get_bv`. `get_bv` recursively traverses the term:
  - If the term is an abstraction (`is_abs tm`), the bound variable (`bndvar tm`) is returned.
  - If the term is a combination (`is_comb tm`), `get_bv` first attempts to find a binding variable in the right operand (`rand tm`). If this fails, it attempts to find a binding variable in the left operand (`rator tm`).
  - If neither of these cases applies, `get_bv` fails.
- Apply the given conversion `conv` to the input term `tm`, yielding a theorem `th1`.
- Apply the `ONCE_DEPTH_CONV` conversion to the right-hand side of the conclusion of the theorem `th1`. This conversion uses `GEN_ALPHA_CONV v` to alpha-rename the binding variable `v`. The result is a theorem `th2`.
- Return the theorem resulting from the transitivity of `th1` and `th2` (`TRANS th1 th2`).

### Mathematical insight
The purpose of `CONV_OF_RCONV` is to provide a way to apply a conversion and then alpha-normalize the result with respect to a binding variable found within the original term. This is useful for ensuring consistent naming of bound variables after applying a conversion, which can simplify further reasoning or comparisons. It essentially combines a generic conversion with an alpha-conversion step.

### Dependencies
- `is_abs`
- `bndvar`
- `is_comb`
- `rand`
- `rator`
- `ONCE_DEPTH_CONV`
- `GEN_ALPHA_CONV`
- `rhs`
- `concl`
- `TRANS`


---

## (CONV_OF_THM:

### Name of formal statement
CONV_OF_THM

### Type of the formal statement
New Definition

### Formal Content
```ocaml
let (CONV_OF_THM: thm -> conv) =
  CONV_OF_RCONV o REWR_CONV;;
```

### Informal statement
The function `CONV_OF_THM` is defined to be a function that takes a theorem `thm` as input and returns a conversion. The conversion returned is the composition of `CONV_OF_RCONV` and `REWR_CONV`. That is, given a theorem `thm`, first apply `REWR_CONV` to `thm`, and then apply `CONV_OF_RCONV` to the resulting rewriter.

### Informal sketch
- The definition of `CONV_OF_THM` simply composes two existing functions: `REWR_CONV` and `CONV_OF_RCONV`.
- `REWR_CONV` converts a theorem to a rewriter.
- `CONV_OF_RCONV` converts a rewriter to a conversion.
- In effect: applying `CONV_OF_THM` to a theorem `t` means creating a rewriter from `t` using `REWR_CONV`, and subsequently lifting that rewriter to a conversion using `CONV_OF_RCONV`.

### Mathematical insight
This definition provides a mechanism to automatically derive a conversion from a given theorem. Theorems expressing equalities are often useful for rewriting, and rewriting can be lifted to conversions, which are the basic building blocks of equational reasoning in HOL Light. The conversion returned by `CONV_OF_THM` will perform rewriting based on the equational theorem passed as input. This is a standard technique for building conversions in HOL Light.

### Dependencies
- `CONV_OF_RCONV`
- `REWR_CONV`

### Porting notes (optional)
The key to porting this definition is to understand how rewriting and conversions are represented in the target proof assistant. Ensure that you have functions for creating rewriters from theorems, and for lifting rewriters to conversions. The function composition operator (`o`) may have a different syntax (e.g., `.` in Coq).


---

## (X_FUN_EQ_CONV:term->conv)

### Name of formal statement
`X_FUN_EQ_CONV`

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let (X_FUN_EQ_CONV:term->conv) =
  fun v -> (REWR_CONV FUN_EQ_THM) THENC GEN_ALPHA_CONV v;;
```

### Informal statement
The conversion `X_FUN_EQ_CONV` maps a term `v` to a conversion that first applies the theorem `FUN_EQ_THM` via rewriting and then applies alpha conversion that generalizes over the variable `v`.

### Informal sketch
- The conversion `X_FUN_EQ_CONV` takes a term `v` as input.
- It first applies the theorem `FUN_EQ_THM` using the `REWR_CONV` conversion. This likely transforms the term based on the equality stated by `FUN_EQ_THM`.
- Then, it applies `GEN_ALPHA_CONV v`, which performs alpha conversion by generalizing the variable `v`. This replaces `v` with a fresh variable to ensure that the equality remains valid after the rewrite.

### Mathematical insight
The conversion `X_FUN_EQ_CONV` is designed to apply `FUN_EQ_THM` in a way that avoids variable capture. After rewriting by equality, it systematically replaces `v` with a fresh variable so that the equality remains valid in the general case. This is a standard step when applying equalities and generalizing results.

### Dependencies
- Theorem: `FUN_EQ_THM`
- Conversion: `REWR_CONV`, `GEN_ALPHA_CONV`


---

## (FUN_EQ_CONV:conv)

### Name of formal statement
FUN_EQ_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let (FUN_EQ_CONV:conv) =
  fun tm ->
    let vars = frees tm in
    let op,[ty1;ty2] = dest_type(type_of (lhs tm)) in
    if op = "fun"
       then let varnm =
                if (is_vartype ty1) then "x" else
                   hd(explode(fst(dest_type ty1))) in
            let x = variant vars (mk_var(varnm,ty1)) in
            X_FUN_EQ_CONV x tm
       else failwith "FUN_EQ_CONV";;
```

### Informal statement
The conversion `FUN_EQ_CONV` takes a term `tm` as input. It checks whether the left-hand side of `tm` is a function type. If the left-hand side has a function type of the form `ty1 -> ty2`, it generates a variable `x` of type `ty1` whose name is "x" if `ty1` is a type variable, and otherwise whose name is derived from the type `ty1`. Here, `x` is chosen to be a variant that does not clash with the free variables in `tm`. Finally, it calls `X_FUN_EQ_CONV` with that variable `x` and the original term `tm`. If the left-hand side of `tm` does not have a function type, the conversion fails.

### Informal sketch
The conversion `FUN_EQ_CONV` attempts to apply `X_FUN_EQ_CONV` to a term, after preparing the arguments for `X_FUN_EQ_CONV`.

- The input term `tm` is examined.
- The free variables `vars` of `tm` are collected to avoid clashes later.
- The type of the left-hand side of `tm` is determined.  If the type has the form `ty1 -> ty2`, then the operator is `"fun"`.
- A suitable variable name `varnm` is deduced based on `ty1`. If `ty1` is a type variable, the name is `"x"`; otherwise, the name is derived from the head of the string representation of `ty1`.
- A variable `x` is constructed with the derived variable name `varnm` and type `ty1`. The variable is a variant, ensuring it doesn't clash with `vars`.
- `X_FUN_EQ_CONV` is called with variable `x` and the term `tm`.

### Mathematical insight
This conversion prepares the ground for beta-reduction of equational theorems involving functions. It effectively introduces a fresh variable of the correct type, which is then used by `X_FUN_EQ_CONV` in the actual beta-reduction process. The purpose is to discharge the equation between functions by specializing it to a fresh variable.

### Dependencies
- `frees`
- `dest_type`
- `type_of`
- `is_vartype`
- `explode`
- `fst`
- `mk_var`
- `variant`
- `X_FUN_EQ_CONV`

### Porting notes (optional)
The `variant` function may require special attention during porting, as it ensures that the introduced variable does not clash with existing free variables. Also `dest_type` can be tricky because dependent type theories have more complex typing rules. Similarly, the string manipulation using `explode` will potentially vary widely depending on the target language.


---

## (SINGLE_DEPTH_CONV:conv->conv)

### Name of formal statement
SINGLE_DEPTH_CONV

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (SINGLE_DEPTH_CONV:conv->conv) =
  let rec SINGLE_DEPTH_CONV conv tm =
    try conv tm with Failure _ ->
    (SUB_CONV (SINGLE_DEPTH_CONV conv) THENC (TRY_CONV conv)) tm in
  SINGLE_DEPTH_CONV;;
```

### Informal statement
The function `SINGLE_DEPTH_CONV` takes a conversion `conv` as input and returns a new conversion. This new conversion, when applied to a term `tm`, attempts to apply `conv` to `tm`. If this application fails, it recursively applies `SINGLE_DEPTH_CONV conv` to all subterms of `tm` and then attempts to apply `conv` to `tm`.

### Informal sketch
The definition of `SINGLE_DEPTH_CONV` is as follows:
- A recursive function is defined that takes a conversion `conv` and a term `tm`.
- The function first attempts to apply the conversion `conv` to the term `tm` directly using `try conv tm with Failure _`.
- If the application of `conv` to `tm` fails:
  - The conversion `SINGLE_DEPTH_CONV conv` is applied to all subterms of `tm` using `SUB_CONV (SINGLE_DEPTH_CONV conv)`.
  - Then, the original conversion `conv` is attempted on `tm` via `TRY_CONV conv)`. This is done because applying the conversion recursively to subterms may have changed `tm` into a term where `conv` now applies.
- The result of either the successful direct application or the combined subterm conversion and final attempt of `conv` becomes the result.

### Mathematical insight
The `SINGLE_DEPTH_CONV` combinator is used to apply a conversion to a term, traversing the term's subterms in a single "depth-first" pass. It first attempts to apply the conversion directly to the term. If that fails, it applies the same conversion recursively to all subterms and tries the original conversion on the original term `tm` again. This is useful when the subterms need to be simplified before the original conversion can be applied. The combinator implements a strategy of applying conversions at different depths within a term, stopping once the conversion succeeds at a given subterm.

### Dependencies
- `SUB_CONV`
- `THENC`
- `TRY_CONV`

### Porting notes (optional)
The `try ... with Failure _` construct might have a different syntax in other proof assistants. Similarly, the handling of conversions and their application might vary. The core logic of recursively traversing the term structure and attempting the conversion at each step should be preserved.


---

## (SKOLEM_CONV:conv)

### Name of formal statement
SKOLEM_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let (SKOLEM_CONV:conv) =
  SINGLE_DEPTH_CONV (REWR_CONV SKOLEM_THM);;
```

### Informal statement
The conversion `SKOLEM_CONV` is defined as a single-depth conversion that applies the theorem `SKOLEM_THM` using a rewriting conversion.

### Informal sketch
- The `SKOLEM_CONV` conversion applies the theorem `SKOLEM_THM` to the subterms of a term at a single level of depth.
- `REWR_CONV SKOLEM_THM` creates a conversion which rewrites the term using the theorem `SKOLEM_THM`.
- `SINGLE_DEPTH_CONV` applies the given conversion to all subterms at one level of depth.

### Mathematical insight
This conversion automates the application of Skolemization rule (expressed via `SKOLEM_THM`) at a subterm within a larger term. It advances a Skolemization within a term by one level. The intent is to automate the process of eliminating existential quantifiers by introducing Skolem functions.

### Dependencies
- Theorem: `SKOLEM_THM`
- Conversionals: `REWR_CONV`, `SINGLE_DEPTH_CONV`


---

## (X_SKOLEM_CONV:term->conv)

### Name of formal statement
`X_SKOLEM_CONV`

### Type of the formal statement
New definition

### Formal Content
```ocaml
let (X_SKOLEM_CONV:term->conv) =
  fun v -> SKOLEM_CONV THENC GEN_ALPHA_CONV v;;
```

### Informal statement
The function `X_SKOLEM_CONV` is defined as a function that takes a term `v` as input and applies the conversion `SKOLEM_CONV` followed by the conversion `GEN_ALPHA_CONV` to `v`.

### Informal sketch
The definition of `X_SKOLEM_CONV` combines two conversions:
- First, it applies `SKOLEM_CONV` to perform Skolemization on the input term `v`.
- Subsequently, it applies `GEN_ALPHA_CONV` to perform generalized alpha conversion on the result.

### Mathematical insight
This definition constructs a combined conversion strategy. Skolemization is used to eliminate existential quantifiers by introducing fresh function symbols and `GEN_ALPHA_CONV` renames bound variables to ensure freshness and simplifies the result

### Dependencies
- `SKOLEM_CONV`
- `GEN_ALPHA_CONV`


---

## EXISTS_UNIQUE_CONV

### Name of formal statement
EXISTS_UNIQUE_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXISTS_UNIQUE_CONV tm =
  let v = bndvar(rand tm) in
  let th1 = REWR_CONV EXISTS_UNIQUE_THM tm in
  let tm1 = rhs(concl th1) in
  let vars = frees tm1 in
  let v = variant vars v in
  let v' = variant (v::vars) v in
  let th2 =
   (LAND_CONV(GEN_ALPHA_CONV v) THENC
    RAND_CONV(BINDER_CONV(GEN_ALPHA_CONV v') THENC
              GEN_ALPHA_CONV v)) tm1 in
  TRANS th1 th2;;
```

### Informal statement
Given a term `tm` of the form `exists! x. P x` (exists unique x such that `P x`), the theorem `EXISTS_UNIQUE_CONV` transforms this term by rewriting it using the theorem `EXISTS_UNIQUE_THM` and then performing alpha conversions to ensure that the existentially quantified variable `v'` in the expanded form `exists x. P x /\ !y. P y ==> y = x` is different from any free variable in `P x`.

### Informal sketch
- Given a term `tm` which is expected to be of the form `exists! x. P x`.
- Rewrite `tm` using the theorem `EXISTS_UNIQUE_THM` which expands `exists! x. P x` to `exists x. P x /\ !y. P y ==> y = x`. Store the resulting theorem as `th1` and extract the right-hand side of its conclusion as `tm1`.
- Determine the free variables `vars` in `tm1`.
- Generate a variable `v` which is a variant of the bound variable of `tm` such that `v` does not appear in `vars`.
- Generate another variable `v'` which is a variant of `v`  such that `v'` does not appear in `v::vars`.
- Apply a series of alpha conversions using `v` and `v'` to `tm1`. Specifically, the alpha conversions are applied to the universally quantified variable `y` within the uniqueness part of the expanded formula obtained in step 2. The overall structure is to alpha-convert the left-hand side of a conjunction with `v`, and then alpha-convert the right-hand side, which involves first alpha-converting the binder `y` to `v'` and then alpha-converting `v`. The resulting theorem is stored as `th2`.
- Finally, combine the theorems `th1` and `th2` using `TRANS` to produce the final result.

### Mathematical insight
This theorem automates the process of rewriting a uniqueness quantifier (`exists!`) into its equivalent definition involving an existence quantifier and a universal quantifier, while also ensuring that the bound variables introduced by the expansion do not clash with any free variables already present in the term. This is crucial for maintaining the validity of logical transformations during automated reasoning.

### Dependencies
- `EXISTS_UNIQUE_THM`
- `GEN_ALPHA_CONV`
- `REWR_CONV`
- `EXISTS_UNIQUE_THM`

### Porting notes (optional)
The main work of porting this is ensuring the alpha conversion and variant finding work correctly. The use of higher-order abstract syntax can obviate the need for explicit renaming.


---

## NOT_FORALL_CONV

### Name of formal statement
NOT_FORALL_CONV

### Type of the formal statement
theorem conversion

### Formal Content
```ocaml
let NOT_FORALL_CONV = CONV_OF_THM NOT_FORALL_THM;;
```
### Informal statement
The theorem conversion `NOT_FORALL_CONV` is a conversion derived from the theorem `NOT_FORALL_THM`.

### Informal sketch
- The conversion `NOT_FORALL_CONV` is constructed directly from the theorem `NOT_FORALL_THM` using the `CONV_OF_THM` function. This function lifts a theorem of the form `|- t = u` to a conversion that maps the term `t` to the theorem `|- t = u`.
- To create this conversion, the theorem `NOT_FORALL_THM` must be available.

### Mathematical insight
The conversion `NOT_FORALL_CONV` provides a way to automatically rewrite instances of the negation of a universal quantification to the corresponding existential quantification of the negation. This is a standard logical equivalence, and having it available as a conversion speeds up proofs by automating this rewrite step.

### Dependencies
- Theorem: `NOT_FORALL_THM`
- Function: `CONV_OF_THM`

### Porting notes (optional)
The key to porting this is to ensure that the corresponding theorem `NOT_FORALL_THM` is available and that the target system has a similar mechanism to create a conversion (rewriting rule) from the theorem. Most proof assistants have a tactic or functionality to achieve this. In Coq, one might use `Ltac` or `rewrite` tactics to create a similar conversion. In Isabelle/HOL, one can use `simp` with the theorem or create a simplification rule. In Lean, `simp` or `rw` can achieve this.


---

## NOT_EXISTS_CONV

### Name of formal statement
NOT_EXISTS_CONV

### Type of the formal statement
theorem conversion

### Formal Content
```ocaml
let NOT_EXISTS_CONV = CONV_OF_THM NOT_EXISTS_THM;;
```
### Informal statement
The theorem conversion `NOT_EXISTS_CONV` maps a theorem of the form `|- !x. ~(p x)` to the theorem `|- ~(?x. p x)`.

### Informal sketch
The conversion `NOT_EXISTS_CONV` is constructed by applying the tactic `CONV_OF_THM` to the theorem `NOT_EXISTS_THM`. Therefore we must first have derived a theorem such as `NOT_EXISTS_THM`, namely `|- !x. ~(p x) <=> ~(?x. p x)`.

*   The conversion then takes a theorem `|- !x. ~(p x)` as input.
*   It uses the theorem `|- !x. ~(p x) <=> ~(?x. p x)` to produce `|- ~(?x. p x)`.

### Mathematical insight
This conversion provides a way to reduce quantified expressions. It converts universal quantification over the negation of a predicate to the negation of an existential quantification over the same predicate. This is a standard logical equivalence, specifically useful in simplifying or transforming logical formulas within the theorem prover.

### Dependencies
*   `NOT_EXISTS_THM`
*   `CONV_OF_THM`

### Porting notes (optional)
The main challenge in porting this will be ensuring that the underlying theorem `NOT_EXISTS_THM` is available or can be proven in the target system. Then, there must be a mechanism to transform a theorem using an equivalence (the general form of `CONV_OF_THM` that derives its conversion from a theorem) which many provers support in some form. One should ensure that the treatment of definitional equality and rewriting is compatible between HOL Light and the target system.


---

## RIGHT_IMP_EXISTS_CONV

### Name of formal statement
RIGHT_IMP_EXISTS_CONV

### Type of the formal statement
theorem conversion

### Formal Content
```ocaml
let RIGHT_IMP_EXISTS_CONV = CONV_OF_THM RIGHT_IMP_EXISTS_THM;;
```
### Informal statement
The theorem `RIGHT_IMP_EXISTS_THM` is converted to a conversion `RIGHT_IMP_EXISTS_CONV`, which means that when applied to a term, it attempts to prove that term is beta-equivalent to the right-hand side of the theorem.

### Informal sketch
- The theorem `RIGHT_IMP_EXISTS_THM` likely has the form `|- !x. (p ==> (?y. q)) = (?y. p ==> q)` where `x` and `y` are variables, `p` and `q` are boolean terms possibly depending on `x` and `y`, and `y` is not free in `p`.
- The conversion `CONV_OF_THM` transforms a theorem `|- t1 = t2` into a conversion that, when applied to `t1`, tries to prove the equality `t1 = t2` by beta-conversion.
- Thus, `RIGHT_IMP_EXISTS_CONV` when applied to a term `t` will attempt to prove `t = (?y. p ==> q)` where `!x. (p ==> (?y. q))` has been matched to `t`.

### Mathematical insight
This conversion is useful for transforming implications with an existential quantifier on the right-hand side into an equivalent form where the existential quantifier is pulled outwards. This transformation is valid only when the quantified variable `y` does not occur free in the left-hand side `p` of the implication. This is a standard logical equivalence that can simplify proofs by restructuring the quantifiers.

### Dependencies
- `RIGHT_IMP_EXISTS_THM`
- `CONV_OF_THM`

### Porting notes (optional)
The conversion `CONV_OF_THM` functionality is common in many proof assistants, although the specific name may vary. It's important to ensure that the theorem `RIGHT_IMP_EXISTS_THM` is ported correctly first, paying attention to the variable binding and potential side conditions on the quantified variable `y`.


---

## FORALL_IMP_CONV

### Name of formal statement
FORALL_IMP_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FORALL_IMP_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_FORALL_IMP_THM ORELSEC
   REWR_CONV RIGHT_FORALL_IMP_THM ORELSEC
   REWR_CONV LEFT_FORALL_IMP_THM);;
```

### Informal statement
The theorem `FORALL_IMP_CONV` is a conversion that, given a term, attempts to rewrite it using one of the following theorems (in order): `TRIV_FORALL_IMP_THM`, `RIGHT_FORALL_IMP_THM`, or `LEFT_FORALL_IMP_THM`. The rewriting continues until one of the rewrites applies.

### Informal sketch
- The conversion `FORALL_IMP_CONV` applies a sequence of rewriting passes using the theorems `TRIV_FORALL_IMP_THM`, `RIGHT_FORALL_IMP_THM`, and `LEFT_FORALL_IMP_THM`.
- The `ORELSEC` combinator attempts the first conversion, and if that fails, attempts the second, and so on.
- The rewriting is done using the `REWR_CONV` which, when applied to a theorem, produces a conversion that attempts to rewrite the term by applying the theorem at the root.
- `CONV_OF_RCONV` lifts a rewriting conversion (operating on terms) to a conversion that applies to theorems.

### Mathematical insight
This conversion provides a convenient way to simplify quantified implications by repeatedly applying standard rewrite rules. This can be used to automatically simplify terms before further reasoning.

### Dependencies
- `TRIV_FORALL_IMP_THM`
- `RIGHT_FORALL_IMP_THM`
- `LEFT_FORALL_IMP_THM`


---

## EXISTS_AND_CONV

### Name of formal statement
EXISTS_AND_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EXISTS_AND_CONV = CONV_OF_RCONV
  (REWR_CONV TRIV_EXISTS_AND_THM ORELSEC
   REWR_CONV LEFT_EXISTS_AND_THM ORELSEC
   REWR_CONV RIGHT_EXISTS_AND_THM);;
```

### Informal statement
The theorem `EXISTS_AND_CONV` is a conversion that, given a term, attempts to rewrite it. The rewriting first tries to apply the conversion derived from the theorem `TRIV_EXISTS_AND_THM`. If that fails, it tries the conversion derived from the theorem `LEFT_EXISTS_AND_THM`. If that also fails, it tries the conversion derived from the theorem `RIGHT_EXISTS_AND_THM`.

### Informal sketch
The conversion `EXISTS_AND_CONV` attempts to simplify a term by applying one of three rewrite rules in sequence:
- It first tries rewriting using `TRIV_EXISTS_AND_THM`, which likely deals with trivial cases of existential quantification and conjunction, such as `?x. T /\ P(x)` being simplified to `?x. P(x)`.
- If that fails, it tries rewriting using `LEFT_EXISTS_AND_THM`, which likely handles cases where the left-hand side of a conjunction within an existential quantifier can be simplified, such as `?x. (x = a) /\ P(x)` being simplified to `P(a)`.
- If that also fails, it tries rewriting using `RIGHT_EXISTS_AND_THM`, which likely handles cases where the right-hand side of a conjunction within an existential quantifier can be simplified, such as `?x. P(x) /\ (x = a)` being simplified to `P(a)`.

Each of the theorems are converted into a rewriter using `REWR_CONV`. `ORELSEC` is an operator that attempts the first conversion and, if it fails, attempts the second. `CONV_OF_RCONV` lifts a rewritting conversion into a full conversion.

### Mathematical insight
This theorem provides a conversion that simplifies terms involving existential quantifiers and conjunctions, by applying a series of rewrite rules that handle common simplification patterns. This is useful for automating the simplification of logical formulas.

### Dependencies
- `TRIV_EXISTS_AND_THM`
- `LEFT_EXISTS_AND_THM`
- `RIGHT_EXISTS_AND_THM`
- `CONV_OF_RCONV`
- `REWR_CONV`
- `ORELSEC`


---

## LEFT_IMP_EXISTS_CONV

### Name of formal statement
LEFT_IMP_EXISTS_CONV

### Type of the formal statement
Theorem conversion

### Formal Content
```ocaml
let LEFT_IMP_EXISTS_CONV = CONV_OF_THM LEFT_IMP_EXISTS_THM;;
```
### Informal statement
The theorem conversion `LEFT_IMP_EXISTS_CONV` converts a term of the form `(!x. p x) ==> t` to `!x. (p x) ==> t`.

### Informal sketch
The conversion `LEFT_IMP_EXISTS_CONV` is derived directly from the theorem `LEFT_IMP_EXISTS_THM` by transforming the theorem into a conversion. Hence, the HOL Light implementation is just `CONV_OF_THM LEFT_IMP_EXISTS_THM`. The proof of `LEFT_IMP_EXISTS_THM` likely involves the following:

- Start with `(!x. p x) ==> t`.
- Introduce the universal quantifier to obtain `!x. (!x. p x) ==> t` where the inner quantifier is over `x`.
- Simplify to `!x. (p x) ==> t` by eliminating the vacuous quantifier `!x`. This step is justified because `x` is not free in `t`.

### Mathematical insight
The `LEFT_IMP_EXISTS_CONV` conversion simplifies expressions where a universally quantified statement on the left side of an implication can have its scope adjusted to include the entire implication. If `x` does not occur free in `t`, then `(!x. p x) ==> t` is equivalent to `!x. (p x ==> t)`. This is useful for rewriting formulas into a standardized format in automated reasoning.

### Dependencies
Theorems:
- `LEFT_IMP_EXISTS_THM`


---

## LEFT_AND_EXISTS_CONV

### Name of formal statement
LEFT_AND_EXISTS_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let LEFT_AND_EXISTS_CONV tm =
  let v = bndvar(rand(rand(rator tm))) in
  (REWR_CONV LEFT_AND_EXISTS_THM THENC TRY_CONV (GEN_ALPHA_CONV v)) tm;;
```

### Informal statement
The conversion `LEFT_AND_EXISTS_CONV` takes a term `tm` and applies the theorem `LEFT_AND_EXISTS_THM` to it. If this application is successful, it then attempts to apply a generic alpha conversion (`GEN_ALPHA_CONV`) where the variable to be alpha-converted, `v`, is obtained by extracting the bound variable from the term resulting from taking the operand (`rand`) of the operand (`rand`) of the operator (`rator`) of `tm`.

### Informal sketch
The conversion `LEFT_AND_EXISTS_CONV` aims to apply the theorem `LEFT_AND_EXISTS_THM` which likely deals with moving an existential quantifier to the left of a conjunction. After applying this rewriting, the conversion attempts to rename the bound variable using `GEN_ALPHA_CONV` to avoid variable capture or for standardization.
- It extracts the variable of the existential quantifier by selecting the bound variable of the right hand side of an assumed and-exists structure (e.g., `!x. p x /\ ?x. q x`)
- It uses `REWR_CONV LEFT_AND_EXISTS_THM` to apply the relevant rewriting theorem in the conversion.
- It uses `TRY_CONV (GEN_ALPHA_CONV v)` on the term to perform alpha conversion on the variable `v` if possible. The `TRY_CONV` ensures the alpha conversion does not throw an error if the alpha conversion cannot proceed.

### Mathematical insight
This conversion is designed to simplify or normalize formulas where an existential quantifier appears inside a conjunction. Moving the quantifier to the left and then alpha-renaming the bound variable can be a useful step in automated reasoning or proof simplification.

### Dependencies
- `LEFT_AND_EXISTS_THM`
- `REWR_CONV`
- `GEN_ALPHA_CONV`
- `rator`
- `rand`
- `bndvar`

### Porting notes (optional)
The key to porting this conversion lies in understanding how HOL Light represents and manipulates terms. The extraction of the variable `v` might require adjustments depending on the term representation in the target proof assistant. Also, the `TRY_CONV` tactic needs to be emulated. Lean has `try`, Coq has `try`, Isabelle has `(...)?`.


---

## RIGHT_AND_EXISTS_CONV

### Name of formal statement
`RIGHT_AND_EXISTS_CONV`

### Type of the formal statement
Theorem conversion

### Formal Content
```ocaml
let RIGHT_AND_EXISTS_CONV =
  CONV_OF_THM RIGHT_AND_EXISTS_THM;;
```
### Informal statement
The theorem conversion `RIGHT_AND_EXISTS_CONV` converts a term of the form `t /\ (?x. u[x])` to `(?x. t /\ u[x])` (where `t` does not depend on `x`), provided `t` is of boolean type.

### Informal sketch
- The conversion `RIGHT_AND_EXISTS_CONV` is derived from the theorem `RIGHT_AND_EXISTS_THM`.
- The theorem `RIGHT_AND_EXISTS_THM` proves the logical equivalence `t /\ (?x. u[x]) <=> (?x. t /\ u[x])` given that the term `t` does not contain free occurrences of the variable `x`.
- The conversion applies this theorem to rewrite occurrences of the left-hand side (`t /\ (?x. u[x])`) to the right-hand side (`(?x. t /\ u[x])`).

### Mathematical insight
This conversion is useful for moving a term that is independent of the quantified variable inside the scope of the existential quantifier. This can simplify proofs or enable further rewriting.

### Dependencies
- `RIGHT_AND_EXISTS_THM`
- `CONV_OF_THM`


---

## AND_FORALL_CONV

### Name of formal statement
AND_FORALL_CONV

### Type of the formal statement
Theorem conversion

### Formal Content
```ocaml
let AND_FORALL_CONV = CONV_OF_THM AND_FORALL_THM;;
```
### Informal statement
The theorem conversion `AND_FORALL_CONV` is a conversion derived from the theorem `AND_FORALL_THM`.

### Informal sketch
The theorem conversion `AND_FORALL_CONV` is constructed directly from the theorem `AND_FORALL_THM` via `CONV_OF_THM`. This conversion reduces terms matching the left-hand side of `AND_FORALL_THM` to the corresponding right-hand side.
The steps involves:
- Obtain the theorem `AND_FORALL_THM`, which presumably is of the form `|- !x. (p /\ q) = (!x. p) /\ (!x. q)` under some conditions (e.g., `x` not free in `p`).
- Apply `CONV_OF_THM` to `AND_FORALL_THM` to create a conversion `c`.
- The conversion `c` will then, when applied to a term of the form `!x. (p /\ q)`, attempt to rewrite it to `(!x. p) /\ (!x. q)` using the theorem `AND_FORALL_THM`.

### Mathematical insight
This conversion allows the distribution of a universal quantifier over a conjunction under appropriate conditions, simplifying logical expressions. It is a standard and useful tool for automated reasoning within logical systems. The conditions under which the distribution is valid (e.g., x not free in p) are captured within the theorem `AND_FORALL_THM`, and therefore automatically checked by the conversion.

### Dependencies
- `AND_FORALL_THM`
- `CONV_OF_THM`


---

## AND1_THM

### Name of formal statement
AND1_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AND1_THM = TAUT `!t1 t2. t1 /\ t2 ==> t1`;;
```

### Informal statement
For all boolean values `t1` and `t2`, if `t1` and `t2` are both true, then `t1` is true.

### Informal sketch
The theorem `AND1_THM` is a tautology stating a basic property of logical conjunction. The proof is a decision procedure for propositional logic, which can automatically prove theorems of this kind by evaluating all possible truth assignments. The core idea is to show that the implication `t1 /\ t2 ==> t1` holds true regardless of whether `t1` and `t2` are true or false and relies on the definition of logical conjunction (`/\`) and implication (`==>`). Tautologies are typically proved by complete case analysis over the free boolean variables, which is automated by the `TAUT` tactic.

### Mathematical insight
This theorem captures the fundamental property that if two statements are both true, then the first statement must also be true. It is an essential rule of inference in propositional logic and a cornerstone for constructing more complex proofs. It is a basic lemma, and it is used in many other proofs.

### Dependencies
None


---

## AND2_THM

### Name of formal statement
AND2_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AND2_THM = TAUT `!t1 t2. t1 /\ t2 ==> t2`;;
```

### Informal statement
For all boolean terms `t1` and `t2`, if `t1` and `t2` are both true, then `t2` is true.

### Informal sketch
This theorem is proven by using the tactic `TAUT`, which automatically proves propositional tautologies.

### Mathematical insight
This theorem states a fundamental property of logical conjunction: if a conjunction of two statements is true, then each of the individual statements must be true. In particular, this demonstrates that `t2` is a logical consequence of `t1 /\ t2`.

### Dependencies
- `TAUT` tactic (for automatic tautology proving)

### Porting notes (optional)
Most proof assistants have built-in tactics or decision procedures to prove propositional tautologies automatically. In systems lacking such automation, a manual proof through introduction and elimination rules for conjunction and implication would be straightforward.


---

## AND_IMP_INTRO

### Name of formal statement
AND_IMP_INTRO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AND_IMP_INTRO = TAUT `!t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`;;
```
### Informal statement
For all boolean terms `t1`, `t2`, and `t3`, `t1` implies `t2` implies `t3` is equivalent to (`t1` and `t2`) implies `t3`.

### Informal sketch
The theorem `AND_IMP_INTRO` is a tautology that relates iterated implication to conjunction and implication. The proof involves standard tautology checking by evaluating the boolean expression for all possible values of its constituent boolean variables. This can be automated, but may be conceptually broken into cases:
- Assume `t1` is true
- Assume `t1` is false
- Within the `t1` is true case:
    - Assume `t2` is true
    - Assume `t2` is false

The goal is to show that `t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3` holds in all cases

### Mathematical insight
This theorem provides a fundamental equivalence that is useful for manipulating logical expressions. Specifically, it allows one to convert between curried implications and implications from a conjunction. This is a very common operation when reasoning about assumptions in a logical argument.

### Dependencies
None

### Porting notes (optional)
This theorem relies on boolean tautology checking, which most proof assistants provide. The main challenge in porting would be differences in the automation level of the tautology checker. In proof assistants with limited automation, a more manual proof might be needed.


---

## AND_INTRO_THM

### Name of formal statement
AND_INTRO_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AND_INTRO_THM = TAUT `!t1 t2. t1 ==> t2 ==> t1 /\ t2`;;
```
### Informal statement
For all boolean terms `t1` and `t2`, if `t1` is true and `t2` is true, then the conjunction `t1 /\ t2` is true.

### Informal sketch
The theorem `AND_INTRO_THM` is a tautology, so its proof typically involves establishing its truth using truth tables or similar methods that demonstrate its validity across all possible assignments of boolean values to the variables `t1` and `t2`. The proof proceeds directly by verifying that for any boolean values assigned to `t1` and `t2`, if both `t1` and `t2` are true, then `t1 /\ t2` is also true based on the definition of conjunction. In HOL Light, the `TAUT` tactic likely automates this process.

### Mathematical insight
This theorem formalizes a basic introduction rule for conjunction in propositional logic. It asserts that if we have proofs of both `t1` and `t2`, then we can deduce `t1 /\ t2`. This is a fundamental principle of logic and underlies many logical arguments and proofs. It's a core concept in building more complex logical systems.

### Dependencies
None

### Porting notes (optional)
This theorem should be straightforward to prove in most proof assistants, as it directly follows from the definition of conjunction. Many systems will have automated tactics (e.g., `tauto` in Coq, `simp` in Isabelle) that can prove it directly. The primary consideration is ensuring that the underlying definition of conjunction is compatible.


---

## BOOL_EQ_DISTINCT

### Name of formal statement
BOOL_EQ_DISTINCT

### Type of the formal statement
Theorem

### Formal Content
```ocaml
TAUT `~(T <=> F) /\ ~(F <=> T)`
```

### Informal statement
The theorem states that it is true that `T` is not equivalent to `F`, and `F` is not equivalent to `T`.

### Informal sketch
The proof involves evaluating the boolean equivalences `T <=> F` and `F <=> T`.
- First, the equivalence `T <=> F` reduces to `F`.
- Then, the equivalence `F <=> T` also reduces to `F`.
- Consequently, `~(T <=> F)` becomes `~F`, which is `T`.
- `~(F <=> T)` becomes `~F`, which is `T`.
- Finally, `T /\ T` simplifies to `T`, proving the tautology.

### Mathematical insight
This theorem captures the fundamental distinction between the boolean truth values `T` (true) and `F` (false). It asserts that they are logically distinct; that is, neither implies the other, and they are not logically interchangeable.

### Dependencies
None

### Porting notes (optional)
This theorem is straightforward to prove in most proof assistants, as it only relies on basic boolean logic. The taut tactic in HOL Light automatically proves this theorem by evaluating the boolean expressions. In other proof assistants, one may need to explicitly apply rules for boolean equivalence and negation.


---

## EQ_EXPAND

### Name of formal statement
`EQ_EXPAND`

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EQ_EXPAND = TAUT `!t1 t2. (t1 <=> t2) <=> t1 /\ t2 \/ ~t1 /\ ~t2`;;
```

### Informal statement
For all boolean terms `t1` and `t2`, the equivalence `t1 <=> t2` holds if and only if either both `t1` and `t2` are true, or both `t1` and `t2` are false.

### Informal sketch
- The theorem is a tautology that establishes the equivalence between the logical equivalence operator (`<=>`) and its definition in terms of conjunction (`/\`), disjunction (`\/`), and negation (`~`).
- The proof demonstrates that `(t1 <=> t2)` is equivalent to `(t1 /\ t2) \/ (~t1 /\ ~t2)` for all boolean terms `t1` and `t2`. Since it is a tautology (true for all possible values of `t1` and `t2`), the HOL Light tactic `TAUT` suffices as a proof. `TAUT` automatically proves theorems that are propositional tautologies.

### Mathematical insight
This theorem clarifies the meaning of logical equivalence. It is fundamental for reasoning about logical statements by allowing the equivalence operator to be expanded into a more basic form composed of conjunction, disjunction, and negation. This expansion is particularly useful in situations where definitions or theorems need to be manipulated at a low level or translated into a different logical framework.

### Dependencies
None

### Porting notes (optional)
In other proof assistants, this theorem is likely to be proven automatically by a tautology checker or can be easily proven by expanding the definition of `<=>` and applying propositional reasoning tactics. The main consideration is ensuring that the target system has the standard boolean connectives available and that the user is aware of automatic tautology-proving tactics, if they exist in the target system.


---

## EQ_IMP_THM

### Name of formal statement
EQ_IMP_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EQ_IMP_THM = TAUT `!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)`;;
```

### Informal statement
For all boolean terms `t1` and `t2`, `t1` is equivalent to `t2` if and only if `t1` implies `t2` and `t2` implies `t1`.

### Informal sketch
*   The proof uses the tautology checker (`TAUT`) to establish the equivalence directly. This involves converting the statement into conjunctive normal form and checking if every clause contains a complementary pair of literals.
*   The statement `!t1 t2. (t1 <=> t2) <=> (t1 ==> t2) /\ (t2 ==> t1)` is a tautology because the equivalence of two boolean terms is defined as their mutual implication.

### Mathematical insight
The theorem `EQ_IMP_THM` expresses the fundamental relationship between logical equivalence and implication. It clarifies that two statements are equivalent precisely when each implies the other. This theorem is crucial for reasoning about logical equivalence and is used extensively in simplifying and transforming logical formulas.

### Dependencies
None

### Porting notes (optional)
This theorem is a standard result in propositional logic and should be directly available or easily provable in most proof assistants. No special tactics are required outside of propositional reasoning.


---

## FALSITY

### Name of formal statement
FALSITY

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let FALSITY = TAUT `!t. F ==> t`;;
```

### Informal statement
The constant `FALSITY` is defined as the tautology asserting that for all propositions `t`, the proposition `F` implies `t`.

### Informal sketch
- The definition introduces `FALSITY` as a term equivalent to a specific tautology.
- The tautology states that `F` (`False`) implies every proposition `t`.
- This reflects the principle of explosion or ex falso quodlibet.

### Mathematical insight
This definition captures the fundamental property of falsehood in classical logic: from a false premise, any conclusion can be derived. `FALSITY` represents this logical principle. It's a crucial definition in building consistent logical systems, allowing one to reason about and handle contradictions effectively.

### Dependencies
None

### Porting notes (optional)
Most proof assistants have a built-in notion of falsehood (e.g., `False` in Coq/Lean, `False` or `⊥` in Isabelle). The key is to ensure that the defined `FALSITY` satisfies the ex falso quodlibet principle, which might be an axiom, a primitive rule, or derivable from other axioms. In systems with dependent types, this might relate to the empty type.


---

## F_IMP

### Name of formal statement
F_IMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
TAUT `!t. ~t ==> t ==> F`;;
```

### Informal statement
For all boolean `t`, if `t` is false, then if `t` is true, then false.

### Informal sketch
- The theorem `F_IMP` states that `~t ==> t ==> F` is a tautology.
- This is a standard theorem that can be proved by propositional reasoning.
- The proof involves showing that the implication `~t ==> t ==> F` is true for all possible values of `t`.
- When `t` is true, the antecedent `~t` is false, so the implication is true.
- When `t` is false, the antecedent `~t` is true, so `t ==> F` must be shown to be true, which is true since `t` is false and therefore `F` is true.

### Mathematical insight
This theorem embodies a fundamental principle of classical logic: if something is false, then it implies anything; in particular, if `t` is false, then the implication "if `t` then false" holds true. This is often referred to as "ex falso quodlibet" or the principle of explosion. It highlights that from a contradiction, anything can be derived.

### Dependencies
None

### Porting notes (optional)
Most proof assistants have built-in tautology provers or can easily prove this using basic propositional logic tactics. Some systems might require explicitly declaring `t` as a boolean variable.


---

## IMP_DISJ_THM

### Name of formal statement
IMP_DISJ_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IMP_DISJ_THM = TAUT `!t1 t2. t1 ==> t2 <=> ~t1 \/ t2`;;
```

### Informal statement
For all boolean terms `t1` and `t2`, `t1` implies `t2` is equivalent to `not t1` or `t2`.

### Informal sketch
The theorem `IMP_DISJ_THM` expresses the logical equivalence between implication and disjunction. The proof likely involves tautology checking (TAUT tactic in HOL Light). This tactic automatically proves propositional tautologies by exhaustively considering all possible truth assignments to the variables.

### Mathematical insight
This theorem is a fundamental equivalence in propositional logic. It shows that `t1 ==> t2` can be rewritten as `~t1 \/ t2`. It is a standard way to eliminate implication in favor of negation and disjunction, which is useful in many logical arguments and automated reasoning systems.

### Dependencies
None

### Porting notes (optional)
Most proof assistants have built-in support for propositional tautology checking like HOL Light's `TAUT` tactic. Therefore, porting this theorem should be straightforward using the equivalent tactic in other proof assistants.


---

## IMP_F

### Name of formal statement
IMP_F

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IMP_F = TAUT `!t. (t ==> F) ==> ~t`;;
```

### Informal statement
For all boolean values `t`, if `t` implies false, then `t` is false.

### Informal sketch
The theorem `IMP_F` states that if a boolean value `t` implies falsehood (`F`), then `t` must itself be false (`~t`).

*   The proof proceeds by considering the two possible values of `t`: true (`T`) and false (`F`).
*   If `t` is true, then `t ==> F` is equivalent to `T ==> F`, which is `F`. But we are given that `t ==> F` holds, so `t` cannot be true.
*   If `t` is false, then `t ==> F` is equivalent to `F ==> F`, which is `T`. This is consistent with the assumption that `t ==> F` holds, and in this case `~t` is also true.
*   Since `t` must be false in either case, the theorem holds.

### Mathematical insight
This theorem encapsulates a basic principle of classical logic. It is related to *reductio ad absurdum*, where one shows that a proposition is false by demonstrating that it implies a contradiction. Here, the contradiction is the boolean value `F`. Essentially, if assuming `t` leads to a falsehood, then `t` cannot be true.

### Dependencies
None

### Porting notes (optional)
This theorem is a straightforward translation to most proof assistants. The implication operator, `==>`, and the boolean constants `T` and `F` should have standard equivalents. The automation needed to prove the theorem is also very basic, and can be achieved with simple boolean reasoning tactics in most systems (e.g., `auto` in Isabelle, `tauto` in Coq, `simp` in Lean).


---

## IMP_F_EQ_F

### Name of formal statement
IMP_F_EQ_F

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IMP_F_EQ_F = TAUT `!t. t ==> F <=> (t <=> F)`;;
```
### Informal statement
For all boolean `t`, `t` implies false is equivalent to `t` is equivalent to false.

### Informal sketch
- The theorem expresses the equivalence between `t ==> F` and `t <=> F`, where `t` is a boolean term.
- Proof uses `TAUT` to prove this propositional tautology.

### Mathematical insight
- The statement captures the propositional equivalence `t ==> F <=> (t <=> F)`. It essentially states that if `t` implies false, then `t` must be equivalent to false, and vice versa.
- This is a basic fact in propositional logic.

### Dependencies
- `TAUT`


---

## LEFT_AND_OVER_OR

### Name of formal statement
LEFT_AND_OVER_OR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LEFT_AND_OVER_OR = TAUT
  `!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3`;;
```
### Informal statement
For any boolean terms `t1`, `t2`, and `t3`, `t1` and (`t2` or `t3`) is equivalent to (`t1` and `t2`) or (`t1` and `t3`).

### Informal sketch
The proof establishes the theorem using propositional logic tautology checking.
- The theorem states that `t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3` is a tautology.
- It invokes the `TAUT` tactic which automatically proves theorems that can be shown to be true by considering all possible truth assignments to its variables.

### Mathematical insight
This theorem captures the distributivity of conjunction over disjunction in Boolean algebra. It is a fundamental property used in simplifying logical expressions and reasoning about conditional statements.

### Dependencies
None

### Porting notes (optional)
This is a standard property in propositional logic and can be easily proven in any proof assistant that supports Boolean reasoning. The main challenge would be to find an equivalent of the `TAUT` tactic which handles propositional tautologies automatically. If such a tactic is not available, one can resort to a manual proof by case analysis on the truth values of propositional variables or by using rewrite rules implementing boolean algebra identities or simplification procedures.


---

## LEFT_OR_OVER_AND

### Name of formal statement
LEFT_OR_OVER_AND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LEFT_OR_OVER_AND = TAUT
  `!t1 t2 t3. t1 \/ t2 /\ t3 <=> (t1 \/ t2) /\ (t1 \/ t3)`;;
```
### Informal statement
For all boolean terms `t1`, `t2`, and `t3`, `t1` or (`t2` and `t3`) is equivalent to (`t1` or `t2`) and (`t1` or `t3`).

### Informal sketch
- The theorem states the distributivity of disjunction over conjunction for boolean terms.
- The proof relies on showing that `t1 \/ t2 /\ t3` implies `(t1 \/ t2) /\ (t1 \/ t3)` and vice versa.
- The proof proceeds by using tautology checking, which handles all possible boolean assignments to the variables `t1`, `t2`, and `t3`.

### Mathematical insight
This theorem expresses the distributive property of the logical OR operator over the logical AND operator. It's a fundamental property in Boolean algebra and propositional logic. This theorem provides a way to rewrite logical expressions.

### Dependencies
None

### Porting notes (optional)
This theorem should be portable to any proof assistant with boolean logic and tautology checking capabilities. Many systems provide automated tactics that can directly prove this equivalence.


---

## NOT_AND

### Name of formal statement
NOT_AND

### Type of the formal statement
theorem

### Formal Content
```ocaml
TAUT `~(t /\ ~t)`
```

### Informal statement
The proposition that it is a tautology that `~(t /\ ~t)` holds, where `t` is a boolean term.

### Informal sketch
The proof exploits the tautology tactic (`TAUT`). This tactic automatically proves propositional tautologies. The proposition `~(t /\ ~t)` is equivalent to `~t \/ ~~t`, which simplifies to `~t \/ t`, expressing the law of excluded middle, a standard tautology.

### Mathematical insight
This theorem asserts the law of excluded middle in terms of conjunction and negation. It is a fundamental principle of classical logic, stating that for any proposition `t`, either `t` or its negation `~t` must be true.

### Dependencies
None

### Porting notes (optional)
Since the proof relies on a built-in tautology checker, porting to other systems involves either using a similar built-in tactic or explicitly proving the law of excluded middle as `~t \/ t`` and then showing the equivalence of that to `~(t /\ ~t)`.


---

## NOT_F

### Name of formal statement
NOT_F

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_F = TAUT `!t. ~t ==> (t <=> F)`;;
```

### Informal statement
For all `t`, if `t` is false, then `t` is equivalent to `F`.

### Informal sketch
The theorem `NOT_F` states that if a term `t` is false, then it is equivalent to the boolean `F`. The proof involves assuming `~t` and then showing that `t <=> F` holds. Since `t` is assumed to be false, `t <=> F` simplifies to `F <=> F`, which is trivially true. In HOL Light, this is often achieved using tautological reasoning capabilities such as `TAUT`.

### Mathematical insight
The theorem formalizes a very basic property of Boolean logic, connecting negation (`~t`) with logical equivalence (`<=>`) and the constant `F` (false). It is a useful lemma for simplifying other theorems that involve negated terms.

### Dependencies
- `TAUT`

### Porting notes (optional)
This theorem relies on the tautological reasoning capabilities of HOL Light. Most proof assistants have similar built-in support for propositional logic, so porting this theorem should be straightforward. In systems that lack a dedicated tautology checker, one can manually prove the implication using introduction and elimination rules for negation and equivalence.


---

## OR_ELIM_THM

### Name of formal statement
OR_ELIM_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_ELIM_THM = TAUT
  `!t t1 t2. t1 \/ t2 ==> (t1 ==> t) ==> (t2 ==> t) ==> t`;;
```
### Informal statement
For all propositions `t`, `t1`, and `t2`, if `t1` or `t2` is true, and if `t1` implies `t`, and if `t2` implies `t`, then `t` is true.

### Informal sketch
This theorem, the elimination rule for disjunction, is proven tautologically in HOL Light. The outline mirrors a standard proof of disjunction elimination:
- Assume `t1 \/ t2`.
- Assume `t1 ==> t`.
- Assume `t2 ==> t`.
- Conclude `t`.

### Mathematical insight
The theorem `OR_ELIM_THM` is the standard elimination rule for disjunction (∨). It states that if a disjunction `t1 \/ t2` holds, and if from each disjunct we can derive the same conclusion `t`, then we can conclude `t` itself. This theorem is a fundamental inference rule in constructive and classical logic and is essential for reasoning about disjunctive cases.

### Dependencies
- `TAUT`


---

## OR_IMP_THM

### Name of formal statement
OR_IMP_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_IMP_THM = TAUT `!t1 t2. (t1 <=> t2 \/ t1) <=> t2 ==> t1`;;
```
### Informal statement
For all boolean values `t1` and `t2`, `(t1` is equivalent to `t2` or `t1`) is equivalent to (`t2` implies `t1`).

### Informal sketch
The proof demonstrates that `(t1 <=> t2 \/ t1)` is equivalent to `t2 ==> t1`.
- The proof likely proceeds by expanding the equivalence `t1 <=> t2 \/ t1` into `(t1 ==> t2 \/ t1) /\ (t2 \/ t1 ==> t1)`.
- The first conjunct `t1 ==> t2 \/ t1` is likely proven by propositional reasoning. If `t1` is true, then `t2 \/ t1` is clearly true.
- The second conjunct `t2 \/ t1 ==> t1` is equivalent to `~ (t2 \/ t1) \/ t1`, i.e., `(~t2 /\ ~t1) \/ t1` which simplifies to `(~t2 \/ t1) /\ (~t1 \/ t1)` which simplifies to `~t2 \/ t1`, i.e., `t2 ==> t1`.

### Mathematical insight
This theorem captures a basic equivalence in propositional logic. It demonstrates how a bi-implication involving a disjunction can be simplified to a simple implication. Specifically, asserting that `t1` is equivalent to `t2` or `t1` is actually a weaker constraint and only requires `t2` to imply `t1`.

### Dependencies
None

### Porting notes (optional)
This theorem is a straightforward application of propositional logic and should be easily portable to other proof assistants. The main challenge might be in finding the right sequence of tactics or proof steps to match the HOL Light proof. However, generally applicable automated tactics should be able to solve this.


---

## OR_INTRO_THM1

### Name of formal statement
OR_INTRO_THM1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_INTRO_THM1 = TAUT `!t1 t2. t1 ==> t1 \/ t2`;;
```

### Informal statement
For all boolean terms `t1` and `t2`, if `t1` is true, then `t1 \/ t2` is true.

### Informal sketch
The theorem `OR_INTRO_THM1` is a tautology that states if `t1` holds, then `t1 \/ t2` holds, regardless of the truth value of `t2`. The proof likely proceeds directly from the definition of disjunction.

### Mathematical insight
This theorem expresses a fundamental property of logical disjunction. It's a standard introduction rule for the disjunction connective. It formalizes the basic logical fact that if a statement `t1` is true, then the disjunction of `t1` with any other statement `t2` is also true.

### Dependencies
None

### Porting notes (optional)
This should easily port into any standard proof assistant that supports classical logic. The main challenge may be with the automatic tautology prover as HOL Light has a strong one, so other systems may require more manual construction to prove this. However, because it is a basic introduction rule it is often directly available in other systems. The proof should be easily recreatable based on the definition of `\/` (disjunction).


---

## OR_INTRO_THM2

### Name of formal statement
OR_INTRO_THM2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_INTRO_THM2 = TAUT `!t1 t2. t2 ==> t1 \/ t2`;;
```

### Informal statement
For all boolean values `t1` and `t2`, if `t2` is true, then `t1 \/ t2` (the disjunction of `t1` and `t2`) is true

### Informal sketch
The theorem `OR_INTRO_THM2` establishes a basic introduction rule for disjunction. The proof typically proceeds by assuming `t2` is true and then proving that `t1 \/ t2` holds. This is a direct application of the disjunction introduction rule, where the right disjunct is proven directly. One approach would be to start with the assumption `t2` is true and then apply the `DISJ2` tactic or its equivalent resulting directly in `t1 \/ t2`.

### Mathematical insight
This theorem embodies a fundamental principle of classical logic: if one of the disjuncts is true, then the entire disjunction is true. This direction of the introduction rule is crucial for building more complex disjunctive arguments.

### Dependencies
None

### Porting notes (optional)
This theorem is a standard disjunction introduction rule that should be readily available or provable in most proof assistants. The name `OR_INTRO_THM2` suggests there might be another related theorem called `OR_INTRO_THM1` which proves the other introduction rule. In proof assistants that offer automated reasoning tactics (e.g., `auto` in Coq or `simp` in Isabelle), this statement can be easily shown automatically in most cases.


---

## RIGHT_AND_OVER_OR

### Name of formal statement
RIGHT_AND_OVER_OR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIGHT_AND_OVER_OR = TAUT
  `!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1`;;
```
### Informal statement
For all boolean terms `t1`, `t2`, and `t3`, the conjunction of `t2 \/ t3` and `t1` is equivalent to the disjunction of `t2 /\ t1` and `t3 /\ t1`.

### Informal sketch
The theorem `RIGHT_AND_OVER_OR` expresses the right distributivity of conjunction over disjunction. The proof involves showing that `(t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1` is a tautology. This can be established by using the `TAUT` tactic, which automatically proves propositional tautologies in HOL Light. The `TAUT` tactic handles the entire propositional reasoning and verifies the equivalence for all possible truth assignments to `t1`, `t2`, and `t3`.

### Mathematical insight
This theorem is a fundamental property of boolean algebra and propositional logic. It demonstrates how conjunction distributes over disjunction, which is a core principle in simplifying and manipulating logical expressions. The right distributivity is important because it can be used to rewrite logical expressions into equivalent forms, which is useful in theorem proving, program verification, and circuit design.

### Dependencies
- Theorems: `TAUT`


---

## RIGHT_OR_OVER_AND

### Name of formal statement
RIGHT_OR_OVER_AND

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIGHT_OR_OVER_AND = TAUT
  `!t1 t2 t3. t2 /\ t3 \/ t1 <=> (t2 \/ t1) /\ (t3 \/ t1)`;;
```
### Informal statement
For all boolean terms `t1`, `t2`, and `t3`, `(t2 /\ t3) \/ t1` is equivalent to `(t2 \/ t1) /\ (t3 \/ t1)`.

### Informal sketch
The theorem states the distributivity of disjunction over conjunction.
- The proof proceeds by proving the equivalence of `(t2 /\ t3) \/ t1` and `(t2 \/ t1) /\ (t3 \/ t1)` using the tautology tactic `TAUT`.
- `TAUT` automatically proves propositional tautologies, thus handling all the necessary logical transformations.

### Mathematical insight
This theorem expresses the distributivity of the logical OR operator (`\/`) over the logical AND operator (`/\`). This is a fundamental property in propositional logic and Boolean algebra, and is essential for simplifying and manipulating logical expressions.

### Dependencies
- `TAUT`


---

## is_type

### Name of formal statement
is_type

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_type = can get_type_arity;;
```

### Informal statement
The function `is_type` is defined to be the function `can` applied to the function `get_type_arity`.

### Informal sketch
- The function `is_type` is defined by composing two other simpler functions. First, the arity of the type is retrieved using `get_type_arity`. Then, the `can` function checks if that arity retrieval was successful. More specifically, `can` returns `T` if its argument does not raise an exception and `F` if it does. So `is_type` returns `T` if `get_type_arity` does not fail (i.e. the term is of type `:type`) and returns `F` otherwise.

### Mathematical insight
The `is_type` function determines whether a given term represents a type. It leverages `get_type_arity` which will throw an exception if a term is not a type, and the exception handler `can` transforms this exception into a boolean value indicating whether the term is a type. This approach essentially implements a type check. This is an overwrite of a less performant prior definition.

### Dependencies
- Definition: `can`
- Definition: `get_type_arity`


---

## is_constant

### Name of formal statement
is_constant

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let is_constant = can get_const_type;;
```

### Informal statement
The function `is_constant` is defined as the composition of the functions `can` and `get_const_type`.

### Informal sketch
- The definition introduces `is_constant` by composing two existing functions, `can` and `get_const_type`.
- `get_const_type` likely attempts to extract the type of a constant, returning an option type. It returns `NONE` if the provided term is not a constant.
- `can` likely transforms an option type into a boolean. It returns `T` if the input is `SOME x` for some `x`. It returns `F` if the input is `NONE`.
- Therefore, `is_constant t` returns `T` if `t` is a constant, and `F` otherwise.

### Mathematical insight
The function `is_constant` provides a way to check if a given term is a constant value within the formal system. This is a fundamental operation for analyzing and manipulating terms in the logic.

### Dependencies
- `can`
- `get_const_type`


---

## null

### Name of formal statement
null

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let null l = l = [];;
```

### Informal statement
The function `null` applied to a list `l` is defined to be true if and only if `l` is equal to the empty list `[]`.

### Informal sketch
The definition introduces the function `null` which checks whether a given list is empty. The defining equation directly states that `null l` is equivalent to the list `l` being equal to the empty list `[]`.

### Mathematical insight
The `null` function is a fundamental operation on lists, used to determine if a list contains any elements. It is a basic building block for many list-processing algorithms.

### Dependencies
None

### Porting notes (optional)
This definition is straightforward and should be easily portable to other proof assistants. The key is to ensure that the target system has a notion of lists and equality between lists.


---

## type_tyvars

### Name of formal statement
type_tyvars

### Type of the formal statement
Definition

### Formal Content
```ocaml
let type_tyvars = type_vars_in_term o curry mk_var "x";;
```

### Informal statement
The function `type_tyvars` is defined as the composition of the function `type_vars_in_term` with the function that takes a type `ty` and returns the result of applying `mk_var` to the string `"x"` curried to `ty`. In other words, `type_tyvars ty` is equivalent to `type_vars_in_term (mk_var "x" ty)`.

### Informal sketch
- The definition of `type_tyvars` is a direct composition of two functions.
- The first function `curry mk_var "x"` takes a type `ty` and constructs a term of the form `mk_var "x" ty`, which represents a variable named `"x"` of type `ty`.
- The second function `type_vars_in_term` then extracts the type variables present in this term. Therefore, `type_tyvars ty` essentially computes the type variables in the term `mk_var "x" ty`.

### Mathematical insight
This definition provides a way to find the type variables associated with a specific term constructed from a type. The term is created by using the function `mk_var` with the string `"x"` associated with the input type. It's crucial if you have a function extracting free type variables but want to operate on a representation of a type via a term with a specified variable name.

### Dependencies
- `type_vars_in_term`
- `mk_var`
- `curry`


---

## find_match

### Name of formal statement
find_match

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let find_match u =
  let rec find_mt t =
    try term_match [] u t with Failure _ ->
    try find_mt(rator t) with Failure _ ->
    try find_mt(rand  t) with Failure _ ->
    try find_mt(snd(dest_abs t))
    with Failure _ -> failwith "find_match" in
  fun t -> let _,tmin,tyin = find_mt t in
           tmin,tyin;;
```

### Informal statement
The function `find_match` takes a term `u` as input and returns a function that, given a term `t`, attempts to find a subterm of `t` that matches `u`. If a match is found, it returns the matching subterm `tmin` and its type `tyin`. The search for a matching subterm is performed by the recursively defined function `find_mt`. If no match is found within the term `t` or its subterms, the function `find_match` fails. The subterms are explored in the following order: first, the term `t` itself, then the rator of `t`, then the rand of `t`, and finally the body of the abstraction if `t` is an abstraction.

### Informal sketch
The definition introduces a function `find_match` that searches for a match of a given term `u` within another term `t`.

- A recursive function `find_mt` is defined to traverse the term `t`.
- `find_mt` first attempts to match `u` against the current term `t` using `term_match`.
- If the match fails, `find_mt` recursively searches in the rator of `t`.
- If the search in the rator fails, `find_mt` recursively searches in the rand of `t`.
- If the search in the rand fails and if `t` is an abstraction, `find_mt` recursively searches the body of the abstraction. The body is accessed using the `snd` component of `dest_abs t`.
- If all searches fail, the function raises a `Failure` exception.
- The `find_match` function calls `find_mt` and extracts the matching subterm and its type.

### Mathematical insight
The function aims to find a subterm within a larger term that satisfies a given pattern. The search strategy prioritizes the term itself, function part, argument part, and finally the body of abstraction in case the term is a lambda abstraction. The function makes use of the exception handling feature of OCaml to handle failed matches without halting the program.

### Dependencies
- `term_match`
- `rator`
- `rand`
- `dest_abs`

### Porting notes (optional)
When porting this definition, ensure that the target proof assistant provides similar functionality for term matching, term decomposition (rator, rand, dest_abs), and exception handling. The order of search should be preserved to maintain the intended behavior. If exceptions are not directly supported, consider using option types or explicit boolean flags to indicate failure. The `term_match` function may need to be replaced with a suitable pattern matching or unification algorithm. Pay close attention to the representation of lambda abstractions and ensure the ported code correctly extracts the body of the abstraction.


---

## rec

### Name of formal statement
`mk_primed_var`

### Type of the formal statement
New Definition

### Formal Content
```ocaml
let rec mk_primed_var(name,ty) =
  if can get_const_type name then mk_primed_var(name^"'",ty)
  else mk_var(name,ty);;
```

### Informal statement
Define a recursive function `mk_primed_var` taking a variable name `name` (a string) and a type `ty` as input.
If a constant with the given `name` can be found, then `mk_primed_var` calls itself recursively with the name appended with a prime symbol (`'`) and the same type `ty`.
Otherwise, if no constant with the given `name` exists, the function returns a variable with the given `name` and `ty`, created by the function `mk_var`.

### Informal sketch
The definition uses recursion to create a variable name that does not clash with any existing constant names.
- The base case for the recursion is when `can get_const_type name` is false, which means a constant with that name does not exist.
- The recursive step calls `mk_primed_var` with a modified name (`name^"'"`), which appends a prime symbol to the original name.

### Mathematical insight
This function is important for generating fresh variable names, particularly when performing substitutions or other operations that might lead to variable capture. It ensures that the newly created variable does not accidentally shadow an existing constant, avoiding potential logical errors. The use of the prime symbol is a common convention for generating new names.

### Dependencies
- `can get_const_type`
- `mk_var`


---

## subst_occs

### Name of formal statement
`subst_occs`

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let subst_occs =
  let rec subst_occs slist tm =
    let applic,noway = partition (fun (i,(t,x)) -> aconv tm x) slist in
    let sposs = map (fun (l,z) -> let l1,l2 = partition ((=) 1) l in
                                  (l1,z),(l2,z)) applic in
    let racts,rrest = unzip sposs in
    let acts = filter (fun t -> not (fst t = [])) racts in
    let trest = map (fun (n,t) -> (map (C (-) 1) n,t)) rrest in
    let urest = filter (fun t -> not (fst t = [])) trest in
    let tlist = urest @ noway in
      if acts = [] then
      if is_comb tm then
        let l,r = dest_comb tm in
        let l',s' = subst_occs tlist l in
        let r',s'' = subst_occs s' r in
        mk_comb(l',r'),s''
      else if is_abs tm then
        let bv,bod = dest_abs tm in
        let gv = genvar(type_of bv) in
        let nbod = vsubst[gv,bv] bod in
        let tm',s' = subst_occs tlist nbod in
        alpha bv (mk_abs(gv,tm')),s'
      else
        tm,tlist
    else
      let tm' = (fun (n,(t,x)) -> subst[t,x] tm) (hd acts) in
      tm',tlist in
  fun ilist slist tm -> fst(subst_occs (zip ilist slist) tm);;
```

### Informal statement
Define a function `subst_occs` that takes a list of integers `ilist`, a list of pairs `slist` consisting of a term `t` and a variable `x`, and a term `tm` as input. The function `subst_occs` returns a term which is the result of substituting terms for variables in `tm` according to `ilist` and `slist` where `ilist` indicates the occurence number to be substituted. Specifically, calculate `subst_occs (zip ilist slist) tm` whose fst part is the returned term.
The internal recursive function `subst_occs` is defined as follows:
partition `slist` into `applic` and `noway`, where `applic` contains pairs `(i, (t, x))` such that `tm` is alpha-convertible to `x`. `noway` contains the remaining pairs.
From `applic`, construct a list `sposs` of pairs `((l1, z), (l2, z))`, where `l1` is the sublist of `l` (coming from `(i, (t, x))` in `applic` and rearranged into `(l, z)`) consisting of elements equal to 1, and `l2` is the sublist of `l` consisting of the remaining elements from `l`.
Unzip `sposs` into `racts` and `rrest`.
Filter `acts` from `racts` where `acts` contains elements that are not equal to `[]`.
Transform `rrest` into `trest` by decrementing each element in the first component of the pairs by 1.
Filter `urest` from `trest` where `urest` contains elements that are not equal to `[]`.
Concatenate `urest` and `noway` to form `tlist`.
If `acts` is empty, then:
  If `tm` is a combination, decompose it into `l` and `r`. Recursively call `subst_occs` on `tlist` and `l` to get `l'` and `s'`.  Then recursively call `subst_occs` on `s'` and `r` to get `r'` and `s''`. Return the combination of `l'` and `r'`, along with `s''`.
  If `tm` is an abstraction, decompose it into bound variable `bv` and body `bod`. Generate a fresh variable `gv` of the same type as `bv`. Substitute `gv` for `bv` in `bod` to get `nbod`.  Recursively call `subst_occs` on `tlist` and `nbod` to get `tm'` and `s'`. Alpha-convert `bv` to the abstraction of `gv` over `tm'`, and return the result along with `s'`.
  Otherwise, return `tm` and `tlist`.
Otherwise (if `acts` is not empty), let `tm'` be the result of substituting `t` for `x` in `tm` according to the head of `acts` (where the head of `acts` has the form `(n, (t, x))`). Return `tm'` and `tlist`.

### Informal sketch
The definition of `subst_occs` performs term substitution based on a list of occurrences to be substituted.

- The main function `subst_occs ilist slist tm` first zips `ilist` and `slist` to associate occurrence indices with substitutions.
- The recursive helper function processes a term `tm` along with the combined list `slist` of (occurrence index, (term, variable)) entries. The list `slist` represents substitutions to be applied at certain occurrences.
- If the list `acts` of applicable substitutions is empty, the function recurses based on the structure of the term `tm`:
  - If `tm` is an application `l r`, it recursively applies `subst_occs` to `l` and `r`.
  - If `tm` is an abstraction `λx. bod`, it alpha-converts the bound variable to avoid capture, applies `subst_occs` to the body, and then reconstitutes the abstraction.
  - If `tm` is neither, it's a variable or constant, and no substitution is needed.
- If `acts` is not empty, then function applies the head substitution of `acts`, and returns the resulting term.
- Core logic involves maintaining a list of substitutions with occurence indices, filtering to applicable substitutions, applying the substitution, and recursing.
- Renaming of bound variables via alpha conversion uses `vsubst` and `genvar` to avoid variable capture during substitution in abstractions.

### Mathematical insight
The `subst_occs` function is a generalization of standard term substitution that permits controlling exactly which occurrences of a variable are substituted. This capability is important in contexts like formalizing rewrite systems or fine-grained program transformations where one may want to substitute at specific locations, rather than all locations. The occurence information is used to control where beta reduction happens within a large term.

### Dependencies
- `aconv`
- `is_comb`
- `dest_comb`
- `is_abs`
- `dest_abs`
- `genvar`
- `type_of`
- `vsubst`
- `alpha`
- `subst`
- `hd`
- `zip`
- `partition`
- `map`
- `unzip`
- `filter`
- `mk_comb`
- `mk_abs`

### Porting notes (optional)
- The handling of variable renaming via alpha conversion is crucial for correctness and will require consideration in systems like Coq or Lean as HOL Light handles alpha equivalence natively.
- The dependent types of Coq or Lean allows to precisely capture the types by their inhabitants, especially when combined with dependent pattern matching making the expression of `subst_occs` more direct.


---

## INST_TY_TERM(substl,insttyl)

### Name of formal statement
INST_TY_TERM

### Type of the formal statement
Definition

### Formal Content
```ocaml
let INST_TY_TERM(substl,insttyl) th =
  let th' = INST substl (INST_TYPE insttyl th) in
  if hyp th' = hyp th then th'
  else failwith "INST_TY_TERM: Free term and/or type variables in hypotheses";;
```

### Informal statement
Given a substitution list `substl` of terms for term variables, a substitution list `insttyl` of types for type variables, and a theorem `th`, the function `INST_TY_TERM` returns a new theorem `th'` obtained by first instantiating the type variables in `th` using `INST_TYPE insttyl th` and then instantiating the term variables in the result using `INST substl`. The instantiation succeeds only if the hypotheses of the resulting theorem `th'` are identical to the hypotheses of the original theorem `th`; otherwise, it fails.

### Informal sketch
- The function `INST_TY_TERM` takes a list of term substitutions `substl`, a list of type substitutions `insttyl`, and a theorem `th` as input.
- It first performs type instantiation on the theorem `th` using `INST_TYPE insttyl th`, which substitutes type variables in `th` with the corresponding types from `insttyl`.
- It then performs term instantiation on the result using `INST substl`, which substitutes term variables with terms.
- The hypotheses of the resulting theorem `th'` are compared with the hypotheses of the original theorem `th`.
- If the hypotheses are equal, the new theorem `th'` is returned.
- Otherwise, the function raises an exception, indicating that the instantiation introduced free term or type variables into the hypotheses.

### Mathematical insight
The purpose of `INST_TY_TERM` is to perform instantiation of both type and term variables in a theorem while ensuring that the instantiation does not introduce any free variables into the hypotheses. This is crucial for maintaining the validity of the theorem after instantiation, as free variables in hypotheses would change the meaning of the theorem. The check `hyp th' = hyp th` ensures that the hypotheses remain unchanged, guaranteeing that no free variables were introduced during the instantiation process.
This function combines type and term instantiation which are fundamental operations in theorem proving and are used to derive new theorems from existing ones.

### Dependencies
- `INST`
- `INST_TYPE`
- `hyp`

### Porting notes (optional)
- In other proof assistants, the `INST` and `INST_TYPE` functions would correspond to appropriate term and type instantiation functions. 
- The check to ensure hypotheses remain unchanged is important and needs to be enforced in the target proof assistant. This check ensures that the instantiation process does not invalidate the theorem by introducing free variables in the hypotheses.
- The error handling mechanism (`failwith`) should be translated to the corresponding exception handling mechanism in the target proof assistant.


---

## RIGHT_CONV_RULE

### Name of formal statement
RIGHT_CONV_RULE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RIGHT_CONV_RULE (conv:conv) th =
  TRANS th (conv(rhs(concl th)));;
```

### Informal statement
Given a conversion `conv` and a theorem `th`, the theorem `RIGHT_CONV_RULE conv th` is the theorem obtained by applying the conversion `conv` to the right-hand side of the conclusion of the theorem `th` and then transitively composing the original theorem `th` with the resulting converted term.

### Informal sketch
- Given a theorem `th` of the form `|- t = u`.
- Apply the conversion `conv` to `u`, obtaining a theorem `|- u = v`.
- Use the `TRANS` tactic to combine `|- t = u` and `|- u = v` to obtain `|- t = v`.

### Mathematical insight
This theorem provides a way to apply a conversion to the right-hand side of an equational theorem and obtain a new theorem with the converted right-hand side. It uses transitivity of equality. Applying conversions to subterms is a fundamental operation in rewriting and simplification.

### Dependencies
- `TRANS`
- `conv`
- `rhs`
- `concl`

### Porting notes (optional)
The `conv` type in HOL Light represents a function that takes a term and returns a theorem asserting the equality of that term with its converted form (i.e., `conv : term -> thm`). The `TRANS` theorem is the transitivity of equality. Other proof assistants might have different ways of representing conversions and rewriting, so the exact formulation might need adaptation. You might need to explicitly introduce the transitivity lemma and apply it.


---

## NOT_EQ_SYM

### Name of formal statement
NOT_EQ_SYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_EQ_SYM =
  let pth = GENL [`a:A`; `b:A`]
    (GEN_REWRITE_RULE I [GSYM CONTRAPOS_THM] (DISCH_ALL(SYM(ASSUME`a:A = b`))))
  and aty = `:A` in
  fun th -> try let l,r = dest_eq(dest_neg(concl th)) in
                MP (SPECL [r; l] (INST_TYPE [type_of l,aty] pth)) th
            with Failure _ -> failwith "NOT_EQ_SYM";;
```

### Informal statement
For any proposition `th` of the form `¬(l = r)`, it can be inferred that `¬(r = l)`.

### Informal sketch
- The theorem `NOT_EQ_SYM` proves that inequality is symmetric.
- A local theorem `pth` is constructed which rewrites `a = b` to `¬(b = a)` given `¬(a = b)`.  This relies on `CONTRAPOS_THM` which states `(p ==> q) ==> (~q ==> ~p)` and `GSYM` which states `(p ==> q) ==> (q ==> p)`. `DISCH_ALL` discharges all assumptions. `SYM` swaps sides of the equality. `ASSUME` creates an assumption.
- The main function takes a theorem `th` of the form `¬(l = r)`.
- The conclusion of `th` is destructed to extract the left-hand side `l` and right-hand side `r` of the negated equality.
- The local theorem `pth` is instantiated with `r` and `l` and the type of `l` to obtain `¬(r = l)` follows from `¬(l = r)`.
- Modus ponens (`MP`) is then applied to derive `¬(r = l)`.

### Mathematical insight
The theorem `NOT_EQ_SYM` formalizes the intuition that if `a` is not equal to `b`, then `b` is not equal to `a`. This is a fundamental property of inequality.

### Dependencies
- `CONTRAPOS_THM`
- `GSYM`

### Porting notes (optional)
The core of the proof relies on contraposition and symmetry of equality. Most proof assistants have built-in rules or tactics for these, so the porting should be straightforward. The instantiation of the local theorem `pth` with types and terms might require adapting to the specific syntax of the target proof assistant.


---

## NOT_MP

### Name of formal statement
NOT_MP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let NOT_MP thi th =
  try MP thi th with Failure _ ->
  try let t = dest_neg (concl thi) in
      MP(MP (SPEC t F_IMP) thi) th
  with Failure _ -> failwith "NOT_MP";;
```

### Informal statement
Given theorems `thi` and `th`, attempt to apply Modus Ponens (`MP`) to `thi` and `th`; if that fails, attempt to negate the conclusion of `thi`, and if the conclusion of `thi` is of the form `~t`, then apply Modus Ponens to `SPEC t F_IMP` and `thi`, and then apply Modus Ponens to the result and `th`; if that fails, the entire process fails.

### Informal sketch
The function `NOT_MP` attempts to apply Modus Ponens (`MP`) in a specific way that handles negated hypotheses.

- First, it tries the standard `MP thi th`.
- If that fails, it tries to decompose the conclusion of the first theorem `thi` as a negation `~t`:
  - If successful, instantiate `SPEC t F_IMP` (which represents `!t. F => t`) and apply `MP` twice. Think of this as converting `F => t` to `~t` using the instantiation of `SPEC`
  - The first application is between `SPEC t F_IMP` and `thi`
  - The second application is between the result of the previous application and `th`
- If both attempts fail, then the tactic fails.

### Mathematical insight
This function implements a derived inference rule. It attempts to apply Modus Ponens directly, but if that fails, it tries to apply it indirectly by first instantiating the negation of the hypothesis (if the hypothesis is a negation). This allows the proof to proceed even when the hypothesis is in a negated form. It effectively handles cases where one needs to infer `t` from `~t ==> th` and `th`, via `F ==> t`.

### Dependencies
- `MP`
- `dest_neg`
- `SPEC`
- `F_IMP`


---

## FORALL_EQ

### Name of formal statement
`FORALL_EQ`

### Type of the formal statement
Function Definition

### Formal Content
```ocaml
let FORALL_EQ x =
  let mkall = AP_TERM (mk_const("!",[type_of x,mk_vartype "A"])) in
  fun th -> try mkall (ABS x th)
            with Failure _ -> failwith "FORALL_EQ";;
```

### Informal statement
Define a function `FORALL_EQ` that takes a term `x` as input and returns a function that attempts to create a universal quantification over `x` applied to a theorem. Specifically, given a term `x` and a theorem `th`, the function attempts to construct the term `!x. th`, where `!` is the universal quantifier. If the construction succeeds, it returns the term; otherwise, it fails with the string "FORALL_EQ".

### Informal sketch
- The definition constructs a function `FORALL_EQ` which, when given a term `x`, returns a function that maps a theorem `th` to a new term representing the universal quantification of `th` with respect to `x`.
- The term representing the universal quantifier `!` is constructed based on the type of `x` and a type variable `"A"`.
- It attempts to create the abstraction `ABS x th`, representing the body of the universal quantification and then apply the universal quantifier `!` to generate the term `!x. th`.
- A `try...with` block handles potential failures during term construction; specifically, it fails if `ABS x th` leads to a failure.

### Mathematical insight
The function `FORALL_EQ` attempts to lift the universal quantifier from the term level to the theorem level of HOL Light by constructing the universally quantified term and signalling failure if that construction proves impossible. This failure might arise if term `x` is not free in theorem (i.e. hypothesis) `th`.

### Dependencies
- `AP_TERM`
- `mk_const`
- `type_of`
- `mk_vartype`
- `ABS`


---

## EXISTS_EQ

### Name of formal statement
EXISTS_EQ

### Type of the formal statement
Definition

### Formal Content
```ocaml
let EXISTS_EQ x =
  let mkex = AP_TERM (mk_const("?",[type_of x,mk_vartype "A"])) in
  fun th -> try mkex (ABS x th)
            with Failure _ -> failwith "EXISTS_EQ";;
```

### Informal statement
Given a term `x` and a theorem `th` whose conclusion is of type boolean, `EXISTS_EQ` attempts to create a new term representing the existential quantification of `x` over the boolean term within `th`. Specifically, it applies the existential quantifier constructor `mkex` (which is the application of the existential quantifier constant "?" to the type of `x` and a type variable "A") to the abstraction of `x` in the conclusion of the theorem `th`. If successful, it returns the resulting term; otherwise if the application of `mkex` to the abstraction fails, it raises an exception "EXISTS_EQ".

### Informal sketch
- The function `EXISTS_EQ` takes a term `x` and a theorem `th` as input.
- An existential quantifier instantiation `mkex` is created, parameterized by the type of `x` and a type variable.
- The function attempts to abstract `x` from the conclusion of `th` using the `ABS` operator (representing lambda abstraction).
- It then applies the existential quantifier constructor `mkex` to the abstraction.
- The `try...with` block handles potential failures during abstraction or application. If these operations succeed, the resulting quantified term is returned. If abstraction or application fails, the function raises a `Failure` exception, specifically "EXISTS_EQ".

### Mathematical insight
The function `EXISTS_EQ` is designed to construct an existential quantification term from a theorem. The theorem `th` essentially proves a statement involving some variable `x`. The function turns this into a term asserting the existence of an `x` satisfying the proven statement. The use of `try...with` allows for handling cases where the provided theorem might not be in a suitable form for direct abstraction and quantification.

### Dependencies
None

### Porting notes (optional)
The use of `AP_TERM` and `mk_const` suggest a specific way of constructing terms in HOL Light. Other proof assistants might have different mechanisms for creating application terms and constants. The handling of exceptions with `try...with` should be portable to other systems, but specifics depend on the target system. Ensuring the proper handling of type variables (A in `mk_vartype "A"`) will also be crucial. Pay close attention to how the target system handles term construction and exception/error management.


---

## SELECT_EQ

### Name of formal statement
SELECT_EQ

### Type of the formal statement
Definition

### Formal Content
```ocaml
let SELECT_EQ x =
  let mksel = AP_TERM (mk_const("@",[type_of x,mk_vartype "A"])) in
  fun th -> try mksel (ABS x th)
            with Failure _ -> failwith "SELECT_EQ";;
```

### Informal statement
The function `SELECT_EQ` takes a term `x` and a theorem `th` as input. It constructs a term `mksel` representing the application of a constant `@` (with type dependent on `x` and a type variable `"A"`). It then attempts to apply `mksel` to the abstraction of `x` in `th` (i.e., `ABS x th`). If this application fails, then the function `SELECT_EQ` fails.

### Informal sketch
The function `SELECT_EQ` tries to create a term representing a selection from an abstracted theorem.

- Given a term `x` and a theorem `th`, the goal is to extract a selection from `th` with respect to `x`.
- The function first constructs `mksel`, which represents an application of the constant `@` with a specific type to allow selection. The types of this constant are the type of `x` and a type variable `A`.
- It then attempts to apply `mksel` to the abstraction of the term `x` within the theorem `th`. That is, it creates the abstraction `ABS x th` and applies the selector `mksel` to it.
- The entire process is wrapped in a `try...with` block so that if the term construction or application fails, the function `SELECT_EQ` will fail.

### Mathematical insight
The function exploits the internal representation of theorems and terms within HOL Light to perform a selection operation. The `'@'` may be used to indicate the selection operator within the logic, though the user does not see its name directly and it is rarely used for its own sake. The construction ensures that if the selection operation cannot be performed (e.g., due to type mismatches or other inconsistencies), the function produces an exception rather than returning an invalid result. This kind of exception control ensures the logical consistency of the system.

### Dependencies
- `AP_TERM`
- `mk_const`
- `type_of`
- `mk_vartype`
- `ABS`
- `Failure`


---

## RIGHT_BETA

### Name of formal statement
RIGHT_BETA

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let RIGHT_BETA th =
  try TRANS th (BETA_CONV(rhs(concl th)))
  with Failure _ -> failwith "RIGHT_BETA";;
```

### Informal statement
Given a theorem `th`, attempt to transform it by transitivity with the beta conversion of the right-hand side of its conclusion. If the transformation fails, then fail with the string "RIGHT_BETA".

### Informal sketch
- The function `RIGHT_BETA` takes a theorem `th` as input.
- It attempts to apply `TRANS` (transitivity) to the input theorem `th` and the result of applying the tactic `BETA_CONV` to the right-hand side (`rhs`) of the conclusion (`concl`) of `th`.
- If the `TRANS` application succeeds, the resulting theorem is returned.
- If the `TRANS` application fails (indicated by a `Failure` exception), the function fails with the string "RIGHT_BETA".

### Mathematical insight
This function aims to simplify a theorem by performing a beta reduction on the right-hand side of its conclusion and then using transitivity to replace the original right-hand side with its beta-reduced form. Beta-reduction is a fundamental simplification rule in lambda calculus and is commonly used to reduce expressions to a normal form. The `TRANS` tactic is used to connect the original theorem with the beta-reduced version of its conclusion's RHS. The potential failure indicates that the beta conversion does not produce a directly compatible term for transitivity.

### Dependencies
-  `TRANS`
-  `BETA_CONV`
-  `rhs`
-  `concl`


---

## rec

### Name of formal statement
rec

### Type of the formal statement
theorem

### Formal Content
```ocaml
let rec LIST_BETA_CONV tm =
  try let rat,rnd = dest_comb tm in
      RIGHT_BETA(AP_THM(LIST_BETA_CONV rat)rnd)
  with Failure _ -> REFL tm;;
```

### Informal statement
Define a recursive function `LIST_BETA_CONV` that acts on a term `tm`. If `tm` is a combination, decompose it into its operator part `rat` and operand part `rnd`. Then apply `LIST_BETA_CONV` recursively to `rat`, obtaining a theorem; combine this theorem with the operand `rnd` using `AP_THM`, and apply `RIGHT_BETA` to the result. If `tm` is not a combination (i.e., the decomposition fails), then return the reflexivity theorem for `tm`.

### Informal sketch
The function `LIST_BETA_CONV` attempts to perform beta reduction on a term and its subterms recursively.

- Base Case: If the term `tm` is not a combination (cannot be decomposed into an operator and operand), then it means no beta reduction is possible at the top level, so the reflexivity theorem `REFL tm` is returned, stating `tm = tm`.
- Recursive Step: If the term `tm` is a combination, it's decomposed into `rat` and `rnd`. The function then recursively applies `LIST_BETA_CONV` to `rat`. This results in a theorem stating that `rat = rat'`, where `rat'` is the beta-reduced form of `rat`.  This theorem `rat = rat'` is then applied to `rnd` via `AP_THM` resulting in the theorem `rat rnd = rat' rnd`. Finally, `RIGHT_BETA` is applied which performs the beta reduction on the right-hand side if possible, resulting in `rat rnd = rat'rnd -> rat rnd = v` where `v` is the beta reduced term.

### Mathematical insight
The function `LIST_BETA_CONV` implements a full beta reduction on a term, reducing all beta-redexes in the term and its subterms until no further reduction is possible. The use of the `try...with` construct combined with recursion allows the function to traverse the term structure and perform beta reductions wherever possible.

### Dependencies
- `dest_comb`
- `RIGHT_BETA`
- `AP_THM`
- `REFL`

### Porting notes (optional)
- Most proof assistants have built-in beta reduction, however the specific function `LIST_BETA_CONV` provides a way to beta-reduce all subterms as well, which can reduce manual labor.
- The try-catch structure can have different syntax in other proof assistants. The HOL Light code relies on exceptions via `Failure _` in order to determine when `dest_comb` fails, which needs to be converted into the corresponding error handling structure in the target proof assistant. For example, some systems return an option type that must be handled explicitly.


---

## RIGHT_LIST_BETA

### Name of formal statement
RIGHT_LIST_BETA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(snd(dest_eq(concl th))));;
```

### Informal statement
Given a theorem `th` whose conclusion is an equality, the theorem `RIGHT_LIST_BETA th` is obtained by transforming `th` using the beta reduction of the right-hand side of the equation which is the conclusion of `th`, where this right hand side is assumed to be a list.

### Informal sketch
- Extract the conclusion of the theorem `th`, which is assumed to be an equality.
- Destruct the equality to obtain its right-hand side, which is assumed to be a list.
- Apply the `LIST_BETA_CONV` conversion to the right-hand side list.
- Transform the original theorem `th` using the conversion `LIST_BETA_CONV` applied to the right-hand side of the equality in the conclusion of `th`.

### Mathematical insight
The theorem `RIGHT_LIST_BETA` provides a way to perform beta reduction specifically on lists that appear on the right-hand side of an equation that is the conclusion of a theorem. Beta reduction simplifies expressions by applying functions to their arguments. This is a specialized beta reduction that applies to lists.

### Dependencies
- `TRANS`
- `LIST_BETA_CONV`
- `dest_eq`
- `concl`
- `snd`


---

## LIST_CONJ

### Name of formal statement
LIST_CONJ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LIST_CONJ = end_itlist CONJ ;;
```

### Informal statement
The function `LIST_CONJ` is defined as the result of applying the function `end_itlist` to the binary function `CONJ`.

### Informal sketch
- `end_itlist` presumably iterates through a list, applying a binary function to accumulate a result. In this case it starts from the end of a list and applies `CONJ` which is the boolean conjunction. Thus the function `LIST_CONJ` is equivalent to taking the boolean conjunction over a list of booleans. For example, `LIST_CONJ [T; T; F]` would reduce to `T AND (T AND F)`, which simplifies to `F`.

### Mathematical insight
The definition captures the standard mathematical idea of conjunction (AND) applied to all elements of a list of booleans. This is a common operation in logic and computer science.

### Dependencies
- `end_itlist`
- `CONJ`

### Porting notes (optional)
Most proof assistants have similar functions for iterating over lists and accumulating a result. Often called `fold`, `foldr`, or reduce. This should be straightforward to port. Pay attention to the order of arguments and the initial value in the fold operation.


---

## rec

### Name of formal statement
`CONJ_LIST`

### Type of the formal statement
New definition

### Formal Content
```ocaml
let rec CONJ_LIST n th =
  try if n=1 then [th] else (CONJUNCT1 th)::(CONJ_LIST (n-1) (CONJUNCT2 th))
  with Failure _ -> failwith "CONJ_LIST";;
```

### Informal statement
Define a recursive function `CONJ_LIST` that takes a natural number `n` and a term `th` as input.
If `n` equals 1, the function returns the list containing only `th`.
Otherwise, the function returns a list whose head is the term `CONJUNCT1 th` and whose tail is the result of recursively calling `CONJ_LIST` with `n-1` and `CONJUNCT2 th`.
If the process encounters a failure, the function raises an exception named `CONJ_LIST`.

### Informal sketch
- The definition of `CONJ_LIST` proceeds by recursion on the natural number `n`.
- Base case: If `n` is 1, the list containing the single term `th` is returned.
- Recursive step: If `n` is greater than 1, the function constructs a list. The head of this list is `CONJUNCT1 th`. The tail of the list is obtained by calling `CONJ_LIST` recursively, with the arguments `n-1` and `CONJUNCT2 th`. Thus, the function deconstructs `th` into two subterms `CONJUNCT1 th` and `CONJUNCT2 th` in each recursive step.
- Error case: If the recursion fails (presumably because the input term `th` does not have the required structure to be split into `CONJUNCT1` and `CONJUNCT2`), the function throws an exception.

### Mathematical insight
The function `CONJ_LIST` is designed to repeatedly decompose a term `th` into its constituent conjuncts, up to a specified number of times `n`. The motivation is to create a list of `n` successive left-hand sides of some logical conjunction, which are obtained by iteratively applying `CONJUNCT1` to `th`, where `CONJUNCT1` and `CONJUNCT2` are functions designed to extract parts of a conjunctive term. If the structure of `th` is not as expected, the construction may fail, resulting in an exception.

### Dependencies
None

### Porting notes (optional)
The `try ... with Failure _ -> failwith` structure should be translated into the equivalent exception handling mechanism within the target proof assistant. The recursive definition style should be supported (or transformed into a fixpoint definition).
Need to make sure that `CONJUNCT1` and `CONJUNCT2` are defined according to the target proof assistant.


---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec BODY_CONJUNCTS th =
  if is_forall(concl th) then
    BODY_CONJUNCTS (SPEC_ALL th) else
  if is_conj (concl th) then
      BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th)
  else [th];;
```

### Informal statement
Define a recursive function `BODY_CONJUNCTS` that takes a theorem `th` as input and returns a list of theorems.
- If the conclusion of `th` is a universal quantification, then recursively call `BODY_CONJUNCTS` with the theorem obtained by specializing the universal quantifier (using `SPEC_ALL`).
- Otherwise, if the conclusion of `th` is a conjunction, then recursively call `BODY_CONJUNCTS` with the theorem obtained by taking the first conjunct (using `CONJUNCT1`) and the theorem obtained by taking the second conjunct (using `CONJUNCT2`), and concatenate the resulting lists.
- Otherwise (if the conclusion is neither a universal quantification nor a conjunction), return a singleton list containing `th`.

### Informal sketch
The function `BODY_CONJUNCTS` traverses a theorem, breaking it down into its constituent non-quantified, non-conjunctive parts.

- The base case is when the conclusion of the theorem is neither a universal quantification nor a conjunction. In this case, the theorem itself is returned as a single-element list.

- If the conclusion is a universally quantified formula, the theorem is specialized using `SPEC_ALL`, and `BODY_CONJUNCTS` is recursively called on the specialized theorem. This effectively strips off universal quantifiers one by one.

- If the conclusion is a conjunction, the theorem is split into its two conjuncts using `CONJUNCT1` and `CONJUNCT2`. `BODY_CONJUNCTS` is recursively called on each conjunct, and the results are concatenated. This effectively splits a conjunction into a list of its individual conjuncts.

### Mathematical insight
The function `BODY_CONJUNCTS` is designed to decompose a theorem into a list of theorems whose conclusions are atomic or negated atomic formulas, after stripping off all outermost universal quantifiers and conjunctions. This is useful for processing theorems in a normal form.

### Dependencies
- `is_forall`
- `concl`
- `SPEC_ALL`
- `is_conj`
- `CONJUNCT1`
- `CONJUNCT2`


---

## rec

### Name of formal statement
`IMP_CANON`

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let rec IMP_CANON th =
    let w = concl th in
    if is_conj w then IMP_CANON (CONJUNCT1 th) @ IMP_CANON (CONJUNCT2 th)
    else if is_imp w then
        let ante,conc = dest_neg_imp w in
        if is_conj ante then
            let a,b = dest_conj ante in
            IMP_CANON
            (DISCH a (DISCH b (NOT_MP th (CONJ (ASSUME a) (ASSUME b)))))
        else if is_disj ante then
            let a,b = dest_disj ante in
            IMP_CANON (DISCH a (NOT_MP th (DISJ1 (ASSUME a) b))) @
            IMP_CANON (DISCH b (NOT_MP th (DISJ2 a (ASSUME b))))
        else if is_exists ante then
            let x,body = dest_exists ante in
            let x' = variant (thm_frees th) x in
            let body' = subst [x',x] body in
            IMP_CANON
            (DISCH body' (NOT_MP th (EXISTS (ante, x') (ASSUME body'))))
        else
        map (DISCH ante) (IMP_CANON (UNDISCH th))
    else if is_forall w then
        IMP_CANON (SPEC_ALL th)
    else [th];;
```

### Informal statement
The function `IMP_CANON` takes a theorem `th` as input and transforms it into a list of theorems based on the structure of the conclusion of `th`.
- If the conclusion of `th` is a conjunction, then `IMP_CANON` is recursively applied to both conjuncts, and the results are concatenated.
- If the conclusion of `th` is an implication `ante ==> conc`, then:
  - If the antecedent `ante` is a conjunction `a /\ b`, then `IMP_CANON` is applied to the discharged theorem `a ==> b ==> |- NOT_MP th (CONJ (ASSUME a) (ASSUME b))`.
  - If the antecedent `ante` is a disjunction `a \/ b`, then `IMP_CANON` is applied to `a ==> |- NOT_MP th (DISJ1 (ASSUME a) b)` and `b ==> |- NOT_MP th (DISJ2 a (ASSUME b))`, and results are concatenated.
  - If the antecedent `ante` is an existential quantification `EXISTS (x, body)`, then let `x'` be a variant of `x` avoiding the free variables of `th`, and let `body'` be `body` with `x` replaced by `x'`. `IMP_CANON` is applied to the discharge of the substitution `body'` from `NOT_MP th (EXISTS (ante, x') (ASSUME body'))`.
  - Otherwise, `IMP_CANON` is applied to `UNDISCH th`, and each resulting theorem is discharged with respect to the antecedent `ante`.
- If the conclusion of `th` is a universal quantification, then `IMP_CANON` is applied to the result of specializing `th` with `SPEC_ALL`.
- Otherwise, the list containing only the original theorem `th` is returned.

### Informal sketch
The `IMP_CANON` theorem processing function performs a series of transformations of a theorem `th` depending on the structure of its conclusion. The goal is to break down the conclusion into atomic theorems. A key tactic used is `NOT_MP` which represents modus ponens with a negated conclusion, used to eliminate assumptions based on implications.

- **Conjunction:** If the conclusion is `A /\ B`, recursively process `A` and `B` separately by calling `IMP_CANON` on each resulting theorem.
- **Implication:** If the conclusion is `A ==> B`:
  - If `A` is a conjunction `a /\ b`, then construct the proof of `a ==> b ==> B` using `CONJ`, `ASSUME`, and `NOT_MP`. Recursively process with `IMP_CANON`.
  - If `A` is a disjunction `a \/ b`, then construct the proofs of `a ==> B` and `b ==> B` using `DISJ1`, `DISJ2`, `ASSUME`, and `NOT_MP`. Recursively process each with `IMP_CANON`.
  - If `A` is an existential `exists x. body`, then perform variable renaming for `x`, and construct the proof of `body ==> B` where `body` stands for `body` with variable `x` substituted as `x'` using `EXISTS`, `ASSUME` and `NOT_MP`. Recursively process with `IMP_CANON`.
  - Otherwise (if `A` is atomic), remove the discharge from theorem `th` by `UNDISCH th`, put the result into `IMP_CANON`, and for each theorem from the result apply discharge tactic by `DISCH ante`.
- **Universal Quantifier:** If the conclusion is `forall x. P(x)`, specialize the theorem `SPEC_ALL`, and apply `IMP_CANON` to the result.
- **Base Case:** If the conclusion is atomic, return the original theorem wrapped in a list.

### Mathematical insight
The `IMP_CANON` function is a normalization procedure that attempts to decompose complex logical statements into simpler, more manageable theorems. Similar implication canonicalization methods are used to reduce proofs to a canonical form. This transformation is crucial for automated reasoning and efficient proof search.

### Dependencies
- `concl`
- `is_conj`
- `CONJUNCT1`
- `CONJUNCT2`
- `is_imp`
- `dest_neg_imp`
- `is_disj`
- `dest_disj`
- `DISCH`
- `NOT_MP`
- `CONJ`
- `ASSUME`
- `DISJ1`
- `DISJ2`
- `is_exists`
- `dest_exists`
- `variant`
- `thm_frees`
- `subst`
- `EXISTS`
- `UNDISCH`
- `is_forall`
- `SPEC_ALL`

### Porting notes (optional)
- The `variant` function, which generates a variable name that avoids capture, might need special attention when porting.
- The handling of discharging and undischarging theorems (`DISCH` and `UNDISCH`) might differ across systems. Be sure to check the documentation of your target system.
- Pay close attention to how existential elimination and universal instantiation are performed in the target proof assistant.


---

## LIST_MP

### Name of formal statement
LIST_MP

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LIST_MP  = rev_itlist (fun x y -> MP y x);;
```

### Informal statement
The function `LIST_MP` is defined as the reverse iterated application of the function which applies `MP` (Modus Ponens) to its arguments `y` and `x`, where `y` is the antecedent and `x` is the consequent. The iteration is performed over a list.

### Informal sketch
The definition of `LIST_MP` specifies how a list of implications operates. The function `rev_itlist` iterates through the list in reverse order, applying the function `fun x y -> MP y x` at each step. Essentially, it applies Modus Ponens iteratively, starting from the end of the list and working backwards. The final element in the list is a premise, while the other elements are implications.

- `rev_itlist` applies the function from right to left.
- The function `fun x y -> MP y x` represents Modus Ponens, where `y` is the implication and `x` is the current theorem.

### Mathematical insight
This definition formalizes the repeated application of Modus Ponens over a list of implications. It provides a compact and usable formulation for reasoning with a chained sequence of deductions. The order is reversed because Modus Ponens works backwards - from an implication and its antecedent, it infers the consequent.

### Dependencies
- Definition: `rev_itlist`
- Definition: `MP`


---

## DISJ_IMP

### Name of formal statement
DISJ_IMP

### Type of the formal statement
Theorem-deriving Definition

### Formal Content
```ocaml
let DISJ_IMP =
  let pth = TAUT`!t1 t2. t1 \/ t2 ==> ~t1 ==> t2` in
  fun th ->
    try let a,b = dest_disj(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "DISJ_IMP";;
```

### Informal statement
Given a theorem `th` whose conclusion is a disjunction `a \/ b`, derive the theorem `~a ==> b`.

### Informal sketch
- The theorem `TAUT` `!t1 t2. t1 \/ t2 ==> ~t1 ==> t2` is instantiated with the two terms `a` and `b` obtained by deconstructing (using `dest_disj`) the conclusion of the input theorem `th` (which must be of the form `a \/ b`).
- The result of the instantiation `SPECL [a; b] pth` of the tautology along with the original theorem `th` are then combined using Modus Ponens (`MP`) to derive `~a ==> b`.
- If the input theorem `th`'s conclusion is not a disjunction (i.e., `dest_disj` fails) then fail with `"DISJ_IMP"`.

### Mathematical insight
This theorem provides a means to reason about disjunctions in constructive logic. It exploits the equivalence between `a \/ b` and `~a ==> b`. The tactic effectively performs a case split on the disjunction, handling the case where `a` is false to conclude `b`.

### Dependencies
- `TAUT`
- `dest_disj`
- `MP`
- `SPECL`


---

## IMP_ELIM

### Name of formal statement
IMP_ELIM

### Type of the formal statement
Theorem-derived conversion

### Formal Content
```ocaml
let IMP_ELIM =
  let pth = TAUT`!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2` in
  fun th ->
    try let a,b = dest_imp(concl th) in MP (SPECL [a;b] pth) th
    with Failure _ -> failwith "IMP_ELIM";;
```

### Informal statement
The theorem (derived conversion) `IMP_ELIM` takes as input a theorem `th` whose conclusion has the form `a ==> b` for some terms `a` and `b`, and returns a theorem whose conclusion is `~a \/ b`. It attempts to prove `~a \/ b` by using `MP` (Modus Ponens) with `th` and a specialization of the tautology `!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2`. If `th` does not have the form `a ==> b`, it fails.

### Informal sketch
- The theorem `TAUT` is used to prove the tautology `!t1 t2. (t1 ==> t2) ==> ~t1 \/ t2`.
- The conversion `IMP_ELIM` takes a theorem `th`.
- If the conclusion of `th` has the form `a ==> b`, then `MP` is used with the specialization `(a ==> b) ==> ~a \/ b` and the theorem `th` to deduce `~a \/ b`.
- If the conclusion of `th` does not match the expected form, the conversion fails.

### Mathematical insight
The theorem `IMP_ELIM` provides a way to rewrite an implication `a ==> b` into its equivalent form `~a \/ b`. This is a fundamental equivalence in classical logic. Specifically, it implements the logical equivalence of an implication and its corresponding disjunction. It is an example of a derived rule, whose proof is automated, and it returns results of type `thm`.

### Dependencies
- `TAUT`
- `MP`
- `dest_imp`
- `SPECL`


---

## DISJ_CASES_UNION

### Name of formal statement
DISJ_CASES_UNION

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);;
```

### Informal statement
Given a goal `dth` of the form `A \/ B |- C`, if it can be shown that `A |- C` by the assumption tactic with the assumption theorem `ath`, and `B |- C` by the assumption tactic with the assumption theorem `bth`, then the original goal `A \/ B |- C` is proven.

### Informal sketch
The theorem `DISJ_CASES_UNION` states that if we can prove the conclusion `C` from each disjunct (`A` and `B`) of a disjunction `A \/ B`, individually, then we can prove `C` from the disjunction `A \/ B`.

- The function `DISJ_CASES` performs the disjunction elimination, splitting the goal `A \/ B |- C` into two subgoals.
- The first subgoal `A |- C` is discharged by the theorem `ath` using `DISJ1 ath (concl bth)`. `DISJ1` introduces the assumption `A`.
- The second subgoal `B |- C` is discharged by the theorem `bth` using `DISJ2 (concl ath) bth)`. Likewise, `DISJ2` introduces the assumption `B`.
- `concl` extracts the conclusion of the provided theorems to form the appropriate assumption theorems.

### Mathematical insight
This theorem captures a fundamental principle of logic: to prove something from a disjunction, it suffices to prove it from each disjunct separately. This is a common proof strategy and justifies the case-splitting approach when dealing with disjunctions. The theorems `ath` and `bth` encapsulate the specific proofs for each case. The theorem combines the case splitting and assumption tactics to accomplish the discharging of the goal.

### Dependencies
- `DISJ_CASES`
- `DISJ1`
- `DISJ2`
- `concl`

### Porting notes (optional)
This theorem relies on the assumption tactic, which directly uses assumption theorems to discharge subgoals. Proof assistants which don't have an equivalent assumption tactic might need to re-introduce the assumption theorems appropriately to discharge subgoals.


---

## MK_ABS

### Name of formal statement
MK_ABS

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let MK_ABS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = ABS bv rth in
      let cnv = ALPHA_CONV ov in
      CONV_RULE(BINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_ABS";;
```

### Informal statement
The theorem `MK_ABS` states that applying the transformation `SPEC_VAR` to a quotation theorem `qth` (resulting in a variable `bv` and a theorem `rth`), abstracting `bv` in `rth` (resulting in the theorem `sth`), alpha-converting a variable `ov` (obtained from the conclusion of `qth`) with respect to a binary operation, and then applying this conversion as a rule `CONV_RULE` to `sth`, succeeds, provided the initial `qth` satisfies certain conditions. If any of these steps fail, the function will raise a `Failure "MK_ABS"` exception.

### Informal sketch
- The function `MK_ABS` attempts to construct a theorem based on a quotation theorem `qth`.
- It first extracts a binding variable `ov` from the conclusion of `qth`.
- It then applies `SPEC_VAR` to `qth`, which presumably specializes some quantified variable in the assumptions of `qth` and returns both the instantiated variable `bv` and the modified theorem `rth`, specializing a variable in qth.
- Next, it abstracts the variable `bv` in the theorem `rth`, creating a lambda abstraction using `ABS bv rth` to obtain the theorem `sth`.
- It creates an alpha conversion rule `cnv` that renames a variable to `ov` using `ALPHA_CONV ov`.
- Then, `MK_ABS` `CONV_RULE` applies `cnv`.`
- If any of the operations (`bndvar`, `SPEC_VAR`, `ABS`, `ALPHA_CONV``CONV_RULE`) fails, then the entire function call `failwith "MK_ABS"`.

### Mathematical insight
The theorem `MK_ABS` seems to implement meta-reasoning by effectively constructing a new theorem from an existing quotation theorem, involving variable specialization, abstraction and alpha conversion. It provides a way to derive new theorems from existing ones via manipulation of terms within the logic. Effectively, it lifts operations on terms to operations on theorems.

### Dependencies
- `bndvar`
- `rand`
- `concl`
- `SPEC_VAR`
- `ABS`
- `ALPHA_CONV`
- `CONV_RULE`
- `BINOP_CONV`

### Porting notes (optional)
The `SPEC_VAR` function is crucial and its behavior must be replicated exactly. `ALPHA_CONV` must also handle the necessary renaming correctly and avoiding free variable capture, which would be the most difficult part to implement. The exception handling may need to be adapted to the target proof assistant's error reporting mechanisms.


---

## HALF_MK_ABS

### Name of formal statement
HALF_MK_ABS

### Type of the formal statement
Theorem Conversion

### Formal Content
```ocaml
let HALF_MK_ABS th =
  try let th1 = MK_ABS th in
      CONV_RULE(LAND_CONV ETA_CONV) th1
  with Failure _ -> failwith "HALF_MK_ABS";;
```

### Informal statement
The theorem conversion `HALF_MK_ABS` takes a theorem `th` as input. It attempts to apply the rule `MK_ABS` to `th` to obtain a theorem `th1`. If the application of `MK_ABS` is successful, `HALF_MK_ABS` applies the conversion `CONV_RULE(LAND_CONV ETA_CONV)` to `th1` and returns the resulting theorem. If the application of `MK_ABS` fails, `HALF_MK_ABS` raises an exception.

### Informal sketch
The conversion `HALF_MK_ABS` attempts to:
- First, derive a theorem `th1` by applying `MK_ABS` to the input theorem `th`. The `MK_ABS` rule likely introduces an abstraction over a variable.
- Second, if successful, apply the combined conversion `CONV_RULE(LAND_CONV ETA_CONV)` to the resulting theorem `th1`.
  - This conversion likely involves simplifying conjunctions (`LAND_CONV`) and applying eta-reduction (`ETA_CONV`).
- If `MK_ABS` fails, the conversion signals an error.

### Mathematical insight
This conversion combines abstraction introduction (`MK_ABS`) with simplification steps, potentially to put a theorem in a more standardized form. The use of `LAND_CONV` and `ETA_CONV` suggests that theorems whose conclusions contain lambda abstractions and conjunctions are being simplified. The `HALF_` prefix suggests it only performs part of the abstraction simplification or it may related to symmetry.

### Dependencies
- `MK_ABS`
- `CONV_RULE`
- `LAND_CONV`
- `ETA_CONV`


---

## MK_EXISTS

### Name of formal statement
MK_EXISTS

### Type of the formal statement
Theorem-deriving conversion

### Formal Content
```ocaml
let MK_EXISTS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = SPEC_VAR qth in
      let sth = EXISTS_EQ bv rth in
      let cnv = GEN_ALPHA_CONV ov in
      CONV_RULE(BINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_EXISTS";;
```

### Informal statement
The function `MK_EXISTS` takes a theorem `qth` of the form `|- t = F` and attempts to derive a theorem `|- t = T` by replacing a free variable in `t` with existentially quantified `T`. More precisely: It tries to bind a variable `ov` occurring in the right-hand side of the conclusion of the theorem `qth`. It specializes the theorem `qth` using `SPEC_VAR` to obtain a new variable `bv` and a reduced theorem `rth` such that `|- (t[bv/x] = F)`. Then, given a theorem `sth` stating the existential quantification of equality (constructed by `EXISTS_EQ`), it performs alpha conversion on `ov` using `GEN_ALPHA_CONV` resulting in a conversion `cnv`, and finally applies `CONV_RULE` with `BINOP_CONV cnv` to `sth` to prove `|- t = T`. If any of these steps fail, the function `MK_EXISTS` fails.

### Informal sketch
The conversion `MK_EXISTS` aims to prove that a term `t` is equal to `T` given a theorem stating `t` is equal to `F`. It works by:
- Extracting a variable `ov` from the right-hand side of the conclusion of the input theorem. This likely involves pattern matching to find a suitable binding variable.

- Using `SPEC_VAR` to specialize the input theorem `qth` and obtain a variable `bv` and a theorem `rth`. Assume `qth` has the form `|- t = F`.

- Use the specialized theorem `rth` and the variable `bv` to form an existentially quantified equality theorem using `EXISTS_EQ bv rth`. This theorem should have the form `|- (?x. t[x/bv] = F) = T`.

- Create an alpha-conversion `cnv` for `ov` to avoid variable capture, then apply this conversion to the binary operation performed using `BINOP_CONV cnv`.

- Use the converted theorem along with `CONV_RULE` to derive the final theorem `|- t = T`.

### Mathematical insight
This conversion encodes a specific pattern of reasoning about equality, where specializing a universally quantified variable allows one to assert an existential statement. The key idea is to leverage the contradiction (`t=F`) provided by input theorem `qth` to convert it to a True case given a equality theorem that replaces the quantified variable by specialized one using `EXISTS_EQ`

### Dependencies
- `bndvar`
- `rand`
- `concl`
- `SPEC_VAR`
- `EXISTS_EQ`
- `GEN_ALPHA_CONV`
- `CONV_RULE`
- `BINOP_CONV`

### Porting notes (optional)
- The `try ... with Failure _ -> failwith` construct should be translated to appropriate exception handling mechanisms in other proof assistants.
- The use of `SPEC_VAR` and `EXISTS_EQ` indicates a dependency on specific logical structures (universal quantification and equality). Ensure that the target proof assistant has similar constructs.
- The variable renaming via `GEN_ALPHA_CONV` is crucial to avoid variable capture. Ensure that alpha-conversion is handled correctly in the target system.


---

## LIST_MK_EXISTS

### Name of formal statement
LIST_MK_EXISTS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LIST_MK_EXISTS l th = itlist (fun x th -> MK_EXISTS(GEN x th)) l th;;
```

### Informal statement
Given a list `l` of variables and a term `th`, create a term by iterating through the list `l`. For each variable `x` in `l`, create an existential quantification `EXISTS x. t` where `t` is the term accumulated so far. The initial term is `th`.

### Informal sketch
The definition `LIST_MK_EXISTS` constructs a nested existential quantification over a list of variables. The function `itlist` applies a function (in this case, creating an existential quantifier) to each element (variable) of the list, accumulating the result.

*   Initialize the term as `th`.
*   Iterate through the list `l`. In each step, take the current variable `x` from `l` and the current term `t`. Create a new term `EXISTS x. t` by existentially quantifying variable `x` over term `t`.
*   The final result will be nested existential quantifications, where the innermost term is `th`. E.g. for a list `[x1; x2; x3]` and term `t`, the definition creates `EXISTS x1. EXISTS x2. EXISTS x3. t`.

### Mathematical insight
This definition provides a convenient way to create nested existential quantifications. Constructing quantified formulas in proof assistants like HOL Light is a common task, and this definition encapsulates that process, making it easier to quantify over multiple variables at once.

### Dependencies
- `MK_EXISTS`
- `GEN`
- `itlist`


---

## IMP_CONJ

### Name of formal statement
IMP_CONJ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let IMP_CONJ th1 th2 =
  let A1,C1 = dest_imp (concl th1) and A2,C2 = dest_imp (concl th2) in
  let a1,a2 = CONJ_PAIR (ASSUME (mk_conj(A1,A2))) in
      DISCH (mk_conj(A1,A2)) (CONJ (MP th1 a1) (MP th2 a2));;
```

### Informal statement
Given two theorems `th1` and `th2` whose conclusions are implications of the form `A1 ==> C1` and `A2 ==> C2` respectively, derive a theorem whose conclusion is the conjunction `(A1 /\ A2) ==> (C1 /\ C2)`.

### Informal sketch
The proof proceeds as follows:
- Destruct the conclusions of the given theorems `th1` and `th2` to obtain the assumptions `A1` and `A2`, and the conclusions `C1` and `C2` respectively, using `dest_imp`. Thus, `th1` proves `A1 ==> C1` and `th2` proves `A2 ==> C2`.
- Assume the conjunction `A1 /\ A2`, obtaining the assumption theorem `ASSUME (mk_conj(A1,A2))`.
- Split this conjunctive assumption into two assumptions, `a1` which is `A1` and `a2` which is `A2`, using `CONJ_PAIR`.
- Apply Modus Ponens to `th1 : A1 ==> C1` and `a1 : A1` to obtain `C1`.
- Apply Modus Ponens to `th2 : A2 ==> C2` and `a2 : A2` to obtain `C2`.
- Form the conjunction of `C1` and `C2` using `CONJ`, so we have `C1 /\ C2`.
- Discharge the initial assumption `A1 /\ A2` to obtain the implication `(A1 /\ A2) ==> (C1 /\ C2)` using `DISCH`.

### Mathematical insight
This theorem shows how to combine two implications into a single implication where both the assumptions and the conclusions are conjoined. This is a standard logical manipulation, allowing one to reason about multiple implications simultaneously when their assumptions can be proven together.

### Dependencies
- `dest_imp`
- `concl`
- `CONJ_PAIR`
- `ASSUME`
- `mk_conj`
- `DISCH`
- `CONJ`
- `MP`


---

## EXISTS_IMP

### Name of formal statement
EXISTS_IMP

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EXISTS_IMP x =
  if not (is_var x) then failwith "EXISTS_IMP: first argument not a variable"
  else fun th ->
         try let ante,cncl = dest_imp(concl th) in
             let th1 = EXISTS (mk_exists(x,cncl),x) (UNDISCH th) in
             let asm = mk_exists(x,ante) in
             DISCH asm (CHOOSE (x,ASSUME asm) th1)
         with Failure _ -> failwith "EXISTS_IMP: variable free in assumptions";;
```

### Informal statement
Given a variable `x` and a theorem `th` whose conclusion is an implication `ante ==> cncl`, if `x` is not free in the assumptions of `th`, then `?x. ante ==> cncl` implies `(?x. ante) ==> (?x. cncl)`.

### Informal sketch
- The function `EXISTS_IMP` takes a variable `x` and a theorem `th: A |- (ante ==> cncl)` as input.
- It checks if `x` is indeed a variable.
- It decomposes the conclusion of `th` into the antecedent `ante` and conclusion `cncl` of the implication.
- It removes the discharge of the assumptions `A` from the theorem `th` using `UNDISCH`, resulting in `|- (ante ==> cncl)`.
- It applies existential quantification to the consequent `cncl` with variable `x`, resulting in the theorem `|- ?x. cncl` when the existential variable is not free in assumptions of `th`.
- Now by applying the `EXISTS` rule, the theorem becomes `|- (ante ==> (?x. cncl)) ==> (?x.cncl)`.
- Form the assumption `asm` which is `?x. ante`.
- Assume `asm` using `ASSUME`, i.e., `asm |- asm`, which is `?x. ante |- ?x. ante`.
- Use `CHOOSE` to derive `?x.ante |- ante`, provided `x` is not free in `?x.ante`.
- Derive `?x.ante |- cncl` using the original `th` which concludes `ante ==> cncl`
- Apply `EXISTS` rule get `(?x.ante) |- (?x.cncl)`
- Discharge `?x.ante` using `DISCH` to obtaining the final result `|- (?x. ante) ==> (?x. cncl)`.

### Mathematical insight
This theorem provides a way to transform an implication involving free variables into an implication involving existentially quantified formulas. It is a standard and useful principle in first-order logic. Existential quantification distributes over implication under certain conditions, namely that we can instantiate the antecedent and consequent to the same witness. This is an important derived rule as it allows one to move existential quantifiers outside of an implication.

### Dependencies
- `is_var`
- `dest_imp`
- `EXISTS`
- `UNDISCH`
- `mk_exists`
- `DISCH`
- `CHOOSE`
- `ASSUME`


---

## CONJUNCTS_CONV

### Name of formal statement
CONJUNCTS_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let CONJUNCTS_CONV (t1,t2) =
  let rec build_conj thl t =
    try let l,r = dest_conj t in
        CONJ (build_conj thl l) (build_conj thl r)
    with Failure _ -> find (fun th -> concl th = t) thl in
  try IMP_ANTISYM_RULE
     (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
     (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
  with Failure _ -> failwith "CONJUNCTS_CONV";;
```
### Informal statement
Given two terms `t1` and `t2`, the conversion `CONJUNCTS_CONV (t1, t2)` attempts to prove the equivalence (mutual implication) between `t1` and `t2` by iteratively breaking down `t1` and `t2` into conjunctions. If successful it returns the theorem `!t1. !t2. (t1 <=> t2)`.

The conversion recursively decomposes `t2` (and `t1`) into its conjuncts, using the library theorem `CONJUNCTS (ASSUME t1)` (and `CONJUNCTS (ASSUME t2)`) to match the conjuncts of `t2` (and `t1`) against the assumed term `t1` (and `t2`). If `t2` (and `t1`) cannot be decomposed further, the conversion searches for a theorem in `thl` (where `thl` consists of the conjuncts of `t1` (and `t2`)) whose conclusion is equal to the undcomposed term. Finally the equivalence between `t1` and `t2` is proved by showing that `t1` implies `t2` and `t2` implies `t1` (using `IMP_ANTISYM_RULE`).

### Informal sketch
The conversion `CONJUNCTS_CONV` attempts to prove the equivalence of two terms by decomposing them into conjunctions.

- First, a recursive function `build_conj` attempts to decompose the input term (`t2` and `t1` respectively) into conjunctions.
    - If the term is a conjunction `l /\ r`, then `build_conj` is recursively called on `l` and `r`, and the results are combined using the `CONJ` constructor.
    - Otherwise, it searches for a theorem in the list `thl` (initially the conjuncts of `t1` or `t2` assumed as hypotheses) whose conclusion matches the term.
- The conversion then tries to establish the equivalence between `t1` and `t2` by proving `t1 ==> t2` and `t2 ==> t1`, then applying `IMP_ANTISYM_RULE`.
    - `DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2)` proves `t1 ==> t2`
    - `DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1)` proves `t2 ==> t1`
- If any of these steps fail, the conversion fails.

### Mathematical insight
This conversion is useful for proving the equivalence of two terms when they are both conjunctions of similar subterms, possibly in different orders. It automates the process of breaking down the conjunctions and matching corresponding conjuncts. The use of `CONJUNCTS` to obtain the conjuncts of the assumptions makes this conversion fairly robust in handling reordered conjuncts.

### Dependencies
- Theorem: `CONJUNCTS`
- Theorem: `IMP_ANTISYM_RULE`
- Theorem: `ASSUME`


---

## CONJ_SET_CONV

### Name of formal statement
CONJ_SET_CONV

### Type of the formal statement
New Definition

### Formal Content
```ocaml
let CONJ_SET_CONV l1 l2 =
  try CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
  with Failure _ -> failwith "CONJ_SET_CONV";;
```

### Informal statement
The function `CONJ_SET_CONV`, when applied to two lists of terms `l1` and `l2`, attempts to convert the conjunction of the terms in `l1` to the conjunction of the terms in `l2` using the `CONJUNCTS_CONV` conversion. If this conversion fails, the function raises an exception. `list_mk_conj` transforms two lists of terms into a single conjunctive term.

### Informal sketch
- The function `CONJ_SET_CONV` first constructs the conjunctions `list_mk_conj l1` and `list_mk_conj l2` from the given lists `l1` and `l2`, respectively.
- It then attempts to convert `list_mk_conj l1` to `list_mk_conj l2` using the conversion `CONJUNCTS_CONV`.
- If the conversion `CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)` succeeds, the result is returned.
- If the conversion fails (raising a `Failure` exception), it catches the exception and re-raises a new exception with the message "CONJ_SET_CONV". This signals that the conversion was not successful.

### Mathematical insight
This function is designed to efficiently convert one conjunctive formula into another when the conjuncts are presented as lists. It leverages an existing conversion `CONJUNCTS_CONV`, providing a way to handle failures gracefully. The `CONJ_SET_CONV` is a conversion that checks if a set of conjuncts is convertible to another set of conjuncts.

### Dependencies
- `CONJUNCTS_CONV`
- `list_mk_conj`

### Porting notes (optional)
The error handling using exceptions might need adjustment depending on the target proof assistant's exception mechanisms. Ensure that the underlying conversion (`CONJUNCTS_CONV`) is available or can be reproduced with similar functionality. If the target proof assistant lacks a direct equivalent to `CONJUNCTS_CONV`, it might be necessary to implement a custom conversion strategy.


---

## FRONT_CONJ_CONV

### Name of formal statement
FRONT_CONJ_CONV

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let FRONT_CONJ_CONV tml t =
 let rec remove x l =
    if hd l = x then tl l else (hd l)::(remove x (tl l)) in
 try CONJ_SET_CONV tml (t::(remove t tml))
 with Failure _ -> failwith "FRONT_CONJ_CONV";;
```
### Informal statement
For any term list `tml` and term `t`, the theorem states the result of attempting the conversion `CONJ_SET_CONV tml (t::(remove t tml))`. If the `CONJ_SET_CONV` conversion fails, then the function `FRONT_CONJ_CONV` fails. The function `remove` removes the first occurence of an element `x` from a list `l`. If the head of `l` equals `x`, then the result is the tail of `l`; otherwise, the result is the head of `l` prepended to the result of recursively calling `remove` with `x` and the tail of `l`.

### Informal sketch
The theorem defines a conversion `FRONT_CONJ_CONV` that attempts to use `CONJ_SET_CONV` after adjusting the input list.

- The function `remove x l` is defined recursively, removing the first occurrence of `x` from `l`.
- The conversion attempts to apply `CONJ_SET_CONV` to `tml` with an adjustment: `t` is prepended to `tml` after the first occurrence of `t` is removed from `tml`. This adjustment is performed by constructing a new list `t::(remove t tml)`.
- A `try ... with Failure _ -> failwith` block manages potential failures. If `CONJ_SET_CONV` fails, then `FRONT_CONJ_CONV` fails.

### Mathematical insight
The function `FRONT_CONJ_CONV` is designed to adjust a set of conjuncts of a term by removing the first instance of the current proven term, and add it at the beginning. This ensures that the most recently established term is considered first when attempting to prove a goal by conjunction simplification. It tries to put the current term to the front before applying `CONJ_SET_CONV`.

### Dependencies
- `CONJ_SET_CONV`


---

## CONJ_DISCH

### Name of formal statement
CONJ_DISCH

### Type of the formal statement
theorem

### Formal Content
```ocaml
let CONJ_DISCH =
  let pth = TAUT`!t t1 t2. (t ==> (t1 <=> t2)) ==> (t /\ t1 <=> t /\ t2)` in
  fun t th ->
    try let t1,t2 = dest_eq(concl th) in
        MP (SPECL [t; t1; t2] pth) (DISCH t th)
    with Failure _ -> failwith "CONJ_DISCH";;
```

### Informal statement
Given a term `t` and a theorem `th` whose conclusion is an equivalence `t1 <=> t2`, the theorem `CONJ_DISCH t th` proves the equivalence `t /\ t1 <=> t /\ t2`, assuming that `t ==> (t1 <=> t2)` holds.

### Informal sketch
- The theorem `TAUT` `!t t1 t2. (t ==> (t1 <=> t2)) ==> (t /\ t1 <=> t /\ t2)` is instantiated with the provided term `t` and the left-hand side `t1` and right-hand side `t2` of the equivalence which forms the conclusion of the theorem `th`.
- The assumption `t ==> (t1 <=> t2)` is discharged using `DISCH t th` resulting in a theorem with conclusion `t ==> (t1 <=> t2)`.
- Modus ponens (`MP`) is applied to combine the instantiated theorem and the discharged theorem, proving `t /\ t1 <=> t /\ t2`.

### Mathematical insight
The theorem states that if `t1` and `t2` are equivalent under the condition `t`, then `t /\ t1` and `t /\ t2` are unconditionally equivalent. In other words, if two expressions are equivalent when `t` is true, then conjoining each of them with `t` results in equivalent expressions without any condition. This result is useful when working with conditional equivalences and reasoning about the behavior of systems under specific conditions.

### Dependencies
- `TAUT`
- `dest_eq`
- `MP`
- `SPECL`
- `DISCH`


---

## rec

### Name of formal statement
rec

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let rec CONJ_DISCHL l th =
  if l = [] then th else CONJ_DISCH (hd l) (CONJ_DISCHL (tl l) th);;
```

### Informal statement
Define a recursive function `CONJ_DISCHL` taking a list of terms `l` and a term `th` as input. If the list `l` is empty, the function returns `th`. Otherwise, it applies the function `CONJ_DISCH` to the head of the list `l` and the result of recursively calling `CONJ_DISCHL` on the tail of `l` and `th`.

### Informal sketch
The definition proceeds by recursion on the list `l`.
- Base case: If `l` is empty, return `th`.
- Recursive step: If `l` is not empty, apply `CONJ_DISCH` to the head of `l` and the recursive call of `CONJ_DISCHL` on the tail of `l` with `th`.
The structure follows a standard list recursion pattern.

### Mathematical insight
The function `CONJ_DISCHL` repeatedly applies `CONJ_DISCH` to elements of a list. It is likely used to discharge a list of conjuncts from a hypothesis. Each application of `CONJ_DISCH` probably separates a conjunction.

### Dependencies
- `CONJ_DISCH`
- `hd` (head of a list)
- `tl` (tail of a list)


---

## rec

### Name of formal statement
rec

### Type of the formal statement
Definition

### Formal Content
```ocaml
let rec GSPEC th =
  let wl,w = dest_thm th in
  if is_forall w then
      GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
  else th;;
```

### Informal statement
Define a recursive function `GSPEC` that takes a theorem `th` as input. If the conclusion `w` of the theorem `th` (where `wl` is the assumptions of `th`) is a universal quantification, then apply `GSPEC` to the theorem obtained by specializing `th` with a generic variable of the appropriate type. Otherwise, if the conclusion is not a universal quantification, return the original theorem `th`.

### Informal sketch
The function `GSPEC` removes leading universal quantifiers from the conclusion of a theorem by repeatedly specializing the theorem with fresh variables until the conclusion is no longer a universal quantification.
- The function destructures the theorem `th` into its assumptions and conclusion.
- It checks if the conclusion is a universal quantification using `is_forall`.
- If the conclusion is a universal quantification, it specializes the theorem using `SPEC` with a generic variable generated by `genvar` having the correct type (obtained from `type_of (fst (dest_forall w))`). Then, it recursively calls `GSPEC` with the specialized theorem.
- If the conclusion is not a universal quantification, the function returns the original theorem `th`.

### Mathematical insight
The function `GSPEC` is used to strip off leading universal quantifiers from a theorem. This is a common operation when you want to apply a theorem to a specific instance or when you want to reason about the body of a quantified statement. The repeated application of `SPEC` effectively instantiates the universally quantified variables with fresh variables, which can then be used in subsequent proof steps.

### Dependencies
Core:
- `dest_thm`
- `is_forall`
- `SPEC`
- `genvar`
- `type_of`
- `dest_forall`


---

## ANTE_CONJ_CONV

### Name of formal statement
ANTE_CONJ_CONV

### Type of the formal statement
theorem

### Formal Content
```ocaml
let ANTE_CONJ_CONV tm =
  try let (a1,a2),c = (dest_conj F_F I) (dest_imp tm) in
      let imp1 = MP (ASSUME tm) (CONJ (ASSUME a1) (ASSUME a2)) and
          imp2 = LIST_MP [CONJUNCT1 (ASSUME (mk_conj(a1,a2)));
                          CONJUNCT2 (ASSUME (mk_conj(a1,a2)))]
                         (ASSUME (mk_imp(a1,mk_imp(a2,c)))) in
      IMP_ANTISYM_RULE (DISCH_ALL (DISCH a1 (DISCH a2 imp1)))
                       (DISCH_ALL (DISCH (mk_conj(a1,a2)) imp2))
  with Failure _ -> failwith "ANTE_CONJ_CONV";;
```

### Informal statement
Given a term `tm` of the form `(a1 /\ a2) ==> c`, the theorem `ANTE_CONJ_CONV` proves the equivalence between `(a1 /\ a2) ==> c` and `a1 ==> a2 ==> c`.

### Informal sketch
The tactic `ANTE_CONJ_CONV` attempts to prove the equivalence between `(a1 /\ a2) ==> c` and `a1 ==> a2 ==> c`. The proof proceeds as follows:
- Deconstructs the input term `tm`, which should have the form `(a1 /\ a2) ==> c`, into its constituent parts `a1`, `a2`, and `c` using `dest_imp` and `dest_conj`. It destructs the hypothesis to extract the conjuncts and the consequent.
- Constructs a proof of `(a1 /\ a2) ==> c |- a1 /\ a2`. Then, uses conjunction introduction to obtain `(a1 /\ a2) ==> c |- a1 /\ a2`. This is achieved using `MP` with `ASSUME tm` and `CONJ (ASSUME a1) (ASSUME a2)`.
- Constructs a proof of `a1 /\ a2 |- a1 ==> a2 ==> c`. The first assumption made by `LIST_MP` is `CONJUNCT1 (ASSUME (mk_conj(a1,a2))) resulting in a1`. The second assumption is `CONJUNCT2 (ASSUME (mk_conj(a1,a2))) resulting in a2`. These are used to derive/discharge `mk_imp(a1, mk_imp(a2,c))`.
- Finally, combines these two implications using `IMP_ANTISYM_RULE` after discharging assumptions `a1`, `a2` in the first implication and `(a1 /\ a2)` in the second implication to prove the bi-implication. `DISCH_ALL` is then used to discharge any remaining type variables.
- If the input term `tm` does not match the expected form, the tactic fails.

### Mathematical insight
This theorem encapsulates a fundamental logical equivalence: an implication with a conjunctive antecedent is equivalent to a nested implication where the conjuncts become successive antecedents. This is crucial for manipulating logical formulas and simplifying proofs. This allows rewriting conjunctions in the antecedent to successive implications which is a useful tool in many proofs.

### Dependencies
- `dest_conj`
- `dest_imp`
- `MP`
- `ASSUME`
- `CONJ`
- `CONJUNCT1`
- `CONJUNCT2`
- `mk_conj`
- `mk_imp`
- `IMP_ANTISYM_RULE`
- `DISCH_ALL`
- `DISCH`


---

## bool_EQ_CONV

### Name of formal statement
bool_EQ_CONV

### Type of the formal statement
Theorem (conversion)

### Formal Content
```ocaml
let bool_EQ_CONV =
  let check = let boolty = `:bool` in check (fun tm -> type_of tm = boolty) in
  let clist = map (GEN `b:bool`)
                  (CONJUNCTS(SPEC `b:bool` EQ_CLAUSES)) in
  let tb = hd clist and bt = hd(tl clist) in
  let T = `T` and F = `F` in
  fun tm ->
    try let l,r = (I F_F check) (dest_eq tm) in
        if l = r then EQT_INTRO (REFL l) else
        if l = T then SPEC r tb else
        if r = T then SPEC l bt else fail()
    with Failure _ -> failwith "bool_EQ_CONV";;
```
### Informal statement
The `bool_EQ_CONV` is a conversion for boolean equalities. Given a term `tm` that is an equality between two boolean terms `l` and `r`, it attempts to prove the equality.
If `l` and `r` are identical, it returns a reflexivity proof.
If `l` is `T`, it specializes the theorem `tb` with `r`.
If `r` is `T`, it specializes the theorem `bt` with `l`.
Otherwise, the conversion fails. `tb` and `bt` are instances of `EQ_CLAUSES` specialized with a boolean variable `b`.

### Informal sketch
- The conversion `bool_EQ_CONV` takes a term `tm` assumed to be an equation `l = r` between boolean terms.
- It first checks if `tm` is indeed an equation using `dest_eq`.
- It obtains the left-hand side `l` and the right-hand side `r` of the equation.
- If `l` and `r` are equal, `REFL l` provides a proof for `l = l`, and `EQT_INTRO` lifts it to a conversion.
- If `l` is the boolean constant `T`, then the theorem `SPEC r tb` returns a proof of `T = r` specialized over `b` with `r`, where `tb` is the theorem `!b. T = b ==> b`.
- If `r` is the boolean constant `T`, then the theorem `SPEC l bt` returns a proof of `l = T` specialized over `b` with `l`, where `bt` is the theorem `!b. b = T ==> b`.
- If none of the above conditions are met, the conversion fails.
- The theorems `tb` and `bt` are obtained by specializing the automatically derived theorems `EQ_CLAUSES` which represent the boolean equality laws.

### Mathematical insight
This conversion simplifies boolean equalities of the form `T = r` or `l = T` to `r` or `l` respectively. It leverages the boolean equality laws. It is part of a suite of conversions that can be used for automated simplification. `CONJUNCTS(SPEC `b:bool` EQ_CLAUSES)` generates a list of theorems that represent standard boolean equalities laws.

### Dependencies
Theorems:
- `EQ_CLAUSES`


---

## COND_CONV

### Name of formal statement
`COND_CONV`

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let COND_CONV =
  let T = `T` and F = `F` and vt = genvar`:A` and vf = genvar `:A` in
  let gen = GENL [vt;vf] in
  let CT,CF = (gen F_F gen) (CONJ_PAIR (SPECL [vt;vf] COND_CLAUSES)) in
  fun tm ->
    let P,(u,v) = try dest_cond tm
                  with Failure _ -> failwith "COND_CONV: not a conditional" in
    let ty = type_of u in
    if (P=T) then SPEC v (SPEC u (INST_TYPE [ty,`:A`] CT)) else
    if (P=F) then SPEC v (SPEC u (INST_TYPE [ty,`:A`] CF)) else
    if (u=v) then SPEC u (SPEC P (INST_TYPE [ty,`:A`] COND_ID)) else
    if (aconv u v) then
       let cnd = AP_TERM (rator tm) (ALPHA v u) in
       let thm = SPEC u (SPEC P (INST_TYPE [ty,`:A`] COND_ID)) in
           TRANS cnd thm else
  failwith "COND_CONV: can't simplify conditional";;
```

### Informal statement
The theorem `COND_CONV` is a conditional simplification tactic. It takes a term `tm` representing a conditional expression `P --> u | v` and attempts to simplify it based on the values of `P`, `u`, and `v`.
- If `P` is equal to `T` (true), then the term is simplified to `u`.
- If `P` is equal to `F` (false), then the term is simplified to `v`.
- If `u` and `v` are equal, then the term is simplified to `u`.
- If `u` and `v` are alpha-equivalent, then the conditional is rewritten by alpha conversion of `v` to `u` using `ALPHA v u`, resulting in a term of the form `P --> u | u`, which then simplifies to `u`.
- If none of the above conditions are met, the tactic fails.

### Informal sketch
The tactic `COND_CONV` examines a conditional term and attempts to simplify it.
- First, it decomposes the input term `tm` into its constituent parts `P`, `u`, and `v`, representing the condition, the "then" branch, and the "else" branch. `dest_cond` attempts to destructure the term as a conditional; failure indicates the input is not a conditional.
- It checks if `P` is equal to `T`. If it is, it uses `SPEC` and `INST_TYPE` with theorem `CT` (derived from `COND_CLAUSES`) to reduce the conditional to `u`.
- It checks if `P` is equal to `F`. If it is, it uses `SPEC` and `INST_TYPE` with theorem `CF` (derived from `COND_CLAUSES`) to reduce the conditional to `v`.
- It checks if `u` and `v` are equal. If they are, it uses `SPEC` and `INST_TYPE` with theorem `COND_ID` to reduce the conditional to `u`.
- It checks if `u` and `v` are alpha-equivalent using `aconv`. If they are, it applies alpha conversion with `ALPHA v u` to create a term where both branches are syntactically equal. Then, it uses `SPEC` and `INST_TYPE` with `COND_ID`, along with `TRANS`, to rewrite the original conditional to `u`.
- If none of the above simplifications apply, it fails.

### Mathematical insight
The `COND_CONV` tactic embodies the fundamental simplifications applicable to conditional expressions. It formalizes the idea that if the condition is true, the expression evaluates to the "then" branch, and if the condition is false, it evaluates to the "else" branch.  Furthermore, if both branches are equivalent, the conditional can be replaced by either branch. The alpha-equivalence check allows the tactic to normalize expressions before performing the simplification, improving robustness.

### Dependencies
- Definitions: `T`, `F`
- Theorems: `COND_CLAUSES`, `COND_ID`
- Functions: `dest_cond`, `type_of`, `SPEC`, `INST_TYPE`, `ALPHA`, `ACONV`, `GENL`, `CONJ_PAIR`, `TRANS`, `AP_TERM`, `rator`, `SPECL`, `genvar`

### Porting notes (optional)
- The `dest_cond` function will need to be reproduced or replaced with an equivalent tactic for decomposing conditional terms.
- Theorems such as `COND_CLAUSES` and `COND_ID` need to be ported, ensuring equivalent logical content. The specifics of how these are proven/imported are important.
- Pay attention to the handling of type instantiation via `INST_TYPE`, as the syntax and functionality vary across systems.
- The alpha conversion function `ALPHA` also needs an analogue in the target system.
- The tactic relies on equational reasoning, so ensuring that the target system has suitable rewriting rules and a tactic for applying equations (`TRANS` in HOL Light) will be crucial.


---

## SUBST_MATCH

### Name of formal statement
SUBST_MATCH

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUBST_MATCH eqth th =
 let tm_inst,ty_inst = find_match (lhs(concl eqth)) (concl th) in
 SUBS [INST tm_inst (INST_TYPE ty_inst eqth)] th;;
```
### Informal statement
Given an equational theorem `eqth` asserting that some term is equal to another, and a theorem `th`, the function `SUBST_MATCH` attempts to unify the left-hand side of the conclusion of `eqth` with the conclusion of `th`. If successful, it produces a substitution mapping terms and types, then instantiates `eqth` with these mappings, and finally performs the substitution on `th` using the instantiated `eqth`.

### Informal sketch
The proof proceeds by:
- Attempting to match the left-hand side of the conclusion of the equational theorem `eqth` with the conclusion of the theorem `th`, resulting in term and type instantiations `tm_inst` and `ty_inst`.
- Instantiating the equational theorem `eqth` with `tm_inst` and `ty_inst` using `INST` and `INST_TYPE` respectively.
- Substituting in `th` with the instantiated theorem obtained from the previous step, using the `SUBS` tactic.

### Mathematical insight
This theorem provides a mechanism for rewriting a theorem `th` based on an equational theorem `eqth`. It first tries to match a part of `th`'s conclusion with the left-hand side of `eqth`'s conclusion using unification. If the unification succeeds, it yields a substitution which can then be applied to both `eqth` and `th` to perform a rewriting. This is a core procedure for equational reasoning in HOL Light

### Dependencies
- Definitions: `lhs`, `concl`
- Theorems: `INST`, `INST_TYPE`, `SUBS`, `find_match`


---

## SUBST

### Name of formal statement
SUBST

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let SUBST thl pat th =
  let eqs,vs = unzip thl in
  let gvs = map (genvar o type_of) vs in
  let gpat = subst (zip gvs vs) pat in
  let ls,rs = unzip (map (dest_eq o concl) eqs) in
  let ths = map (ASSUME o mk_eq) (zip gvs rs) in
  let th1 = ASSUME gpat in
  let th2 = SUBS ths th1 in
  let th3 = itlist DISCH (map concl ths) (DISCH gpat th2) in
  let th4 = INST (zip ls gvs) th3 in
  MP (rev_itlist (C MP) eqs th4) ;;
```

### Informal statement
Given a list of theorems `thl` of the form `t1 = u1, ..., tn = un`, a term `pat` and a theorem `th` whose assumption is `pat`, the theorem `SUBST thl pat th` is obtained as follows:

Let `eqs` be the list of equations in `thl`, and `vs` the list of left-hand sides of the equations `t1,...,tn`. Let `gvs` be a list of generated variables of the same types as `vs`. Let `gpat` be the term obtained by substituting the generated variables `gvs` for the original variables `vs` in the term `pat`. 

Next, let `ls` be the left-hand sides of the equations in `eqs` and `rs` the right-hand sides of the equations in `eqs`. Let `ths` be a list of theorems, where each theorem is an assumption of the equation `gi = ui` where `gi` is a generic variable from `gvs` and `ui` is the corresponding right-hand side from `rs`.

Now, assume `gpat` to produce the theorem `th1`. perform a substitution using the assumptions `ths` on the theorem `th1` to obtain `th2`. Then discharge all the assumptions `gi = ui` and `gpat` from `th2` to get `th3`. Afterwards specialize the assumptions by instantiating theorem `th3` with the list of pairs formed out of `ls` and `gvs`.

Finally, perform a series of modus ponens inferences using the theorems `eqs` and the theorem `th4` to yield the final result.

### Informal sketch
The theorem `SUBST` is a form of substitution that replaces variables in the assumption of a theorem.
- Given a list of equational theorems `thl` (`t1 = u1, ..., tn = un`) and a theorem `th` whose assumption is `pat`, aim to prove a theorem whose assumption is `subst [(t1, u1), ..., (tn, un)] pat`.
- Introduce fresh, generic variables `gvs` for the left-hand sides `vs` of the equations in `thl`.
- Replace the variables `vs` in the pattern `pat` with the fresh variables `gvs`, yielding a modified assumption `gpat`.
- Assume each equation `gi = ui` for each generic variable `gi` in `gvs` and corresponding right-hand side `ui` from `eqs`.
- Substitute the fresh variables `gvs` in `pat` to produce `gpat`.
- Assume `gpat` and perform a substitution with the generated assumptions `gi = ui`, discharging all assumptions `gi = ui` and `gpat`.
- Instantiate with the actual left-hand sides `ls` where the `gi`'s are.
- Perform a sequence of modus ponens inferences using the original equational theorems `eqs`.

### Mathematical insight
The `SUBST` theorem provides a mechanism to perform substitutions within the assumptions of theorems.
This is a core part of rewriting and equational reasoning in HOL Light. The introduction of generic variables and subsequent instantiation ensures that the substitution is sound and avoids variable capture issues.

### Dependencies
None evident from content (assumed basic theorem-proving primitives).

### Porting notes (optional)
The `SUBST` theorem relies heavily on HOL's metatheory and its manipulation of theorems.
In other proof assistants (e.g., Coq, Lean), the corresponding functionality might be provided by tactics that handle rewriting and substitutions more implicitly.
The key is to ensure that the variable renaming and instantiation steps are handled correctly to maintain logical soundness.
Specifically, be mindful of variable capture when translating this theorem, as the `subst` function in HOL Light is carefully designed to avoid it.
Use of de Bruijn indices or similar techniques can be helpful in this regard. Some proof assistants have facilities to generate fresh variables, analogous to HOL Light's `genvar`; ensure that you are using these correctly.


---

## SUBST_CONV

### Name of formal statement
SUBST_CONV

### Type of the formal statement
Conversion

### Formal Content
```ocaml
let SUBST_CONV thvars template tm =
  let thms,vars = unzip thvars in
  let gvs = map (genvar o type_of) vars in
  let gtemplate = subst (zip gvs vars) template in
  SUBST (zip thms gvs) (mk_eq(template,gtemplate)) (REFL tm);;
```

### Informal statement
Given a list `thvars` of theorem-variable pairs, a term `template`, and a term `tm`, the conversion `SUBST_CONV thvars template tm` returns a theorem.
Let `thms` be the list of theorems and `vars` the list of variables obtained by unzipping `thvars`.
Let `gvs` be the list of generated variables, where each generated variable is obtained by creating a fresh variable of the same type as the corresponding variable in `vars`.
Let `gtemplate` be the term obtained by substituting each generated variable in `gvs` for the corresponding variable in `vars` within the `template`.
The resulting theorem is obtained by applying the substitution conversion `SUBST` with theorem-variable pairs built from `thms` and `gvs` to the equation `template = gtemplate` and the reflexivity theorem `REFL tm`.

### Informal sketch
- The conversion `SUBST_CONV` performs a substitution based on a list of theorems and variables.
- It first generates fresh variables `gvs` corresponding to the variables in `vars`.
- It then creates a modified template `gtemplate` by substituting the fresh variables into the original `template`.
- It forms an equation between the original `template` and the modified `gtemplate`.
- Finally, it uses the `SUBST` conversion to apply the given theorems `thms` (substituted for the generated variables `gvs`) to the equation `template = gtemplate`, applying the result to the reflexivity theorem `REFL tm` about the input term `tm`.
- The effect is to rewrite `tm` to itself.

### Mathematical insight
The `SUBST_CONV` conversion allows for a controlled substitution of variables in a term, using existing theorems as substitutions. It essentially constructs an equality stating that substituting generated variables into a template is equivalent to the template itself, and then uses given theorems to perform further substitutions based on these freshly generated variables in a way that is known to be type-safe. Finally the conversion maps this equality to the trivial reflexivity theorem `tm = tm` for the term `tm`, so that the resulting theorem proves `tm = tm`.

### Dependencies
- `unzip`
- `genvar`
- `type_of`
- `subst`
- `zip`
- `mk_eq`
- `SUBST`
- `REFL`


---

## FILTER_PURE_ASM_REWRITE_RULE

### Name of formal statement
FILTER_PURE_ASM_REWRITE_RULE

### Type of the formal statement
Definition

### Formal Content
```ocaml
let FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ASM_REWRITE_RULE f thl th =
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th

and FILTER_ONCE_ASM_REWRITE_RULE f thl th =
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th;;
```

### Informal statement
The function `FILTER_PURE_ASM_REWRITE_RULE` takes a predicate `f`, a list of theorems `thl`, and a theorem `th` as input. It returns a new theorem obtained by applying a pure rewrite rule derived from a subset of the assumptions of `th`, specifically those assumptions for which `f` evaluates to true, combined with the provided list of theorems `thl`. The function `FILTER_ASM_REWRITE_RULE` is similar except that it builds a standard (impure) rewrite rule. The function `FILTER_PURE_ONCE_ASM_REWRITE_RULE` is similar to `FILTER_PURE_ASM_REWRITE_RULE`, except that the rewrite rule is applied only once. The function `FILTER_ONCE_ASM_REWRITE_RULE` is similar to `FILTER_ASM_REWRITE_RULE`, except that the rewrite rule is applied only once.
`ASSUME` constructs a theorem from an assumption. `hyp th` returns the hypothesis of the theorem `th`.

### Informal sketch
The functions constructs rewrite rules from the assumptions of a theorem that satisfy a given filter `f` and applies the resulting rewrite rule to the theorem.
- The assumptions of the theorem `th` are extracted using `hyp th`.
- The assumptions are filtered using the predicate `f`.
- The filtered assumptions are turned into theorems using `ASSUME`.
- The theorems constructed from filtered assumptions are prepended to the list `thl`.
- A rewrite rule is constructed from the combined theorem list (filtered assumptions, plus `thl`).
- The function `FILTER_PURE_ASM_REWRITE_RULE` uses `PURE_REWRITE_RULE` to apply the rewrite rule exhaustively, without using the assumption list; `FILTER_ASM_REWRITE_RULE` uses standard `REWRITE_RULE` that uses the assumption list., `FILTER_PURE_ONCE_ASM_REWRITE_RULE` uses `PURE_ONCE_REWRITE_RULE` to apply the rewrite rule once, without using the assumption list, and `FILTER_ONCE_ASM_REWRITE_RULE` uses `ONCE_REWRITE_RULE` to apply the rewrite rule once that uses the assumption list.

### Mathematical insight
These definitions provides a mechanism for selectively applying rewrite rules based on the assumptions present in a theorem. This is useful for controlling the application of rewrite rules and preventing unwanted or infinite rewriting. The "once" variants provide a way to apply the rewrite rule only once, which can be important for efficiency and correctness. They provide ways to selectively activate assumptions of a theorem to perform rewriting.

### Dependencies
- `ASSUME`
- `hyp`
- `PURE_REWRITE_RULE`
- `REWRITE_RULE`
- `PURE_ONCE_REWRITE_RULE`
- `ONCE_REWRITE_RULE`
- `filter`
- `map`
- `@` (list concatenation)


---

## (FILTER_PURE_ASM_REWRITE_TAC:

### Name of formal statement
FILTER_PURE_ASM_REWRITE_TAC

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (FILTER_PURE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    PURE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_PURE_ONCE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    PURE_ONCE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w)

and (FILTER_ONCE_ASM_REWRITE_TAC: (term->bool) -> thm list -> tactic) =
  fun f thl (asl,w) ->
    ONCE_REWRITE_TAC (filter (f o concl) (map snd asl) @ thl) (asl,w);;
```

### Informal statement
The definitions introduce four tactics: `FILTER_PURE_ASM_REWRITE_TAC`, `FILTER_ASM_REWRITE_TAC`, `FILTER_PURE_ONCE_ASM_REWRITE_TAC`, and `FILTER_ONCE_ASM_REWRITE_TAC`. Each of these tactics takes a filter function `f` (of type `term -> bool`), a list of theorems `thl`, and a goal `(asl, w)` where `asl` is the assumptions list (a list of association pairs) and `w` is the term to be proved. The filter function `f` is used to select assumptions based on the conclusion of each assumption.

- `FILTER_PURE_ASM_REWRITE_TAC f thl (asl, w)` applies `PURE_REWRITE_TAC` to the goal `(asl, w)` using the theorems `thl` concatenated with the list of assumptions from `asl` whose conclusion satisfies the filter `f`.
- `FILTER_ASM_REWRITE_TAC f thl (asl, w)` applies `REWRITE_TAC` to the goal `(asl, w)` using the theorems `thl` concatenated with the list of assumptions from `asl` whose conclusion satisfies the filter `f`.
- `FILTER_PURE_ONCE_ASM_REWRITE_TAC f thl (asl, w)` applies `PURE_ONCE_REWRITE_TAC` to the goal `(asl, w)` using the theorems `thl` concatenated with the list of assumptions from `asl` whose conclusion satisfies the filter `f`.
- `FILTER_ONCE_ASM_REWRITE_TAC f thl (asl, w)` applies `ONCE_REWRITE_TAC` to the goal `(asl, w)` using the theorems `thl` concatenated with the list of assumptions from `asl` whose conclusion satisfies the filter `f`.

### Informal sketch
The tactics construct a list of theorems (given theorems plus filtered assumptions) and then apply a rewriting tactic with this list:

- All four tactics take a filter function `f`, a theorem list `thl`, and a goal in the form `(asl, w)`.
- They extract assumptions from `asl`, mapping each assumption (which is a pair) to its second element (the actual assumption term).
- `filter (f o concl)` applies the filter `f` to the conclusion of each assumption.
- The filtered assumptions list is appended to the given `thl`.
- The resulting theorem list is then given to one of `PURE_REWRITE_TAC`, `REWRITE_TAC`, `PURE_ONCE_REWRITE_TAC`, or `ONCE_REWRITE_TAC` respectively, along with the original goal `(asl, w)`.
- These tactics then rewrite the goal `w` using the given and filtered theorems. The `PURE` variants don't use assumptions and ONCE rewrite only one step

### Mathematical insight
These tactics provide a mechanism to selectively apply rewrite rules based on the form of the assumptions currently in the context. This allows for more controlled application of rewrite rules, potentially avoiding unwanted rewrites or infinite loops. The filter function `f` allows the user to specify a predicate that assumption conclusions must satisfy to be used in rewriting.

### Dependencies
- `PURE_REWRITE_TAC`
- `REWRITE_TAC`
- `PURE_ONCE_REWRITE_TAC`
- `ONCE_REWRITE_TAC`
- `filter`
- `concl`
- `map`

### Porting notes (optional)
The porting of these tactics depends on the availability and behavior of the core rewriting tactics `PURE_REWRITE_TAC`, `REWRITE_TAC`, `PURE_ONCE_REWRITE_TAC`, and `ONCE_REWRITE_TAC` in the target proof assistant. Also the `filter` higher-order function is standard and easy to implement in other systems. The function `concl`, which extracts the conclusion of a theorem, also has a counterpart in other provers but be sure to check the form of the assumptions list.


---

## (X_CASES_THENL:

### Name of formal statement
X_CASES_THENL

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let (X_CASES_THENL: term list list -> thm_tactic list -> thm_tactic) =
  fun varsl ttacl ->
    end_itlist DISJ_CASES_THEN2
       (map (fun (vars,ttac) -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac)
        (zip varsl ttacl));;
```

### Informal statement
The function `X_CASES_THENL` takes a list of lists of terms `varsl` and a list of theorem tactics `ttacl` as input, where the length of `varsl` and `ttacl` are equal. It returns a theorem tactic which is constructed by the following process: First, zip the list `varsl` and the list `ttacl` into a single list of pairs. Then map over this list of pairs applying the function that maps a pair `(vars, ttac)` to the tactic `EVERY_TCL (map X_CHOOSE_THEN vars) ttac`. Finally, fold this list of tactics together using `end_itlist DISJ_CASES_THEN2`, which applies `DISJ_CASES_THEN2` between each tactic in the list.

### Informal sketch
The tactic `X_CASES_THENL` implements a form of case splitting.

- The input consists of a list of term lists `varsl = [[t11, ..., t1n1], ..., [tk1, ..., tknk]]` and a corresponding list of tactics `ttacl = [tac1, ..., tack]`.
- The zipping operation associates each sublist of terms `[ti1, ..., tin]` with a tactic `taci`.
- The `map (fun (vars,ttac) -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac)` part applies a tactic to each sublist of terms. In particular, given `[ti1, ..., tin]` and `taci`, it constructs a tactic that first applies `X_CHOOSE_THEN` to each term `tij` in the sublist, and then applies `EVERY_TCL` to the resulting list of tactics and the tactic `taci`.
- `end_itlist DISJ_CASES_THEN2` then threads the tactics together using `DISJ_CASES_THEN2` which performs a disjunctive case split for each tactic produced in the mapping applied above.

### Mathematical insight
The `X_CASES_THENL` tactic is a generalization of case splitting on multiple different sets of variables. It allows applying a specific tactic after performing case splits on a given set of terms. This is particularly useful when dealing with multiple hypotheses or variables that require different case analysis strategies.

### Dependencies
- `DISJ_CASES_THEN2`
- `X_CHOOSE_THEN`
- `EVERY_TCL`
- `zip`
- `map`
- `end_itlist`


---

## (X_CASES_THEN:

### Name of formal statement
`X_CASES_THEN`

### Type of the formal statement
Definition

### Formal Content
```ocaml
let (X_CASES_THEN: term list list -> thm_tactical) =
  fun varsl ttac ->
    end_itlist DISJ_CASES_THEN2
       (map (fun vars -> EVERY_TCL (map X_CHOOSE_THEN vars) ttac) varsl);;
```

### Informal statement
The function `X_CASES_THEN` takes a list of list of terms `varsl` and a theorem tactical `ttac` as input. It maps each list of terms `vars` in `varsl` to the application of theorem tactical `ttac` after iteratively choosing each term within `vars` using the tactic `X_CHOOSE_THEN`. Then it iterates through this list of derived tactics using `DISJ_CASES_THEN2`.

### Informal sketch
The tactic `X_CASES_THEN` is defined as follows:
- Given a list of term lists `varsl` and a theorem tactical `ttac`.
- Map over the list of term lists `varsl`, and for each list of terms `vars`, apply the tactical `EVERY_TCL` which applies the `X_CHOOSE_THEN` tactic to each term in `vars`, followed by applying `ttac`. This generates a list of tactics.
- Fold this list of tactics together using `end_itlist DISJ_CASES_THEN2`, where `DISJ_CASES_THEN2` is a tactical that performs case splits.

### Mathematical insight
This definition constructs a tactic that performs iterated case splits on a list of lists of terms. It essentially automates the process of applying a tactical `ttac` after performing case analysis on each term in each sublist of a given list of lists `varsl`. The tactic attempts to prove the goal by considering all possible cases arising from each term of each sublist in `varsl`.

### Dependencies
- `DISJ_CASES_THEN2`
- `X_CHOOSE_THEN`
- `end_itlist`
- `EVERY_TCL`
- `map`


---

## (CASES_THENL:

### Name of formal statement
CASES_THENL

### Type of the formal statement
Definition

### Formal Content
```ocaml
let (CASES_THENL: thm_tactic list -> thm_tactic) =
  fun ttacl -> end_itlist DISJ_CASES_THEN2 (map (REPEAT_TCL CHOOSE_THEN) ttacl);;
```

### Informal statement
The function `CASES_THENL` takes a list of theorem tactics `ttacl` and produces another theorem tactic.
The resulting theorem tactic is constructed by mapping each theorem tactic in `ttacl` to a tactic which repeats `CHOOSE_THEN` until it fails (using `REPEAT_TCL`), applying `DISJ_CASES_THEN2` to each of the resulting tactics, and combining the results using `end_itlist`.

### Informal sketch
*   The `CASES_THENL` tactic takes a list of tactics that perform case splits. The intention is to split the current goal into subgoals, each corresponding to the case handled by one of tactics in the input list.
*   `REPEAT_TCL CHOOSE_THEN` applies `CHOOSE_THEN` repeatedly to a goal until `CHOOSE_THEN` fails. `CHOOSE_THEN` likely performs some kind of choice, until no further choice is possible. The purpose is to fully expand alternatives in each case before applying a case-splitting tactic.
*   `map (REPEAT_TCL CHOOSE_THEN) ttacl` applies `REPEAT_TCL CHOOSE_THEN` to each tactic in the input list `ttacl`.
*   `DISJ_CASES_THEN2` transforms a tactic that proves `A |- B \/ C` into a tactic that splits the goal into two subgoals, `A |- B` and `A |- C`. It applies to a list of tactics; it splits each theorem in the list into cases. Applying the tactic `DISJ_CASES_THEN2` corresponds to a case split based on a disjunction. It turns a theorem of the form `|- A \/ B` into a tactic for splitting the current goal into assuming `A` or assuming `B`.
*   `end_itlist DISJ_CASES_THEN2` then combines the sequence of tactics produced by the map, into a single tactic by repeated application of `DISJ_CASES_THEN2`: sequentially performs case splits.

### Mathematical insight
The tactic `CASES_THENL` provides means for combining multiple tactics responsible for performing case splits, to handle complex scenarios by decomposing them into simpler disjoint cases. This is a standard procedure employed to manage the complexity of proofs involving disjunctions.

### Dependencies
* `CHOOSE_THEN`
* `REPEAT_TCL`
* `DISJ_CASES_THEN2`
* `end_itlist`

### Porting notes (optional)
The main difficulty in porting this definition will arise from the specific tactics used: `CHOOSE_THEN` and `DISJ_CASES_THEN2`. These will have to be implemented in the target proof assistant (or suitable equivalents found). The `end_itlist` function is just a fold with tactic composition, which is itself a standard concept available in most proof assistants. Ensure the interaction between `REPEAT_TCL` and `CHOOSE_THEN` is reproduced correctly to achieve the intended iterative refinement of cases.


---

## (DISCARD_TAC:

### Name of formal statement
`DISCARD_TAC`

### Type of the formal statement
Theorem Tactic Definition

### Formal Content
```ocaml
let (DISCARD_TAC: thm_tactic) =
  let truth = `T` in
  fun th (asl,w) ->
    if exists (aconv (concl th)) (truth::(map (concl o snd) asl))
    then ALL_TAC (asl,w)
    else failwith "DISCARD_TAC";;
```

### Informal statement
The theorem tactic `DISCARD_TAC` is defined as follows: given a theorem `th` and a goal consisting of a list of assumptions `asl` and a term `w` to be proved, if the conclusion of `th` is alpha-convertible to the term `T` (representing truth) or to the conclusion of any assumption in `asl`, then apply the `ALL_TAC` tactic. Otherwise, the tactic fails with the message "DISCARD_TAC".

### Informal sketch
- The tactic `DISCARD_TAC` takes a theorem `th` and a goal state `(asl, w)` as input.
- It checks if the conclusion of `th` (the statement that `th` proves) matches `T` or the conclusion of any assumption in the assumption list `asl` modulo alpha-conversion.
- If a match is found, the tactic applies `ALL_TAC` to the goal. The `ALL_TAC` tactic solves the goal unconditionally by doing nothing.
- If no match is found, the tactic fails with the string "DISCARD_TAC".

### Mathematical insight
The tactic `DISCARD_TAC` is useful for discharging trivial subgoals that are either trivially true (`T`) or are already present as assumptions. It provides a simple check to prevent more complex tactics from being applied to goals which are trivially true or contradictory to the assumptions.

### Dependencies
- `T`
- `aconv`
- `concl`
- `exists`
- `ALL_TAC`


---

## (CHECK_ASSUME_TAC:

### Name of formal statement
CHECK_ASSUME_TAC

### Type of the formal statement
Definition (of a tactic)

### Formal Content
```ocaml
let (CHECK_ASSUME_TAC: thm_tactic) =
  fun gth ->
    FIRST [CONTR_TAC gth;  ACCEPT_TAC gth;
           DISCARD_TAC gth; ASSUME_TAC gth];;
```

### Informal statement
The tactic `CHECK_ASSUME_TAC` is defined as a tactic that, given a goal `gth`, attempts the following tactics in order, until one succeeds: `CONTR_TAC gth`, `ACCEPT_TAC gth`, `DISCARD_TAC gth`, `ASSUME_TAC gth`.

### Informal sketch
The tactic `CHECK_ASSUME_TAC` is defined to try a sequence of tactics on a goal. Specifically:
- First, it tries `CONTR_TAC gth`, which attempts to prove the goal by contradiction (finding `F` in the assumptions).
- If `CONTR_TAC gth` fails, it then tries `ACCEPT_TAC gth`, which immediately solves the goal without further proof. This is typically used for trivial or easily verifiable goals.
- If `ACCEPT_TAC gth` fails, it then tries `DISCARD_TAC gth`, which also immediately solves the goal without further proof (as ACCEPT_TAC).
- If `DISCARD_TAC gth` fails, it attempts to solve the goal using `ASSUME_TAC gth`, which tries to find the top term of the goal in the assumptions.

### Mathematical insight
This tactic is a simple but useful utility for automating the handling of trivial goals within larger proofs. It provides a structured approach to eliminate goals that can be solved by contradiction, immediate acceptance, immediate discarding, or direct assumption. the `FIRST` combinator is like `orelse` for tactics, and tries each until one succeeds.

### Dependencies
- `CONTR_TAC`
- `ACCEPT_TAC`
- `DISCARD_TAC`
- `ASSUME_TAC`
- `FIRST`

### Porting notes (optional)
The core concept of trying tactics in sequence until one succeeds is common across many proof assistants. Most systems have equivalents of `CONTR_TAC` and `ASSUME_TAC`. `ACCEPT_TAC`, and `DISCARD_TAC` can be emulated with a basic `trivial` tactics (e.g., `auto 0` in Isabelle). The `FIRST` combinator may need to be recreated if a similar tactic combinator does not exist in the other proof assistant.


---

## (FILTER_GEN_TAC:

### Name of formal statement
FILTER_GEN_TAC

### Type of the formal statement
Tactic Definition

### Formal Content
```ocaml
let (FILTER_GEN_TAC: term -> tactic) =
  fun tm (asl,w) ->
    if is_forall w && not (tm = fst(dest_forall w)) then
        GEN_TAC (asl,w)
    else failwith "FILTER_GEN_TAC";;
```

### Informal statement
The function `FILTER_GEN_TAC` takes a term `tm` and a goal `(asl, w)` consisting of an assumption list `asl` and a formula `w`. It checks if `w` is a universally quantified formula and if the term `tm` is not equal to the bound variable of the universal quantifier in `w`. If both conditions are true, it applies the tactic `GEN_TAC` to the goal `(asl, w)`. Otherwise, it fails with the message "FILTER_GEN_TAC".

### Informal sketch
The tactic `FILTER_GEN_TAC` attempts to discharge a universally quantified goal using `GEN_TAC`, but only if the specified term `tm` is *not* the variable being generalized.

- Check if the current goal `w` is a universally quantified formula using `is_forall`.
- Check if the term `tm` is different from the variable being quantified over in `w`. This is achieved by extracting the quantified variable using `fst(dest_forall w)` and comparing it with `tm`.
- If both conditions are met, apply `GEN_TAC` to the goal `(asl, w)`.
- If either condition fails, the tactic fails.

### Mathematical insight
The `FILTER_GEN_TAC` provides a mechanism for conditional generalization, where the generalization tactic `GEN_TAC` is applied only when the term being considered is *not* the quantified variable. This allows for more controlled introduction of assumptions and prevents unwanted generalizations. It is useful when the quantified variable has a specific role and shouldn't be generalized over.

### Dependencies
- `is_forall`
- `dest_forall`
- `GEN_TAC`


---

## (FILTER_DISCH_THEN:

### Name of formal statement
FILTER_DISCH_THEN

### Type of the formal statement
Definition

### Formal Content
```ocaml
let (FILTER_DISCH_THEN: thm_tactic -> term -> tactic) =
  fun ttac tm (asl,w) ->
    if is_neg_imp w && not (free_in tm (fst(dest_neg_imp w))) then
      DISCH_THEN ttac (asl,w)
    else failwith "FILTER_DISCH_THEN";;
```

### Informal statement
`FILTER_DISCH_THEN` is a function that takes a theorem tactic `ttac` and a term `tm` and returns a tactic. Given a goal consisting of assumptions `asl` and a term `w` to prove, if `w` is a negation of an implication, and the term `tm` is not free in the antecedent of the implication, then it applies the tactic `DISCH_THEN ttac` to the goal. Otherwise, it fails.

### Informal sketch
The function `FILTER_DISCH_THEN` combines a filter with the `DISCH_THEN` tactic.

- The function first checks if the term to be proved, `w`, is a negation of an implication. In HOL Light notation, this means `is_neg_imp w` evaluates to true, meaning `w` is of the form `¬(p ==> q)`.

- If it is, the function then checks if the term `tm` is free in the antecedent, `p`, of the implication i.e., `not (free_in tm p)`.

- If both of the above conditions hold, the tactic `DISCH_THEN ttac` is applied to the goal `(asl, w)`. The `DISCH_THEN` tactic discharges the antecedent of the implication as an assumption, and then applies `ttac` to the resulting goal.

- If either of the conditions fail, the function `failwith "FILTER_DISCH_THEN"` is executed, resulting in the tactic failing.

### Mathematical insight
The function `FILTER_DISCH_THEN` is useful in situations where one wants to discharge the antecedent of a negated implication using `DISCH_THEN`, but only if a certain term is not free in the antecedent. This is a common pattern when applying tactics selectively based on the structure of the goal and properties of terms within it. It prevents unwanted discharge and application of `ttac` if `tm` is free in the antecedent.

### Dependencies
- `is_neg_imp`
- `free_in`
- `dest_neg_imp`
- `DISCH_THEN`

### Porting notes (optional)
The function `FILTER_DISCH_THEN` combines filtering conditions with tactic application. Other proof assistants often provide mechanisms for combining tactics with conditional checks to achieve similar behavior. For instance, in Lean, one might use `guard` in conjunction with tactic combinators. The key is to replicate the structure test (`is_neg_imp`) and the free variable check (`free_in`) within the tactic.


---

## FILTER_STRIP_THEN

### Name of formal statement
FILTER_STRIP_THEN

### Type of the formal statement
Definition

### Formal Content
```ocaml
let FILTER_STRIP_THEN ttac tm =
  FIRST [FILTER_GEN_TAC tm; FILTER_DISCH_THEN ttac tm; CONJ_TAC];;
```

### Informal statement
The function `FILTER_STRIP_THEN` takes a tactic `ttac` and a term `tm` as input. It applies the first tactic that succeeds from the list `[FILTER_GEN_TAC tm; FILTER_DISCH_THEN ttac tm; CONJ_TAC]`.

### Informal sketch
The function `FILTER_STRIP_THEN ttac tm` attempts three tactics in sequence:
- First, it tries `FILTER_GEN_TAC tm`, which likely tries to apply generalization based on the form of `tm`.
- If that fails, it tries `FILTER_DISCH_THEN ttac tm`, which likely discharges assumptions based on the properties of `tm`, and then applies the tactic `ttac` to the resulting goal.
- If both of the tactics above fail, it applies `CONJ_TAC`, which splits the goal if it's a conjunction.

### Mathematical insight
This function provides a way to strategically apply tactics based on the structure of the current goal. It's designed to handle common goal structures effectively. It first attempts to generalize, then discharge assumptions, and finally split conjunctions if those are present. The use of `FIRST` ensures that only one of these three tactics is applied, providing a structured approach to goal reduction.

### Dependencies
- `FIRST`
- `FILTER_GEN_TAC`
- `FILTER_DISCH_THEN`
- `CONJ_TAC`


---

## FILTER_DISCH_TAC

### Name of formal statement
FILTER_DISCH_TAC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FILTER_DISCH_TAC = FILTER_DISCH_THEN STRIP_ASSUME_TAC;;
```

### Informal statement
The tactic `FILTER_DISCH_TAC` is defined as the tactic `FILTER_DISCH_THEN` followed by the tactic `STRIP_ASSUME_TAC`.

### Informal sketch
- The tactic `FILTER_DISCH_TAC` is constructed by combining two existing tactics.
- First, the `FILTER_DISCH_THEN` tactic is applied. This tactic likely discharges assumptions based on a filtering criterion.
- Subsequently, `STRIP_ASSUME_TAC` is applied, which performs assumption stripping. This tactic typically simplifies or removes assumptions in the goal.

### Mathematical insight
This definition creates a new tactic by composing existing tactics. The purpose is likely to combine the assumption-discharging capabilities of `FILTER_DISCH_THEN` with the simplification or cleanup provided by `STRIP_ASSUME_TAC`, resulting in a more effective or streamlined tactic for proving theorems.

### Dependencies
- Tactics: `FILTER_DISCH_THEN`, `STRIP_ASSUME_TAC`


---

## FILTER_STRIP_TAC

### Name of formal statement
FILTER_STRIP_TAC

### Type of the formal statement
Theorem proving tactic

### Formal Content
```ocaml
let FILTER_STRIP_TAC = FILTER_STRIP_THEN STRIP_ASSUME_TAC;;
```

### Informal statement
The tactic `FILTER_STRIP_TAC` is defined as the sequential application of the tactic `FILTER_STRIP_THEN` followed by the tactic `STRIP_ASSUME_TAC`.

### Informal sketch
The tactic `FILTER_STRIP_TAC` is a composed tactic:
- First step: apply `FILTER_STRIP_THEN` tactic. This tactic likely filters and modifies the current goal using some striping mechanism like removing redundant assumptions.
- Second step: apply `STRIP_ASSUME_TAC` tactic. This tactic probably strips the assumptions of the goal, potentially simplifying them.

### Mathematical insight
This tactic seems to be designed for simplifying and cleaning up the assumptions of a goal during theorem proving. The combination of `FILTER_STRIP_THEN` and `STRIP_ASSUME_TAC` suggests a multi-stage process: first, filter out certain irrelevant or redundant parts of the current goal using `FILTER_STRIP_THEN`, then strip the goal's assumptions using `STRIP_ASSUME_TAC`. This sequential application of these two tactics enhances the effectiveness of automated proof search by streamlining the target context.

### Dependencies
- `FILTER_STRIP_THEN`
- `STRIP_ASSUME_TAC`


---

## RES_CANON

### Name of formal statement
RES_CANON

### Type of the formal statement
Definition

### Formal Content
```ocaml
let RES_CANON =
    let not_elim th =
      if is_neg (concl th) then true,(NOT_ELIM th) else (false,th) in
    let rec canon fl th =
       let w = concl th in
       if (is_conj w) then
          let (th1,th2) = CONJ_PAIR th in (canon fl th1) @ (canon fl th2) else
       if ((is_imp w) && not(is_neg w)) then
          let ante,conc = dest_neg_imp w in
          if (is_conj ante) then
             let a,b = dest_conj ante in
             let cth = NOT_MP th (CONJ (ASSUME a) (ASSUME b)) in
             let th1 = DISCH b cth and th2 = DISCH a cth in
                 (canon true (DISCH a th1)) @ (canon true (DISCH b th2)) else
          if (is_disj ante) then
             let a,b = dest_disj ante in
             let ath = DISJ1 (ASSUME a) b and bth = DISJ2 a (ASSUME b) in
             let th1 = DISCH a (NOT_MP th ath) and
                 th2 = DISCH b (NOT_MP th bth) in
                 (canon true th1) @ (canon true th2) else
          if (is_exists ante) then
             let v,body = dest_exists ante in
             let newv = variant (thm_frees th) v in
             let newa = subst [newv,v] body in
             let th1 = NOT_MP th (EXISTS (ante, newv) (ASSUME newa)) in
                 canon true (DISCH newa th1) else
             map (GEN_ALL o (DISCH ante)) (canon true (UNDISCH th)) else
       if (is_eq w && (type_of (rand w) = `:bool`)) then
          let (th1,th2) = EQ_IMP_RULE th in
          (if fl then [GEN_ALL th] else []) @ (canon true th1) @ (canon true th2) else
       if (is_forall w) then
           let vs,body = strip_forall w in
           let fvs = thm_frees th in
           let vfn = fun l -> variant (l @ fvs) in
           let nvs = itlist (fun v nv -> let v' = vfn nv v in (v'::nv)) vs [] in
               canon fl (SPECL nvs th) else
       if fl then [GEN_ALL th] else [] in
    fun th -> try let args = map (not_elim o SPEC_ALL) (CONJUNCTS (SPEC_ALL th)) in
                  let imps = flat (map (map GEN_ALL o (uncurry canon)) args) in
                  check (fun l -> l <> []) imps
              with Failure _ ->
                failwith "RES_CANON: no implication is derivable from input thm.";;
```

### Informal statement
The function `RES_CANON` takes a theorem `th` as input and attempts to derive a list of theorems representing the canonical form of implications derivable from the input theorem. First, the function `RES_CANON` applies `SPEC_ALL` to the input theorem `th` and splits the resulting conjunction into individual conjuncts. It then applies `not_elim` and `SPEC_ALL` on each of these conjuncts. The `not_elim` function converts each conjunct into an equivalent negated form if the conclusion of the conjunct is in the form of a negation. The theorems are then processed using the recursive function `canon`, which transforms the theorem based on the logical structure of its conclusion.
The function `canon` takes a boolean flag `fl` and a theorem `th` as input and returns a list of theorems. If the conclusion of `th` is a conjunction, the function splits the theorem using `CONJ_PAIR` into left and right conjuncts `th1` and `th2`, and then recursively calls `canon` on each of them, concatenating the resulting lists. If the conclusion is an implication and not a negation, and the antecedent is a conjunction, the function decomposes the antecedent into its conjuncts `a` and `b`, and constructs a new theorem using `NOT_MP` and `CONJ`. It then discharges `b` and `a` respectively, creating two new theorems `th1` and `th2`, and recursively calls `canon` on each of them. The `canon` also processes implications with disjunctive or existentially quantified antecedents similarly, using `DISJ1`, `DISJ2`, `EXISTS`, and `UNDISCH` appropriately. If the conclusion is an equality of booleans, the function applies `EQ_IMP_RULE` to obtain two implications `th1` and `th2`. Depending on the flag `fl`, it may generalize the original theorem using `GEN_ALL`. It then recursively calls `canon` on the generated implications. If the conclusion is a universal quantification, the function specializes the theorem using `SPECL` with fresh variables, and recursively calls `canon` on the specialized theorem. The final result is a list of theorems obtained from transforming implications.
If all the implications cannot be converted into canonical form, then `RES_CANON` fails.

### Informal sketch
The `RES_CANON` function transforms a theorem by repeatedly breaking down its structure and deriving canonical implications from it.
- The function processes a theorem `th` by first specializing it and splitting it into conjuncts via `SPEC_ALL` and `CONJUNCTS`.
- Each conjunct is checked to determine if its conclusion is a negation; if it is not, the equivalent negation via `NOT_ELIM` is used.
- A recursive function `canon` is used to transform the theorem depending on the structure of its conclusion.
  - If the conclusion is a conjunction, recursively apply the function to the theorems representing each conjunct (`canon fl th1` and `canon fl th2`), and concatenate the resulting lists.
  - If the conclusion is an implication (and not a negation):
    - If the antecedent is a conjunction `a /\ b`, use `NOT_MP` to derive consequences and discharge `a` and `b` to generate two new theorems via `DISCH`, and then recurse with these new theorems.
    - If the antecedent is a disjunction `a \/ b`, use `NOT_MP`, `DISJ1`, and `DISJ2` to derive consequences and discharge `a` and `b` to generate two new theorems via `DISCH`, and then recurse with these new theorems.
    - If the antecedent is an existential quantification `EXISTS v, body`, specialize the theorem with a fresh variable and recurse using `DISCH`.
    - Otherwise, generalize the theorem and revert specialization using `UNDISCH`, then recurse.
  - If the conclusion is an equality between boolean terms, convert to implications using `EQ_IMP_RULE` and recurse.
  - If the conclusion is a universal quantification, specialize it with fresh variables generated by `variant` using `SPECL` and recurse with specialized result.
  - If the flag `fl` is true, generalize the theorem using `GEN_ALL`.
- The `RES_CANON` function also wraps the process in a `try...with` block to catch failures if no implications can be derived.

### Mathematical insight
The `RES_CANON` function is designed to transform a theorem into a set of canonical implications. This process involves breaking down the theorem into its constituent parts based on the logical connectives (conjunction, implication, disjunction, existential quantifiers, and boolean equality) in its conclusion, and recursively processing these parts to derive implications in a standard form suitable for resolution-based theorem proving. The canonical form helps to standardize the theorem for use in automated reasoning and facilitates quantifier movement. The use of `variant` ensures that fresh variables are used during specialization of universal quantifiers, preventing variable capture.

### Dependencies
- `NOT_ELIM`
- `CONJ_PAIR`
- `dest_neg_imp`
- `dest_conj`
- `NOT_MP`
- `CONJ`
- `ASSUME`
- `DISCH`
- `dest_disj`
- `DISJ1`
- `DISJ2`
- `dest_exists`
- `variant`
- `subst`
- `EXISTS`
- `UNDISCH`
- `EQ_IMP_RULE`
- `strip_forall`
- `thm_frees`
- `SPECL`
- `GEN_ALL`
- `SPEC_ALL`
- `CONJUNCTS`
- `check`

### Porting notes (optional)
- The extensive use of HOL Light's term and theorem manipulation functions (e.g., `is_conj`, `dest_conj`, `CONJ`, `DISCH`, `SPEC_ALL`, etc.) will require careful translation into corresponding functions or tactics of other proof assistants.
- The `variant` function, used to generate fresh variable names, is important for preventing variable capture during specialization of quantifiers. Ensure that the target proof assistant provides a similar mechanism.
- The function implicitly relies on the properties of the underlying logic, like the equivalence between `A -> B` and `~A \/ B`.
- The `try ... with` block should translate straightforwardly into exception handling mechanisms present in most proof assistants.


---

## IMP_RES_THEN,RES_THEN

### Name of formal statement
IMP_RES_THEN,RES_THEN

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let IMP_RES_THEN,RES_THEN =
  let MATCH_MP impth =
      let sth = SPEC_ALL impth in
      let matchfn = (fun (a,b,c) -> b,c) o
                    term_match [] (fst(dest_neg_imp(concl sth))) in
         fun th -> NOT_MP (INST_TY_TERM (matchfn (concl th)) sth) th in
  let check st l = (if l = [] then failwith st else l) in
  let IMP_RES_THEN ttac impth =
      let ths = try RES_CANON impth with Failure _ -> failwith "IMP_RES_THEN: no implication" in
      ASSUM_LIST
       (fun asl ->
        let l = itlist (fun th -> (@) (mapfilter (MATCH_MP th) asl)) ths [] in
        let res = check "IMP_RES_THEN: no resolvents " l in
        let tacs = check "IMP_RES_THEN: no tactics" (mapfilter ttac res) in
        EVERY tacs) in
  let RES_THEN ttac (asl,g) =
      let asm = map snd asl in
      let ths = itlist (@) (mapfilter RES_CANON asm) [] in
      let imps = check "RES_THEN: no implication" ths in
      let l = itlist (fun th -> (@) (mapfilter (MATCH_MP th) asm)) imps [] in
      let res = check "RES_THEN: no resolvents " l in
      let tacs = check "RES_THEN: no tactics" (mapfilter ttac res) in
          EVERY tacs (asl,g) in
  IMP_RES_THEN,RES_THEN;;
```

### Informal statement
The definition introduces two tactics combinators: `IMP_RES_THEN` and `RES_THEN`.

`IMP_RES_THEN` takes a tactic `ttac` and a theorem `impth` representing an implication. It transforms the implication into canonical form using `RES_CANON`. Given an assumption list `asl`, it attempts to resolve each theorem in the canonicalized implication with theorems in the assumption list `asl` using `MATCH_MP`. It filters the results to find the successful resolutions and then applies the tactic `ttac` to each of the resolvents. Finally, it combines the resulting subgoals using the `EVERY` tactic.

`RES_THEN` takes a tactic `ttac` and a goal represented by an assumption list `asl` paired with a goal term `g`. It extracts the assumptions from `asl`, applies `RES_CANON` to each assumption and collects the resulting implication theorems. It resolves these implication theorems with assumptions from `asl` using `MATCH_MP` and filters for successful resolutions. It then applies `ttac` to each resolvent and combines the resulting tactics using `EVERY`.

### Informal sketch
The definition constructs two tactic combinators related to resolution:

- `MATCH_MP`: This internal function takes a theorem `impth` which is expected to be an implication. It finds substitutions that, when applied to the antecedent of `impth`, make it match the conclusion of another theorem `th`. It returns the result of applying the instantiation of `impth` with the computed substitution and then applying `NOT_MP` to derive the consequent.
- `IMP_RES_THEN`:
  - Convert the implication theorem `impth` to canonical form using `RES_CANON`.
  - Apply `MATCH_MP` to each canonicalized implication and each assumption in the assumption list `asl` to find resolvents.
  - Apply the tactic `ttac` to each resolvent.
  - Combine the resulting tactics using `EVERY`.
- `RES_THEN`:
  - Extract the assumptions from assumption list `asl`.
  - Convert each assumption to canonical form using `RES_CANON`, collecting the results.
  - Apply `MATCH_MP` to each implication theorem and each assumption to find resolvents.
  - Apply the tactic `ttac` to each resolvent.
  - Combine the resulting tactics using `EVERY`.

The purpose is to automate the resolution process, where the given tactic will be applied at each resolution step.

### Mathematical insight
These tactic combinators provide ways to automate resolution inferences within the HOL Light theorem prover. `IMP_RES_THEN` performs a resolution inference using a given implication theorem. `RES_THEN` works similarly, but begins by canonicalizing the assumptions in the goal. The canonicalization step transforms assumptions into a format suitable for resolution, and `MATCH_MP` compares the assumptions to the implication to perform resolution.

### Dependencies
- Theorems:
  - `SPEC_ALL`
- Definitions:
  - `dest_neg_imp`
  - `term_match`
  - `NOT_MP`
  - `INST_TY_TERM`
  - `RES_CANON`
  - `ASSUM_LIST`
  - `EVERY`
  - `mapfilter`


---

## IMP_RES_TAC

### Name of formal statement
IMP_RES_TAC

### Type of the formal statement
Tactical

### Formal Content
```ocaml
let IMP_RES_TAC th g =
  try IMP_RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) th g
  with Failure _ -> ALL_TAC g;;
```

### Informal statement
The tactical `IMP_RES_TAC` takes a theorem `th` and a goal `g` as input. It attempts to resolve the theorem `th` against the goal `g` after repeatedly resolving implications and stripping assumptions. If this attempt succeeds, the resulting subgoal is returned. If the attempt fails, then it applies the `ALL_TAC` tactic, which trivially satisfies the goal, resulting in no subgoals.

### Informal sketch
- Attempt to apply `IMP_RES_THEN` after preprocessing the goal `g`.
- The preprocessing step `REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC` consists of repeatedly applying `IMP_RES_THEN` to resolve any implications introduced by the goal and then stripping any assumptions using `STRIP_ASSUME_TAC`.
- If the resolution succeeds, then the result of `IMP_RES_THEN` is returned as the new goal.
- If the resolution fails (i.e., the goal cannot be solved by resolving and stripping), the tactic `ALL_TAC` is applied, which solves the goal trivially with no subgoals.

### Mathematical insight
The tactical `IMP_RES_TAC` is used to attempt to automatically resolve a given theorem against a goal. It combines implication resolution with assumption stripping to simplify the goal before the resolution. If resolution fails, it solves the goal trivially. This tactic provides an automatic approach to discharging goals based on implication resolution. The tactic prioritizes simplification and resolution over failing.

### Dependencies
- `IMP_RES_THEN `
- `REPEAT_GTCL`
- `STRIP_ASSUME_TAC`
- `ALL_TAC`

### Porting notes (optional)
- The behavior of the `try ... with Failure _ -> ...` construct should be noted, as different proof assistants may have differing ways of handling exceptions and tactic failure.
- `REPEAT_GTCL` corresponds to the `repeat` tactic modifier


---

## RES_TAC

### Name of formal statement
RES_TAC

### Type of the formal statement
Tactical Definition

### Formal Content
```ocaml
let RES_TAC g =
  try RES_THEN (REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC) g
  with Failure _ -> ALL_TAC g;;
```

### Informal statement
The tactic `RES_TAC` applied to a goal `g` attempts to apply resolution repeatedly to the assumptions of the goal. If resolution fails, then the tactic `ALL_TAC` is applied to the goal `g`. More precisely, the tactic `RES_TAC` first attempts to apply `RES_THEN` to `g` using the tactic `REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC`. If this application results in a failure, then `RES_TAC` applies `ALL_TAC` to `g`.

### Informal sketch
The tactic `RES_TAC` is a goal tactic that repeatedly applies resolution to a goal and its assumptions.
- The main strategy consists of attempting to resolve the goal against its assumptions, and iteratively simplifying the assumptions using `STRIP_ASSUME_TAC`.
- The `REPEAT_GTCL IMP_RES_THEN STRIP_ASSUME_TAC` part applies implication resolution (`IMP_RES_THEN`) repeatedly. `STRIP_ASSUME_TAC` likely simplifies the assumptions by stripping away implications and other connectives.
- The `try ... with Failure _ -> ALL_TAC g` construct handles cases where the repeated resolution fails. In such cases, it falls back to `ALL_TAC`, which discharges the goal trivially if it's already true, or does nothing if it is not.

### Mathematical insight
This tactic automates resolution, a fundamental inference rule in logic. It attempts to derive a contradiction, simplifying the goal or proving it directly. The error handling mechanism ensures that the tactic doesn't get stuck indefinitely. The tactic embodies a common problem-solving approach: try a powerful method, and if it fails, resort to a trivial tactic as a fallback.

### Dependencies
- `RES_THEN`
- `REPEAT_GTCL`
- `IMP_RES_THEN`
- `STRIP_ASSUME_TAC`
- `ALL_TAC`

### Porting notes (optional)
The `try ... with Failure _ -> ...` construct may need adaptation depending on the target proof assistant's exception handling mechanisms. The specific behaviors of `RES_THEN`, `REPEAT_GTCL`, `IMP_RES_THEN` and `STRIP_ASSUME_TAC` need to be carefully considered when porting this tactic, as resolution and assumption management may be handled differently in different systems.


---

## prove_rep_fn_one_one

### Name of formal statement
prove_rep_fn_one_one

### Type of the formal statement
theorem

### Formal Content
```ocaml
let prove_rep_fn_one_one th =
  try let thm = CONJUNCT1 th in
      let A,R = (I F_F rator) (dest_comb(lhs(snd(dest_forall(concl thm))))) in
      let _,[aty;rty] = dest_type (type_of R) in
      let a = mk_primed_var("a",aty) in let a' = variant [a] a' in
      let a_eq_a' = mk_eq(a,a') and
          Ra_eq_Ra' = mk_eq(mk_comb(R,a),mk_comb (R,a')) in
      let th1 = AP_TERM A (ASSUME Ra_eq_Ra') in
      let ga1 = genvar aty and ga2 = genvar aty in
      let th2 = SUBST [SPEC a thm,ga1;SPEC a' thm,ga2] (mk_eq(ga1,ga2)) th1 in
      let th3 = DISCH a_eq_a' (AP_TERM R (ASSUME a_eq_a')) in
          GEN a (GEN a' (IMP_ANTISYM_RULE (DISCH Ra_eq_Ra' th2) th3))
  with Failure _ -> failwith "prove_rep_fn_one_one";;
```

### Informal statement
Given a theorem `th` stating that a function `R` is a representation function for a type `A`, meaning that it maps elements of a concrete type to the abstract type `A`, prove that this representation function `R` is one-to-one.
Formally, given `th : !A. (R:concrete_type->A) $ map_representation A R`, prove `!a a'. R a = R a' ==> a = a'`.

### Informal sketch
The proof proceeds as follows:
- First, extract the representation map theorem `thm` from the input theorem `th`.
- Extract the representation function `R` from the representation map theorem `thm`.
- Let `a` and `a'` be variables of the input type to `R`.
- Assume `R a = R a'`.
- Apply the abstraction function `A` (the inverse of `R`) to `R a = R a'` to get `A (R a) = A (R a')`.
- Instantiate the representation map theorem `thm` with `a` and `a'` and substitute the result `A (R a) = A (R a')`, ultimately proving `a=a'`.
- Use implication introduction (discharge) to derive `R a = R a' ==> a = a'`.
- Generalize to show `!a a'. R a = R a' ==> a = a'`.
- Finally, apply `IMP_ANTISYM_RULE` to prove equality

### Mathematical insight
This theorem states an important property of representation functions: they are injective. This is crucial when defining abstract types, as it ensures that distinct concrete representations map to distinct abstract values. Therefore, the representation function allows retrieving a unique element of the concrete type that corresponds to a specific abstract value.

### Dependencies
- `CONJUNCT1`
- `dest_comb`
- `lhs`
- `snd`
- `dest_forall`
- `dest_type`
- `type_of`
- `mk_primed_var`
- `variant`
- `mk_eq`
- `mk_comb`
- `AP_TERM`
- `ASSUME`
- `genvar`
- `SUBST`
- `SPEC`
- `DISCH`
- `GEN`
- `IMP_ANTISYM_RULE`


---

## prove_rep_fn_onto

### Name of formal statement
prove_rep_fn_onto

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let prove_rep_fn_onto th =
  try let [th1;th2] = CONJUNCTS th in
      let r,eq = (I F_F rhs)(dest_forall(concl th2)) in
      let RE,ar = dest_comb(lhs eq) and
          sr = (mk_eq o (fun (x,y) -> y,x) o dest_eq) eq in
      let a = mk_primed_var ("a",type_of ar) in
      let sra = mk_eq(r,mk_comb(RE,a)) in
      let ex = mk_exists(a,sra) in
      let imp1 = EXISTS (ex,ar) (SYM(ASSUME eq)) in
      let v = genvar (type_of r) and
          A = rator ar and
          s' = AP_TERM RE (SPEC a th1) in
      let th = SUBST[SYM(ASSUME sra),v](mk_eq(mk_comb(RE,mk_comb(A,v)),v))s' in
      let imp2 = CHOOSE (a,ASSUME ex) th in
      let swap = IMP_ANTISYM_RULE (DISCH eq imp1) (DISCH ex imp2) in
          GEN r (TRANS (SPEC r th2) swap)
  with Failure _ -> failwith "prove_rep_fn_onto";;
```

### Informal statement
Given a theorem `th` which is a conjunction of two theorems `th1` and `th2`, where `th2` is of the form `!r. eq`, where `eq` is of the form `RE ar = r`, prove that for all `r`, there exists an `a` such that `r = RE a`. In other words, the representation function `RE` is onto.

### Informal sketch
The proof proceeds as follows:
- Deconstruct the given theorem `th` into two theorems `th1` and `th2` using `CONJUNCTS`. `th2` is of the form `!r. RE ar = r`, where `RE` is the representation function and `ar` applied to `r` gives element `r` itself.
- Destruct `th2` to isolate the variable `r` and the equation `RE ar = r`.
- Introduce a new variable `a` of the same type as the argument of `ar`.
- Construct the term `r = RE a`.
- Construct the statement `exists a. r = RE a`.
- Show `exists a. r = RE a` follows from assumption `RE ar = r` .
- Establish, from `th1` an instance of representation using the witnessing `CHOOSE` rule and the properties established by the original abstraction mapping.
- Using the above, prove `!r. ?a. r = RE a` by discharging assumptions and generalizing.

### Mathematical insight
This theorem establishes that the representation function `RE` constructed in an abstraction/representation pair is surjective (onto).  This property is crucial to ensuring that every element of the abstract type is represented by some element of the concrete type.

### Dependencies
- `CONJUNCTS`
- `dest_forall`
- `dest_comb`
- `mk_eq`
- `dest_eq`
- `mk_primed_var`
- `mk_exists`
- `EXISTS`
- `SYM`
- `ASSUME`
- `SPEC`
- `AP_TERM`
- `SUBST`
- `CHOOSE`
- `IMP_ANTISYM_RULE`
- `DISCH`
- `GEN`
- `TRANS`


---

## prove_abs_fn_onto

### Name of formal statement
prove_abs_fn_onto

### Type of the formal statement
theorem

### Formal Content
```ocaml
let prove_abs_fn_onto th =
  try let [th1;th2] = CONJUNCTS th in
      let a,(A,R) = (I F_F ((I F_F rator)o dest_comb o lhs))
        (dest_forall(concl th1)) in
      let thm1 = EQT_ELIM(TRANS (SPEC (mk_comb (R,a)) th2)
                                (EQT_INTRO (AP_TERM R (SPEC a th1)))) in
      let thm2 = SYM(SPEC a th1) in
      let r,P = (I F_F (rator o lhs)) (dest_forall(concl th2)) in
      let ex = mk_exists(r,mk_conj(mk_eq(a,mk_comb(A,r)),mk_comb(P,r))) in
          GEN a (EXISTS(ex,mk_comb(R,a)) (CONJ thm2 thm1))
  with Failure _ -> failwith "prove_abs_fn_onto";;
```

### Informal statement
Given a theorem `th` which represents the conjunction of two theorems:
1. For all `a`, `R a = A` (where `R` is a relation and `A` is the abstraction of that relation over some domain).
2. For all `r`, `P r` implies there exists an `a` such that `R a = A` and `P r`.

The theorem to be proven is: For all `a`, there exists an `r` such that `a = A r` and `P r` (i.e. `(a = A r) /\ (P r)`), given that `R a = A`.

### Informal sketch
The proof proceeds by the following steps:

- First, decompose the input theorem `th` into two conjuncts, `th1` and `th2`.
  `th1` is of the form "For all `a`, `R a = A`" where `A` is the abstraction.
  `th2` is of the form "For all `r`, `P r`".

- Instantiate `th2` with `R a`, obtaining `P (R a)`.

- Instantiate `th1` with `a`, deriving `R a = A`.

- Using equation elimination (`EQT_ELIM`), combine `P (R a)` and `R a = A` to derive `P A`.

- Prove `A = R a` by symmetry from `R a = A` using `SYM`.

- Construct the existential statement: There exists `r` (`mk_exists r`) such that `a = A r /\ P r`.

- Generalize existential statement for arbritrary `a` using `GEN a`.

- The main logical steps are using the given implications and equalities to construct an instance of an existence statement for all `a`.

### Mathematical insight
This theorem proves the surjectivity (onto) property of an abstraction function. Given a relation `R` and its abstraction `A`, the theorem shows that for any `a` in the range of the abstraction, there exists an `r` such that `a` is the result of applying the abstraction function `A` to `r`, and `P r` holds. Essentially, any element `a` in the codomain can be mapped to `r` in the domain such that `A r = a`.

### Dependencies
- `CONJUNCTS`
- `dest_forall`
- `concl`
- `dest_comb`
- `lhs`
- `SPEC`
- `mk_comb`
- `EQT_ELIM`
- `TRANS`
- `EQT_INTRO`
- `AP_TERM`
- `SYM`
- `rator`
- `mk_exists`
- `mk_conj`
- `mk_eq`
- `EXISTS`
- `CONJ`
- `GEN`


---

## prove_abs_fn_one_one

### Name of formal statement
prove_abs_fn_one_one

### Type of the formal statement
theorem

### Formal Content
```ocaml
let prove_abs_fn_one_one th =
  try let [th1;th2] = CONJUNCTS th in
      let r,P = (I F_F (rator o lhs)) (dest_forall(concl th2)) and
          A,R = (I F_F rator) (dest_comb(lhs(snd(dest_forall(concl th1))))) in
      let r' = variant [r] r in
      let as1 = ASSUME(mk_comb(P,r)) and as2 = ASSUME(mk_comb(P,r')) in
      let t1 = EQ_MP (SPEC r th2) as1 and t2 = EQ_MP (SPEC r' th2) as2 in
      let eq = (mk_eq(mk_comb(A,r),mk_comb(A,r'))) in
      let v1 = genvar(type_of r) and v2 = genvar(type_of r) in
      let i1 = DISCH eq
               (SUBST [t1,v1;t2,v2] (mk_eq(v1,v2)) (AP_TERM R (ASSUME eq))) and
          i2 = DISCH (mk_eq(r,r')) (AP_TERM A (ASSUME (mk_eq(r,r')))) in
      let thm = IMP_ANTISYM_RULE i1 i2 in
      let disch =  DISCH (mk_comb(P,r)) (DISCH (mk_comb(P,r')) thm) in
          GEN r (GEN r' disch)
  with Failure _ -> failwith "prove_abs_fn_one_one";;
```

### Informal statement
Given a theorem `th` which is a conjunction of two theorems, the first stating that a function `A` is one-to-one on a set defined by a predicate `P`, and the second stating that the absolute value function is one-to-one, this tactic proves that under the assumption that `P(r)` and `P(r')` hold, if `A(r) = A(r')`, then `r = r'`. Furthermore, it discharges the assumptions `P(r)` and `P(r')` to obtain the final theorem: For all `r` and `r'`, if `P(r)` and `P(r')` hold, and `A(r) = A(r')`, then `r = r'`.

### Informal sketch
The proof proceeds as follows:
- Deconstruct the given theorem `th` into two conjuncts, `th1` and `th2`. `th1` states that `A` is one-to-one on the set defined by `P`, and `th2` states that the absolute value function is one-to-one.
- Extract the function `A` and the predicate `P` from the theorems `th1` and `th2`. Specifically, from `th1` we extract `A` and from `th2` we extract `P`.
- Introduce a variant `r'` of the variable `r`.
- Assume `P(r)` and `P(r')`. Call these assumptions `as1` and `as2`, respectively.
- Specialize theorem `th2` with `r` and `r'` respectively. Use `EQ_MP` with assumptions `as1` and `as2` to obtain `ABS r = ABS r` and `ABS r' = ABS r'`. Call these results `t1` and `t2`. Note that `ABS` serves to denote `A` in our context.
- Form the equation `A(r) = A(r')`, i.e. `ABS r = ABS r'`.
- Instantiate two generic variables `v1` and `v2` with the same type as `r`.
- Use `SUBST` and `AP_TERM` to derive `r=r'` starting from `ABS r = ABS r'`, `ABS r = ABS r`, `ABS r' = ABS r'`, where we use `v1` and `v2` in place of `ABS r` and `ABS r'` in the assumption `ABS r = ABS r'`. The result is an implication `ABS r = ABS r' ==> r = r'`. Discharge the assumption `ABS r = ABS r'` to derive `ABS r = ABS r' ==> r = r'`.
- Use `AP_TERM A` and the assumption `r=r'` to show `A r = A r'`. Since `r = r'` we have `A r = A r'`. Discharge the assumption `r = r'` to get `r = r' ==> A r = A r'`.
- Use `IMP_ANTISYM_RULE` to show `(ABS r = ABS r' ==> r = r') and (r = r' ==> ABS r = ABS r')` yield `r = r'`.
- Discharge the assumptions `P(r)` and `P(r')` using `DISCH` twice, and then generalize over `r` and `r'` using `GEN` twice to obtain the final result.

### Mathematical insight
This theorem provides a way to prove that a function `A` is one-to-one, given that another function (in this case, absolute value) is one-to-one and `A` has a connection to the one-to-one function(absolute value). Specifically, it formalizes the idea that if `A(r) = A(r')` implies `r = r'`, where A can be expressed via the absolute value function. This is useful in contexts where one wants to prove the injectivity of a specific function `A` which is somehow related to absolute value function and one only has theorems about the absolute value itself.

### Dependencies
- `CONJUNCTS`
- `I`
- `F_F`
- `rator`
- `lhs`
- `dest_forall`
- `dest_comb`
- `snd`
- `variant`
- `ASSUME`
- `mk_comb`
- `EQ_MP`
- `SPEC`
- `mk_eq`
- `genvar`
- `type_of`
- `DISCH`
- `SUBST`
- `AP_TERM`
- `IMP_ANTISYM_RULE`
- `GEN`

### Porting notes (optional)
- Pay special attention to how the `SUBST` tactic is used within HOL Light. The equivalent operation in other proof assistants might require careful management of variable scope to prevent unintended captures.
- The instantiation and generalization steps using `SPEC` and `GEN` may require explicit quantifier manipulation in proof assistants like Coq or Lean.
- The `variant` tactic may need an alternative implementation based on generating new names.


---

## AC_CONV(assoc,sym)

### Name of formal statement
AC_CONV(assoc,sym)

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let AC_CONV(assoc,sym) =
  let th1 = SPEC_ALL assoc
  and th2 = SPEC_ALL sym in
  let th3 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [th2] th1 in
  let th4 = SYM th1 in
  let th5 = GEN_REWRITE_RULE RAND_CONV [th4] th3 in
  EQT_INTRO o AC(end_itlist CONJ [th2; th4; th5]);;
```

### Informal statement
Given theorems `assoc` and `sym` that are universally quantified, the function `AC_CONV(assoc, sym)` returns a conversion that performs associative-commutative rewriting based on these theorems. Specifically, it derives an equality theorem stating the equivalence of a term and its associative-commutative normalized form, obtained using theorems derived from `assoc` and `sym`.

### Informal sketch
The function `AC_CONV(assoc, sym)` constructs a conversion for associative-commutative rewriting:
- `th1` is obtained by specializing the universally quantified theorem `assoc`.
- `th2` is obtained by specializing the universally quantified theorem `sym`.
- `th3` is derived by rewriting `th1` using `th2` at all applicable left-hand sides of conjunctions within the right-hand side of `th1`.
- `th4` is obtained by symmetrizing `th1`.
- `th5` is derived by rewriting `th3` using `th4` at the right-hand side.
- Finally, it utilizes the `AC` function, which applies associativity and commutativity rules (derived from `th2`, `th4` and `th5`) to produce an equality theorem through iterated application, resulting in the associative-commutative normal form.

### Mathematical insight
The function `AC_CONV(assoc, sym)` encapsulates the common task of building an AC rewriting conversion based on an associativity theorem `assoc` and a commutativity theorem `sym`. It automates the process of generating the necessary rewrite rules and applying them using the generic AC rewriting functionality in HOL Light. The resulting conversion can be used to simplify expressions modulo associativity and commutativity.

### Dependencies
- `SPEC_ALL`
- `GEN_REWRITE_RULE`
- `RAND_CONV`
- `LAND_CONV`
- `SYM`
- `EQT_INTRO`
- `AC`
- `end_itlist`
- `CONJ`


---

## AC_RULE

### Name of formal statement
AC_RULE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let AC_RULE ths = EQT_ELIM o AC_CONV ths;;
```

### Informal statement
Given a list of theorems `ths`, the theorem `AC_RULE ths` is obtained by eliminating the equality from the theorem resulting from applying the AC conversion `AC_CONV` to the list of theorems `ths`.

### Informal sketch
- The function `AC_RULE` takes a list of theorems `ths` as input.
- The associative-commutative conversion `AC_CONV` is applied to `ths`, resulting in a new theorem of the form `|- t1 = t2`.
- The equality elimination rule `EQT_ELIM` is then applied to the result of `AC_CONV ths`, which strips away the equality and returns a theorem of the form `|- t1`.
- The `o` operator represents function composition, such that `(f o g) x = f (g x)`.

### Mathematical insight
The theorem `AC_RULE` essentially states that if `t1 = t2` is provable using associativity and commutativity, then `t1` is provable. It combines the rearrangement capabilities of `AC_CONV` with the ability to extract the left-hand side of an equation using `EQT_ELIM`. This is useful for simplifying terms by rewriting them into a canonical form and then proving a property about the simplified term.

### Dependencies
- `AC_CONV`
- `EQT_ELIM`


---

## (COND_CASES_TAC

### Name of formal statement
`COND_CASES_TAC`

### Type of the formal statement
Tactic

### Formal Content
```ocaml
let (COND_CASES_TAC :tactic) =
    let is_good_cond tm =
      try not(is_const(fst(dest_cond tm)))
      with Failure _ -> false in
    fun (asl,w) ->
      let cond = find_term (fun tm -> is_good_cond tm && free_in tm w) w in
      let p,(t,u) = dest_cond cond in
      let inst = INST_TYPE [type_of t, `:A`] COND_CLAUSES in
      let (ct,cf) = CONJ_PAIR (SPEC u (SPEC t inst)) in
      DISJ_CASES_THEN2
         (fun th -> SUBST1_TAC (EQT_INTRO th) THEN
               SUBST1_TAC ct THEN ASSUME_TAC th)
         (fun th -> SUBST1_TAC (EQF_INTRO th) THEN
               SUBST1_TAC cf THEN ASSUME_TAC th)
         (SPEC p EXCLUDED_MIDDLE)
         (asl,w) ;;
```

### Informal statement
The tactic `COND_CASES_TAC` takes an assumption list `asl` and a goal `w` and performs case splitting on a conditional term within the goal. It finds a conditional term `cond` in `w` such that the condition part of `cond` is not a constant and is free in `w`. Let `p` be the condition and `(t, u)` be the branches of `cond`.
Then, it instantiates the theorem `COND_CLAUSES` with the type of `t`, resulting in a theorem `inst`. Two theorems are constructed: `ct` and `cf`, via specialization of `inst` with `t` and `u`, respectively, and then combining them with `CONJ_PAIR`. Finally, it applies `DISJ_CASES_THEN2` with `SPEC p EXCLUDED_MIDDLE`. The first case applies `SUBST1_TAC` with an equality introduced from the first disjunct, then it applies `SUBST1_TAC` with `ct` and assumes the first disjunct. The second case applies `SUBST1_TAC` with an equality introduced from the second disjunct, then it applies `SUBST1_TAC` with `cf` and assumes the second disjunct.

### Informal sketch
- The tactic aims to perform case splitting on a conditional within a goal.
- First, it locates a suitable conditional term `cond` within the current goal `w`.  A *suitable* conditional contains a condition that is not a constant, and is free in the goal.  If the conditional is of the form `p --> t | u`, it extracts `p`, `t`, and `u`.
- It then uses `COND_CLAUSES` after instantiating its type variable with the type of `t`. `COND_CLAUSES` presumably gives a theorem of form `!A t u. (p --> t | u) = (p /\ t) \/ (~p /\ u)`
- The tactic specializes this conditional clause using `t` and `u`.
- The tactic constructs the theorems whose conclusions are `(p --> t | u) = (T /\ t)` and `(p --> t | u) = (F /\ u)`. These are named `ct` and `cf` respectively.
- Finally, it applies `DISJ_CASES_THEN2` using the law of excluded middle applied to `p`, where one case assumes T and the other assumes F (`p \/ ~p`). In the first branch corresponding to `p`, `SUBST1_TAC` replaces (part of) the goal based on the assumption `p = T`, it performs another substitution based on `ct`, and then assumes `p`. Similarly, the second branch uses assumption `p = F`, and substitutes based on `cf`, then assumes `~p`.

### Mathematical insight
This tactic automates case splitting on conditionals of the form `p --> t | u`. Case splitting on conditionals is a standard technique in theorem proving. The tactic first identifies a suitable conditional located in the goal. Then uses the law of excluded middle for the condition `p`, i.e., `p \/ ~p`. The tactic splits into two cases, one where `p` is true and the other where `p` is false. The goal in each case is then simplified based on the corresponding assumption.

### Dependencies
- `dest_cond`: Function to deconstruct a conditional.
- `is_const`: Function to check if a term is constant.
- `free_in`: Function to check if a variable is free in a term.
- `find_term`: Function to find a term satisfying a predicate.
- `INST_TYPE`: Function to instantiate a type variable in a theorem.
- `COND_CLAUSES`: A theorem relating a conditional term to a disjunction of conjunctions. Likely of the form `!A t u. (p --> t | u) = ((p /\ t) \/ (~p /\ u))`
- `CONJ_PAIR`: Combines two theorems with conjunction of their conclusions.
- `SPEC`: Specializes a theorem with a term.
- `EXCLUDED_MIDDLE`: Theorem representing the law of excluded middle.
- `DISJ_CASES_THEN2`: Tactic to perform case splitting based on a disjunction.
- `EQT_INTRO`: Introduces equality for true.
- `EQF_INTRO`: Introduces equality for false.
- `SUBST1_TAC`: Tactic to perform substitution based on an equality.
- `ASSUME_TAC`: Tactic to add an assumption to the assumption list.

### Porting notes (optional)
- The `COND_CLAUSES` theorem is central and must be available in the target system. It encapsulates the semantics of the conditional operator.
- The tactic relies heavily on term manipulation and theorem instantiation, so ensure that the target system has equivalent functionality for these operations.
- Pay attention to how free variables and type variables are handled.


---

## MATCH_MP_TAC

### Name of formal statement
MATCH_MP_TAC

### Type of the formal statement
Definition

### Formal Content
```ocaml
let MATCH_MP_TAC th =
  MATCH_MP_TAC th ORELSE
  MATCH_MP_TAC(PURE_REWRITE_RULE[RIGHT_IMP_FORALL_THM] th);;
```

### Informal statement
`MATCH_MP_TAC` is a tactic defined such that, when applied to a theorem `th`, it first attempts to apply `MATCH_MP_TAC` to `th` directly, and if that fails, it attempts to apply `MATCH_MP_TAC` to the result of rewriting `th` using the theorem `RIGHT_IMP_FORALL_THM` with the `PURE_REWRITE_RULE` rewriter.

### Informal sketch
- The definition of `MATCH_MP_TAC` represents an attempt to perform Modus Ponens with a theorem, with an additional step to handle universal quantifications on the right-hand side of implications.

- The tactic tries the unmodified theorem `th`.

- If the original `MATCH_MP_TAC` fails, it proceeds to rewrite the theorem `th` using `RIGHT_IMP_FORALL_THM` (which likely transforms an implication with a universal quantifier on the right) and then retries the `MATCH_MP_TAC`.

### Mathematical insight
The core idea is to extend the applicability of Modus Ponens by automatically handling cases where the implication's consequent is a universally quantified formula. The tactic attempts to massage the theorem into a form where standard Modus Ponens can be applied. This is achieved by rewriting the theorem using `RIGHT_IMP_FORALL_THM`, which likely converts an implication `A ==> (!x. B[x])` into `!x. A ==> B[x]`. The overall goal is to allow the tactic to prove theorems of the form `!x. B[x]` given `A` and `A ==> (!x. B[x])`.

### Dependencies
- `RIGHT_IMP_FORALL_THM`
- `PURE_REWRITE_RULE`
- `ORELSE`


---

## ZERO_LESS_EQ

### Name of formal statement
ZERO_LESS_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ZERO_LESS_EQ = LE_0;;
```
### Informal statement
For any natural number `n`, `0` is less than or equal to `n`.

### Informal sketch
The formal statement `ZERO_LESS_EQ` asserts that `0` is less than or equal to any natural number `n`. This theorem, named `LE_0` in HOL Light, is established through the fundamental axioms governing the `≤` relation concerning `0` with other natural numbers. This proof likely relies directly on the definition, or an immediate consequence of the definition, of the less-than-or-equal-to (`LE`) relation for natural numbers and the properties of `0`.

### Mathematical insight
This theorem establishes a fundamental property of the natural numbers and the order relation. It is an essential component in reasoning about inequalities and orderings in number theory.

### Dependencies
- Definitions:
  - `LE` (Less than or equal)
- Axioms:
  - Related to the definition of `LE` on natural numbers or properties of `0` and natural numbers.


---

## LESS_EQ_MONO

### Name of formal statement
LESS_EQ_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_MONO = LE_SUC;;
```

### Informal statement
The theorem `LESS_EQ_MONO` states that the less than or equal to relation `(<=)` is monotonous with respect to the successor function `SUC`. More specifically, for any two natural numbers `m` and `n`, if `m <= n`, then `SUC m <= SUC n`.

### Informal sketch
The proof of `LESS_EQ_MONO` is a direct application of the theorem `LE_SUC`. The theorem `LE_SUC` directly expresses the monotony of the less than or equal to relation under the successor function.

### Mathematical insight
This theorem expresses a fundamental property of the natural numbers, demonstrating how the ordering relation `(<=)` interacts with the successor function `SUC`. It's a basic yet crucial fact used in many arguments about the properties of natural numbers. The theorem confirms that if `m` is less than or equal to `n`, then incrementing both by one preserves the inequality.

### Dependencies
- Theorems:
  - `LE_SUC`


---

## NOT_LESS

### Name of formal statement
NOT_LESS

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_LESS = NOT_LT;;
```
### Informal statement
`NOT_LESS` is defined to be equivalent to `NOT_LT`.

### Informal sketch
The definition simply assigns the existing definition of `NOT_LT` to `NOT_LESS`. There is no proof involved.

### Mathematical insight
This definition provides an alternative name, `NOT_LESS`, for the concept of logical negation applied to "less than" comparisons (`LT`). This might be introduced for readability or consistency with a naming scheme for other comparison operators (e.g., `NOT_EQ`, `NOT_GREATER_THAN`).

### Dependencies
- `NOT_LT`


---

## LESS_0

### Name of formal statement
LESS_0

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_0 = LT_0;;
```
### Informal statement
The predicate `LESS_0` is defined to be equivalent to the predicate `LT_0`.

### Informal sketch
The definition simply assigns the existing predicate `LT_0` to the new name `LESS_0`. This creates an alias or synonym. There is no proof involved, only a definitional equality.

### Mathematical insight
This definition likely aims to provide an alternative name for the "less than zero" predicate, possibly for stylistic or organizational reasons within the formalization. It introduces shorthand. There is value in having alternative names, especially if one name is used more commonly in specific contexts.

### Dependencies
- Definition: `LT_0`


---

## LESS_EQ_REFL

### Name of formal statement
LESS_EQ_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_REFL = LE_REFL;;
```
### Informal statement
For any term `x`, `x` is less than or equal to `x`.

### Informal sketch
The theorem `LESS_EQ_REFL` is defined to be equal to the theorem `LE_REFL`, which states that for any term `x`, `x` is less than or equal to `x`. Thus, it's simply a renaming or alias of an existing theorem.

### Mathematical insight
The theorem asserts the reflexivity of the less than or equal to relation. It's a basic property of order relations.

### Dependencies
- `LE_REFL`


---

## LESS_EQUAL_ANTISYM

### Name of formal statement
LESS_EQUAL_ANTISYM

### Type of the formal statement
theorem

### Formal Content
```ocaml
GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_ANTISYM)))
```

### Informal statement
For all natural numbers `x` and `y`, if `x` is less than or equal to `y` and `y` is less than or equal to `x`, then `x` equals `y`.

### Informal sketch
The proof starts with the antisymmetry axiom of the less than or equal to relation, `LE_ANTISYM`.
- Specialize the universally quantified `LE_ANTISYM` to remove the quantifiers.
- Apply `EQ_IMP_RULE` which transforms an equality `A = B` into an implication `A ==> B`. This transforms the hypothesis `x <= y /\ y <= x` in `LE_ANTISYM` into an assumption.
- Take the first element of the resulting pair involving the theorem and discharging function using `fst`.
- Generalize the free variables `x` and `y` using `GEN_ALL` to reintroduce universal quantification.

### Mathematical insight
This theorem expresses the antisymmetry property of the less than or equal to relation on natural numbers. It is a fundamental property used in many proofs involving inequalities. It formalizes the intuitive notion that if two numbers are each less than or equal to the other, they must be the same.

### Dependencies
- axiom: `LE_ANTISYM`
- theorem: `EQ_IMP_RULE`
- tactic: `SPEC_ALL`
- tactic: `GEN_ALL`


---

## NOT_LESS_0

### Name of formal statement
NOT_LESS_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_LESS_0 = GEN_ALL(EQF_ELIM(SPEC_ALL(CONJUNCT1 LT)));;
```
### Informal statement
For any totally ordered type with ordering relation `<` it is the case that for all `x`, it is not the case that `x < 0`.

### Informal sketch
The proof expands the universal quantifier and eliminates the equality predicate using `EQF_ELIM`. The main idea is to use `LT` which is defined as `!(x:num). x < SUC(0)` and therefore `0 < 1`. Then using `CONJUNCT1` effectively proves that `!(x:num). ~(x < 0)`.

### Mathematical insight
This theorem states a fundamental property of ordered types: no element is strictly less than the minimal element `0`. This is a basic fact and a cornerstone for many theorems in ordered structures.

### Dependencies
- `LT`
- `CONJUNCT1`
- `SPEC_ALL`
- `EQF_ELIM`
- `GEN_ALL`


---

## LESS_TRANS

### Name of formal statement
LESS_TRANS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_TRANS = LT_TRANS;;
```

### Informal statement
The theorem `LESS_TRANS` states that the relation `<` is transitive. i.e. `LT_TRANS` is a theorem asserting transitivity of less than.

### Informal sketch
The formal statement assigns the theorem `LT_TRANS` to the identifier `LESS_TRANS`. Therefore, one must prove the transitivity rule for `<` which forms `LT_TRANS` with the following rule:
For any natural numbers `x`, `y`, and `z`, if `x < y` and `y < z`, then `x < z`. The proof proceeds by induction or other suitable methods on natural numbers to establish this property, and then the resulting theorem is then assigned to `LESS_TRANS`.

### Mathematical insight
The transitivity of the less-than relation is a fundamental property of ordered sets, particularly the natural numbers. This theorem allows for reasoning about inequalities in a chain-like manner. It is used extensively in proving other properties and theorems related to ordering.

### Dependencies
- `LT_TRANS`


---

## LESS_LEMMA1

### Name of formal statement
LESS_LEMMA1

### Type of the formal statement
theorem

### Formal Content
```ocaml
GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL(CONJUNCT2 LT))));;
```

### Informal statement
For all natural numbers `m` and `n`, if `m < n`, then `m = m /\ m < n`.

### Informal sketch
- The theorem is derived from the definition of `<` (less than).
- The proof uses `CONJUNCT2 LT` to extract the second conjunct of the definition of `<`.
- `SPEC_ALL` instantiates the universally quantified variables `m` and `n` in the extracted conjunct.
- `EQ_IMP_RULE` converts the extracted conjunct (implication) into an equality of the form `|- A = T`, where `T` is the truth value.
- `fst` then extracts the left-hand side of this equality (i.e., the assumption/antecedent of implication).
- `GEN_ALL` generalizes the result over all `m` and `n`.

### Mathematical insight
This lemma exposes the redundant nature of the assumed `m < n` when it is added as an assumption again due to the definition of less-than requiring it. This can be used to perform rewriting or simplify assumptions in later proofs.

### Dependencies
- `LT` (definition of less-than on natural numbers)
- `CONJUNCT2`
- `SPEC_ALL`
- `EQ_IMP_RULE`
- `fst`
- `GEN_ALL`

### Porting notes (optional)
The key is ensuring that the target proof assistant has a similar mechanism for extracting conjuncts from definitions and instantiating variables within theorems. Pay attention to how the definition of less-than is represented as such details will affect the application of `CONJUNCT2`.


---

## LESS_SUC_REFL

### Name of formal statement
LESS_SUC_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_SUC_REFL = prove(`!n. n < SUC n`,REWRITE_TAC[LT]);;
```
### Informal statement
For all natural numbers `n`, `n` is less than the successor of `n`.

### Informal sketch
- The proof proceeds by rewriting the goal `n < SUC n` using the definition of the `<` relation on natural numbers, denoted by `LT` in HOL Light.
- The definition of `LT` states that `n < m` if and only if `SUC n = m + k` for some natural number `k`.
- Applying this rewriting, `n < SUC n` becomes equivalent to `SUC n = SUC n + k` for some `k`.
- This reduces the goal to `SUC n = SUC n + 0`.
	
### Mathematical insight
This theorem establishes a fundamental property of the less-than relation on natural numbers: every natural number is strictly less than its successor. This is a basic fact used frequently in reasoning about inequalities and bounds within the natural numbers.

### Dependencies
- Definition: `LT`


---

## FACT_LESS

### Name of formal statement
FACT_LESS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let FACT_LESS = FACT_LT;;
```

### Informal statement
The theorem `FACT_LESS` is defined to be the theorem `FACT_LT`.

### Informal sketch
The theorem `FACT_LESS` is simply an alias for the already proven theorem `FACT_LT`. Thus, proving `FACT_LESS` requires invoking the already proven `FACT_LT`.

### Mathematical insight
This statement is important because it provides an alternative name, `FACT_LESS`, for the theorem `FACT_LT`. This might be useful for clarity or consistency in certain contexts. The underlying connection between `<` and `LESS` is that they represent the same arithmetical relation, and `LESS` is often the preferred name.

### Dependencies
- `FACT_LT`


---

## LESS_EQ_SUC_REFL

### Name of formal statement
LESS_EQ_SUC_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_SUC_REFL = prove(`!n. n <= SUC n`,REWRITE_TAC[LE; LE_REFL]);;
```
### Informal statement
For all natural numbers `n`, `n` is less than or equal to the successor of `n`.

### Informal sketch
The proof proceeds by rewriting the goal `n <= SUC n` using the definition of the less than or equal relation (`LE`), which reduces the goal to `n = n \/ n < n`. Then, the goal `n = n \/ n < n` is proved by proving `n = n` which is handled by reflexivity of equality (`LE_REFL`).

### Mathematical insight
The theorem `LESS_EQ_SUC_REFL` states a fundamental property of the natural numbers: every number is less than or equal to its successor. This reflects the ordering of the natural numbers and is a basic result useful for proving other theorems about inequalities.

### Dependencies
- Definitions: `LE`
- Theorems: `LE_REFL`


---

## LESS_EQ_ADD

### Name of formal statement
LESS_EQ_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_ADD = LE_ADD;;
```
### Informal statement
For any natural numbers `x`, `y`, and `z`, if `x` is less than or equal to `y`, then `x + z` is less than or equal to `y + z`.

### Informal sketch
The theorem `LESS_EQ_ADD` is a direct consequence of the theorem `LE_ADD`. Thus, to prove `LESS_EQ_ADD`, it suffices to set `LESS_EQ_ADD` as `LE_ADD`.

### Mathematical insight
This theorem states that the less than or equal to relation (`<=`) on natural numbers is preserved under addition of the same natural number to both sides. It is a fundamental property of ordered algebraic structures.

### Dependencies
- `LE_ADD`


---

## GREATER_EQ

### Name of formal statement
GREATER_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let GREATER_EQ = GE;;
```

### Informal statement
Define `GREATER_EQ` to be `GE`.

### Informal sketch
The definition simply introduces the symbol `GREATER_EQ` as an alias for the existing symbol `GE`.

### Mathematical insight
This definition is introduced as a convenience, allowing users to refer to the greater-than-or-equal-to relation using the name `GREATER_EQ`, which may be preferred for readability or consistency with other naming conventions.

### Dependencies
None

### Porting notes (optional)
In other proof assistants, simply define `GREATER_EQ` as an alias or notation for the existing greater-than-or-equal-to relation. The exact syntax will vary depending on the target system. For example, in Coq, one could use `Definition GREATER_EQ := GE.` or introduce a notation.


---

## LESS_EQUAL_ADD

### Name of formal statement
LESS_EQUAL_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQUAL_ADD = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_EXISTS)));;
```

### Informal statement
For all types `:num`, for all `x`, `y`, and `z` of type `:num`, if `x` is less than or equal to `y`, then there exists a `w` of type `:num` such that `x + z = y + w`.

### Informal sketch
The proof proceeds by generalizing the existential instantiation of the theorem `LE_EXISTS`, where `LE_EXISTS` states that if `x <= y` then there exists a `d` such that `x + d = y`. The goal is to show `x <= y ==> ?w. x + z = y + w`. Given `x <= y`, we can apply `LE_EXISTS` to obtain a `d` such that `x + d = y`. Now we want to find a `w` such that `x + z = y + w`. By adding `z` to both sides of `x + d = y`, we have `x + d + z = y + z`. By commutativity, we have `x + z + d = y + z`. Therefore, we can pick `w = z` to have `x + z = y + w` with `w = d`.
The theorem is obtained by universally quantifying over `x`, `y`, and `z`.

### Mathematical insight
The theorem essentially states that if `x <= y`, then for any `z`, we can find a `w` such that adding `z` to `x` is equivalent to adding `w` to `y`. This highlights a kind of "translation" property of less-than-or-equal-to when related to addition. It is important when reasoning about inequalities involving sums.

### Dependencies
- `LE_EXISTS`


---

## LESS_EQ_IMP_LESS_SUC

### Name of formal statement
LESS_EQ_IMP_LESS_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_IMP_LESS_SUC = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_SUC_LE)));;
```
### Informal statement
For all natural numbers `n` and `m`, if `n` is less than or equal to `m`, then `n` is less than the successor of `m`.

### Informal sketch
The proof proceeds by generalizing the consequent of the theorem `LT_SUC_LE`, which states that `n < SUC m <=> n <= m`.
- First, specialize the theorem `LT_SUC_LE` with respect to all variables. The result is that for all `n` and `m`, `n < SUC m <=> n <= m`.
- Apply the rule `EQ_IMP_RULE` to turn the equivalence into implication (`<=>` to `=>`).
- Then universally quantify the resulting implication with respect to both `n` and `m` using `GEN_ALL`.

### Mathematical insight
The theorem `LESS_EQ_IMP_LESS_SUC` formalizes the intuition that if a number `n` is less than or equal to `m`, then `n` must also be strictly less than `m+1`. This is a basic property of the ordering on natural numbers.

### Dependencies
- Theorem: `LT_SUC_LE`
- Rule: `EQ_IMP_RULE`
- Rule: `SPEC_ALL`
- Rule: `GEN_ALL`


---

## LESS_IMP_LESS_OR_EQ

### Name of formal statement
LESS_IMP_LESS_OR_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_IMP_LESS_OR_EQ = LT_IMP_LE;;
```
### Informal statement
For any ordered type `:ord`, if `x` and `y` are elements of `:ord`, then `x < y` implies `x <= y`.

### Informal sketch
The theorem `LT_IMP_LE` is being assigned to the name `LESS_IMP_LESS_OR_EQ`. The theorem `LT_IMP_LE` states that for any `x` and `y` of an ordered type, `x < y` implies `x <= y`. This is a direct consequence of the definitions of `<` and `<=` in terms of the ordering relation.

### Mathematical insight
This theorem states the fundamental relationship between strict inequality `<` and non-strict inequality `<=` for ordered types. It formalizes the intuitive notion that "less than" implies "less than or equal to".

### Dependencies
- Definitions:
  - `<`
  - `<=`
- Theorems:
  - `LT_IMP_LE`


---

## LESS_MONO_ADD

### Name of formal statement
LESS_MONO_ADD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_MONO_ADD = GEN_ALL(snd(EQ_IMP_RULE(SPEC_ALL LT_ADD_RCANCEL)));;
```
### Informal statement
For all natural numbers `x`, `y`, and `z`, if `x` is less than `y`, then `x + z` is less than `y + z`.

### Informal sketch
The proof is derived from `LT_ADD_RCANCEL` which states that `(x:num) + z < y + z` is equivalent to `x < y`.
- Specialize the universally quantified variables in `LT_ADD_RCANCEL`.
- Apply `EQ_IMP_RULE` to convert the equivalence into an implication. Specifically, from `A <=> B` derive `A ==> B`.
- Generalize over all `x`, `y`, and `z` using `GEN_ALL`.

### Mathematical insight
This theorem states that addition preserves the order relation on natural numbers. Intuitively, adding the same number to both sides of an inequality does not change the inequality. This is a fundamental property of ordered algebraic structures, and is essential for reasoning about numerical inequalities.

### Dependencies
- `LT_ADD_RCANCEL`
- `EQ_IMP_RULE`
- `SPEC_ALL`
- `GEN_ALL`


---

## LESS_SUC

### Name of formal statement
LESS_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_SUC = prove(`!m n. m < n ==> m < (SUC n)`,MESON_TAC[LT]);;
```
### Informal statement
For all natural numbers `m` and `n`, if `m` is less than `n`, then `m` is less than the successor of `n`.

### Informal sketch
The proof uses the `MESON_TAC` tactic which invokes a first-order automatic theorem prover. It likely relies on the definition of the less-than relation (`<`) in terms of natural numbers and properties of the successor function (`SUC`). The proof is a direct application of the properties defining the ordering of natural numbers.

### Mathematical insight
This theorem formalizes the intuitive property that if a number `m` is less than `n`, it is also less than `n+1`. It is a fundamental property used in reasoning about inequalities and the ordering of natural numbers.

### Dependencies
- Definitions:
  - `<` (less-than relation on natural numbers)
  - `SUC` (successor function)

### Porting notes (optional)
This theorem should be straightforward to prove in most proof assistants since it relies on a basic property of the ordering of natural numbers. The main challenge might be related to differences in how the ordering and the successor functions are defined. The equivalent of `MESON_TAC` in other proof assistants (e.g., `auto` in Coq, `simp` and `auto` in Isabelle, `library_search` in Lean) should be able to prove this automatically.


---

## LESS_CASES

### Name of formal statement
LESS_CASES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_CASES = LTE_CASES;;
```

### Informal statement
The theorem `LESS_CASES` states that it is equivalent to the theorem `LTE_CASES`.

### Informal sketch
The proof of `LESS_CASES` is trivial; it involves simply replacing `LESS_CASES` with `LTE_CASES`. Essentially, this establishes an alias or synonym to `LTE_CASES` under the name `LESS_CASES`.

### Mathematical insight
This is likely a definition of inequality in terms of less than or equal, and so there are several equivalent ways to express this in HOL Light. This allows one to use the `LTE_CASES` theorem under an alternative name, `LESS_CASES`, possibly to improve readability or match conventional mathematical notation in different contexts.

### Dependencies
- Theorem: `LTE_CASES`


---

## LESS_EQ

### Name of formal statement
LESS_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ = GSYM LE_SUC_LT;;
```

### Informal statement
The theorem `LESS_EQ` states that for any natural numbers `m` and `n`, `n + 1` is less than `m` if and only if `m` is greater than `n + 1`.

### Informal sketch
The proof uses the theorem `LE_SUC_LT`, which states that `n + 1 < m` implies `m > n + 1`. The `GSYM` tactic then reverses the implication, showing that `m > n + 1` implies `n + 1 < m`.

### Mathematical insight
This theorem reflects the symmetry of the "less than" and "greater than" relations when incrementing the value on one side. This symmetry is fundamental in reasoning about inequalities.

### Dependencies
- Theorem: `LE_SUC_LT`


---

## LESS_OR_EQ

### Name of formal statement
LESS_OR_EQ

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let LESS_OR_EQ = LE_LT;;
```

### Informal statement
The definition `LESS_OR_EQ` is defined to be equal to `LE_LT`.

### Informal sketch
The definition directly assigns the existing function `LE_LT` to the new name `LESS_OR_EQ`. Thus, `LESS_OR_EQ` becomes an alias for `LE_LT`.

### Mathematical insight
This definition provides an alternative, perhaps more conventional, name `LESS_OR_EQ` for the concept already embodied by `LE_LT`, which relates to "less than or equals". This renaming can improve code readability and make it more familiar to mathematicians accustomed to standard notation.

### Dependencies
None

### Porting notes (optional)
This definition should be straightforward to port as it simply involves assigning an existing function or relation to a new name. Other proof assistants are likely to have similar mechanisms for creating aliases or synonyms for existing definitions. In some systems, the notation might need to be defined separately to use the usual symbol ≤.


---

## LESS_ADD_1

### Name of formal statement
LESS_ADD_1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_ADD_1 = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL
    (REWRITE_RULE[ADD1] LT_EXISTS))));;
```

### Informal statement
For all natural numbers `n` and `m`, there exists a natural number `k` such that `m < n + 1`.

### Informal sketch
- The proof starts with the theorem stating the existence of a `k` such that `m < n + 1`. It is derived by discharging the quantifiers using `GEN_ALL`, which means generalizing from a specific case. Thus we need to show that for arbitrary `m` and `n`, there exists a `k` such that `m < n + 1`.
- The core of the proof uses `LT_EXISTS`, which states that for any `n` there exists a `k` such that `n < k`.
- Then `ADD1` is used to rewrite `k` as `k+1`.
- Finally `EQ_IMP_RULE` is used to link everything together into the desired goal.

### Mathematical insight
This theorem states that for any natural number `n`, it is always possible to find a number `k` strictly greater than `n`. In particular, `n + 1` is strictly greater than `n`. It is a basic property of the ordering of natural numbers and the successor function.

### Dependencies
- `ADD1`
- `LT_EXISTS`
- `EQ_IMP_RULE`
- `SPEC_ALL`
- `REWRITE_RULE`
- `GEN_ALL`


---

## SUC_SUB1

### Name of formal statement
SUC_SUB1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUC_SUB1 = prove(`!m. SUC m - 1 = m`,
                     REWRITE_TAC[num_CONV `1`; SUB_SUC; SUB_0]);;
```
### Informal statement
For all natural numbers `m`, the predecessor of the successor of `m` minus 1 equals `m`.

### Informal sketch
The proof proceeds by rewriting the goal `SUC m - 1 = m` using the following steps:
- Rewrite using the definition of `1`.
- Rewrite using the theorem `SUB_SUC`, which states that `n - SUC m = PRE (n - m)`. This simplifies the expression.
- Rewrite using the theorem `SUB_0`, which states that `n - 0 = n`.

### Mathematical insight
This theorem formalizes the basic arithmetic fact that decrementing the successor of a number results in the original number. It relies on the definitions of successor, predecessor, and subtraction within the Peano arithmetic formalization in HOL Light. This theorem is a fundamental building block for more complex arithmetic reasoning.

### Dependencies
- Definitions:
    - `1`
- Theorems:
    - `SUB_SUC`
    - `SUB_0`


---

## LESS_MONO_EQ

### Name of formal statement
LESS_MONO_EQ

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_MONO_EQ = LT_SUC;;
```

### Informal statement
The theorem `LESS_MONO_EQ` states that for any natural numbers `n` and `m`, `n < m` if and only if `SUC n < SUC m`, where `SUC` denotes the successor function on natural numbers.

### Informal sketch
The theorem `LESS_MONO_EQ` is defined to be equivalent to `LT_SUC`. The proof of `LT_SUC` likely involves induction to establish the relationship between the less-than relation and the successor function. The proof probably proceeds by showing that if `n < m`, then `SUC n < SUC m`, and conversely, if `SUC n < SUC m`, then `n < m`.

### Mathematical insight
The theorem captures the intuition that the order of natural numbers is preserved by the successor function. It is a fundamental property of natural numbers and the less-than relation, and it is essential for reasoning about arithmetic operations. This is a basic fact that connects the order relation with the successor function and is used in several proofs in number theory.

### Dependencies
- Definition: `LT_SUC`


---

## LESS_ADD_SUC

### Name of formal statement
LESS_ADD_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_ADD_SUC = prove (`!m n. m < m + SUC n`,
                          REWRITE_TAC[ADD_CLAUSES; LT_SUC_LE; LE_ADD]);;
```

### Informal statement
For all natural numbers `m` and `n`, `m` is less than `m` plus the successor of `n`.

### Informal sketch
The proof proceeds by rewriting the goal using the following steps:
- Expand `m + SUC n` to `SUC (m + n)` using the definition of addition (`ADD_CLAUSES`).
- Convert `m < SUC (m + n)` to `m <= m + n` using the equivalence between `< SUC` and `<= ` (`LT_SUC_LE`).
- Rewrite `m <= m + n` to `T` using the theorem `m <= m + n` (`LE_ADD`).

### Mathematical insight
This theorem expresses a fundamental property of natural numbers: adding any natural number to another (including the successor of another) always results in a sum that is strictly greater than the original number. It demonstrates the ordering relation between a number and its sum with another number.

### Dependencies
- Definitions: `ADD_CLAUSES`
- Theorems: `LT_SUC_LE`, `LE_ADD`


---

## LESS_REFL

### Name of formal statement
LESS_REFL

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_REFL = LT_REFL;;
```

### Informal statement
The relation `<` is reflexive.

### Informal sketch
The theorem `LESS_REFL` is defined to be equivalent to the theorem `LT_REFL`. Therefore, to prove that the relation `<` is reflexive one only needs to prove `LT_REFL`.

### Mathematical insight
The theorem establishes that the less-than relation `<` is reflexive. Reflexivity is a fundamental property used in various mathematical proofs and constructions. This relationship is very useful to reason about objects which are related by `<`.

### Dependencies
- `LT_REFL`


---

## INV_SUC_EQ

### Name of formal statement
INV_SUC_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INV_SUC_EQ = SUC_INJ;;
```
### Informal statement
The function `SUC` is injective.  That is, if the successor of a natural number `m` is equal to the successor of a natural number `n`, then `m` is equal to `n`.

### Informal sketch
The theorem `SUC_INJ` is used directly to define `INV_SUC_EQ`. There is no proof sketch to provide, it is a direct assignment.

### Mathematical insight
This theorem, stating the injectivity of the successor function, is a fundamental property of the natural numbers. It asserts that distinct natural numbers have distinct successors. This property is crucial for many arguments and constructions involving natural numbers.

### Dependencies
- Theorems:
    - `SUC_INJ`

### Porting notes (optional)
In many proof assistants, such as Coq or Lean, injectivity of constructors is often automatically derived during the definition of inductive types. Therefore, proving this theorem might be trivial or unnecessary, instead it would be automatically solved by the simplifier or `auto` tactics after the definition of natural numbers and their constructor `SUC`. If it is not automatically derived, then the proof should follow the structure of `SUC_INJ`.


---

## LESS_EQ_CASES

### Name of formal statement
LESS_EQ_CASES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_EQ_CASES = LE_CASES;;
```

### Informal statement
The theorem `LESS_EQ_CASES` states that the cases for less-than-or-equal are identical to the cases for less-than-or-equal.

### Informal sketch
The theorem alias `LESS_EQ_CASES` is defined to be the same as `LE_CASES`. The proof is trivial since it's a direct assignment.

### Mathematical insight
This is a simple alias. It exists potentially for notational convenience or to maintain consistency across a library of definitions and theorems. The statement highlights that the cases to consider when dealing with the less-than-or-equal relation are the same irrespective of the notation used.

### Dependencies
None

### Porting notes (optional)
This should be a straightforward port to any system with theorem aliasing.


---

## LESS_EQ_TRANS

### Name of formal statement
LESS_EQ_TRANS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_TRANS = LE_TRANS;;
```

### Informal statement
The less than or equal to relation is transitive. Formally, if `x <= y` and `y <= z`, then `x <= z`.

### Informal sketch
The theorem `LESS_EQ_TRANS` is defined to be the same as the theorem `LE_TRANS`, meaning the proof is already shown in proving `LE_TRANS`. It utilizes the transitivity of the less than or equal to relation already proven.

### Mathematical insight
This theorem expresses a fundamental property of the less than or equal to relation: transitivity. Transitivity is a core axiom in many ordered structures and is essential for reasoning about inequalities.

### Dependencies
- Definition: `LE_TRANS`


---

## LESS_THM

### Name of formal statement
LESS_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_THM = CONJUNCT2 LT;;
```

### Informal statement
The theorem `LESS_THM` states that it is the second conjunct of the theorem `LT`.

### Informal sketch
The theorem `LESS_THM` is simply defined to be the second conjunct of the previously proven theorem `LT`. The proof is trivial by construction. The `CONJUNCT2` tactic selects the second conjunct of the `LT` theorem.

### Mathematical insight
Given a theorem of the form `A /\ B`, this theorem just "extracts" `B` as a theorem on its own.  This pattern is common in HOL Light to decompose larger theorems into smaller, more manageable pieces. Here, it is presumed that `LT` represents a conjunction, and `LESS_THM` isolates the second part of that conjunction, presumably related to the less-than relation.

### Dependencies
- `LT`


---

## GREATER

### Name of formal statement
GREATER

### Type of the formal statement
New Definition

### Formal Content
```ocaml
let GREATER = GT;;
```

### Informal statement
Define `GREATER` to be equal to `GT`.

### Informal sketch
The definition simply equates `GREATER` to `GT`. There's no proof or construction involved.

### Mathematical insight
This definition introduces a new name, `GREATER`, as an alias for the existing function `GT`. This might be done for readability or to match mathematical notation more closely, where "greater than" might be conceptually distinct from a generic comparison operator.

### Dependencies
- `GT`


---

## LESS_EQ_0

### Name of formal statement
LESS_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_0 = CONJUNCT1 LE;;
```
### Informal statement
The theorem states that `CONJUNCT1` of the relation `LE` holds. (where `LE` is presumably a theorem about less than or equal)

### Informal sketch
The theorem `LESS_EQ_0` is a pre-proved result, directly obtained by taking the first conjunct of the theorem `LE`. The proof should be trivial, since it is directly extracted from `LE`.

### Mathematical insight
It's likely `LE` refers to a theorem that represents the definition or a key property of the less-than-or-equal relation. This theorem `LESS_EQ_0` extracts a specific component of it, possibly a fundamental property to be used independently. The specific meaning will depend on the nature of `LE`.

### Dependencies
- Theorems: `LE`

### Porting notes (optional)
The porting process is straightforward. The theorem will need to be proved by extracting it directly from the proof or definition of `LE`. This usually involves applying an appropriate projection or decomposition tactic/function available in the target proof assistant.


---

## OR_LESS

### Name of formal statement
OR_LESS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let OR_LESS = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_SUC_LT)));;
```
let OR_LESS = GEN_ALL(fst(EQ_IMP_RULE(SPEC_ALL LE_SUC_LT)));;
### Informal statement
For all natural numbers `n` and `m`, if `n` is less than or equal to the successor of `m`, then `n` is less than `m` or `n` is equal to the successor of `m`.

### Informal sketch
- The theorem `OR_LESS` is derived from `LE_SUC_LT` by specializing its universally quantified variables and applying `EQ_IMP_RULE` and `GEN_ALL`.
- `LE_SUC_LT` states that `n <= S m <=> n < m \/ n = S m`.
- `SPEC_ALL` instantiates the universally quantified variables in `LE_SUC_LT` to obtain a specific instance of the equivalence.
- `EQ_IMP_RULE` turns an equivalence `A <=> B` into an implication `A ==> B`.
- `GEN_ALL` generalizes over all free variables to obtain the universally quantified theorem.

### Mathematical insight
The theorem relates the less than or equal relation (`<=`) to the less than (`<`) and equality relations when dealing with the successor function (`S`). It provides a way to decompose `n <= S m` into two exclusive possibilities: either `n < m` or `n = S m`. This is a fundamental property in the ordering of natural numbers.

### Dependencies
- Theorem: `LE_SUC_LT`

### Porting notes (optional)
This theorem relies on a specific ordering and successor definition for natural numbers. Ensure that the target proof assistant's library provides similar definitions and the theorem `LE_SUC_LT` or an equivalent theorem. The tactics `SPEC_ALL`, `EQ_IMP_RULE`, and `GEN_ALL` have equivalents in other proof assistants: instantiation of quantifiers, rewriting with equivalences, and generalization of free variables. These will need to be adapted according to the target system's syntax and available tactics.


---

## SUB_EQUAL_0

### Name of formal statement
SUB_EQUAL_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_EQUAL_0 = SUB_REFL;;
```

### Informal statement
For all terms `x`, the term `x - x` is equal to 0.

### Informal sketch
The proof proceeds by direct application of the theorem `SUB_REFL`, which states that `x - x = 0` for any term `x`.

### Mathematical insight
The theorem `SUB_EQUAL_0` embodies the fundamental property that subtracting a quantity from itself results in zero. This is a basic but essential arithmetic fact.

### Dependencies
- Theorems:
  - `SUB_REFL`


---

## SUB_MONO_EQ

### Name of formal statement
SUB_MONO_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_MONO_EQ = SUB_SUC;;
```

### Informal statement
The theorem `SUB_MONO_EQ` is defined to be equal to the theorem `SUB_SUC`.

### Informal sketch
The definition simply equates `SUB_MONO_EQ` with `SUB_SUC`, so no specific proof is needed, as it is definitional. The theorem `SUB_SUC` likely asserts a property about the relation between subtraction and the successor function on natural numbers.

### Mathematical insight
This definition equates the theorem `SUB_MONO_EQ` to a previously established theorem called `SUB_SUC`. This suggests that `SUB_MONO_EQ` either represents a special case or a restatement of `SUB_SUC` under a more descriptive name, possibly related to the monotonicity of subtraction with respect to equality or ordering induced by successors.

### Dependencies
- Theorems: `SUB_SUC`


---

## NOT_SUC_LESS_EQ

### Name of formal statement
NOT_SUC_LESS_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NOT_SUC_LESS_EQ = prove (`!n m. ~(SUC n <= m) <=> m <= n`,
                             REWRITE_TAC[NOT_LE; LT] THEN
                             MESON_TAC[LE_LT]);;
```

### Informal statement
For all natural numbers `n` and `m`, it is not the case that the successor of `n` is less than or equal to `m` if and only if `m` is less than or equal to `n`.

### Informal sketch
The proof proceeds as follows:
- First, rewrite using the definitions of `NOT_LE` (negation of less than or equal to) and `LT` (less than) to expand the equivalence.
- Then, use a MESON-based tactic, providing lemmas `LE_LT` (relationship between less than or equal to and less than) to complete the proof automatically.

### Mathematical insight
This theorem expresses a basic relationship between the "less than or equal to" relation and its negation in the context of natural numbers. Specifically, it shows that `SUC n <= m` being false is equivalent to `m <= n` being true. This is a useful fact when reasoning about inequalities between natural numbers.

### Dependencies
- Definitions: `NOT_LE`, `LT`
- Theorems: `LE_LT`


---

## SUC_NOT

### Name of formal statement
SUC_NOT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUC_NOT = GSYM NOT_SUC;;
```
### Informal statement
The successor function is not surjective, meaning it's not the case that for all natural numbers `n`, there exists a natural number `m` such that `SUC m = n`.

### Informal sketch
- The theorem `SUC_NOT` is derived by generalizing the negation of the theorem `NOT_SUC`. The theorem `NOT_SUC` states that `¬(SUC n = 0)` for all natural numbers `n`. Taking the generalisation of the negation of `NOT_SUC` gives `¬(∀n. SUC n = 0)`, or equivalently, `∃n, SUC n ≠ 0`, which shows the successor function is not surjective.

### Mathematical insight
The theorem `SUC_NOT` is a fundamental property of the natural numbers and the successor function. It states that zero is not in the range of the successor function. This is a key axiom or theorem in many constructions of the natural numbers.

### Dependencies
- `NOT_SUC`


---

## LESS_LESS_CASES

### Name of formal statement
LESS_LESS_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_LESS_CASES = prove(`!m n:num. (m = n) \/ m < n \/ n < m`,
                            MESON_TAC[LT_CASES]);;
```
### Informal statement
For all natural numbers `m` and `n`, either `m` equals `n`, or `m` is less than `n`, or `n` is less than `m`.

### Informal sketch
- The proof is done using the `MESON_TAC` tactic which automatically discharges the goal using `LT_CASES`.
- The theorem `LT_CASES` states that for any natural numbers `m` and `n`, either `m < n` or `m = n` or `n < m + 1`.

### Mathematical insight
This theorem establishes that `<` is total on the natural numbers, meaning that any two natural numbers are comparable using equality or the less-than relation. This is a fundamental property of the ordering of natural numbers.

### Dependencies
- `LT_CASES`


---

## NOT_LESS_EQUAL

### Name of formal statement
NOT_LESS_EQUAL

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let NOT_LESS_EQUAL = NOT_LE;;
```

### Informal statement
Define `NOT_LESS_EQUAL` to be equivalent to the negation of the less-than-or-equal-to relation, `NOT_LE`.

### Informal sketch
The definition simply assigns an existing function, `NOT_LE`, to a new name, `NOT_LESS_EQUAL`. There is no proof or construction involved; it's a direct definitional equality.

### Mathematical insight
This definition introduces a new name, `NOT_LESS_EQUAL`, as an alias for the function that represents the negation of the less-than-or-equal-to relation. This might be done for notational convenience or to improve readability in specific contexts. The underlying mathematical concept remains the same.

### Dependencies
- Definition: `NOT_LE`


---

## LESS_EQ_EXISTS

### Name of formal statement
LESS_EQ_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_EXISTS = LE_EXISTS;;
```

### Informal statement
For all totally ordered types, represented by a type variable `:A` equipped with a less-than-or-equal-to relation, there exists an element of that type.  In other words, the type `:A` is non-empty.

### Informal sketch
The theorem `LESS_EQ_EXISTS` is simply an alias for the theorem `LE_EXISTS`. Thus, the proof is trivial, since it directly relies on the existence of inhabited types when using the less than or equals relation.

### Mathematical insight
This theorem asserts the fundamental property that for any type equipped with a total order, there must exist at least one element of that type. The existence of an element is a pre-requisite for establishing properties about relationships between ordered elements. This ensures that the theorems about the order relations are not vacuously true for empty sets.

### Dependencies
- Axiom: `LE_EXISTS`


---

## LESS_MONO_ADD_EQ

### Name of formal statement
LESS_MONO_ADD_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_MONO_ADD_EQ = LT_ADD_RCANCEL;;
```

### Informal statement
For all natural numbers `x`, `y`, and `z`, `x` is less than `y` if and only if `x + z` is less than `y + z`.

### Informal sketch
The theorem `LESS_MONO_ADD_EQ` is defined to be equal to the theorem `LT_ADD_RCANCEL`. Thus, the proof is the proof that `LT_ADD_RCANCEL` has.

### Mathematical insight
This theorem states that addition preserves the less-than relation. Adding the same number to both sides of an inequality does not change the inequality. This is a basic property of ordered semigroups.

### Dependencies
- `LT_ADD_RCANCEL`


---

## LESS_LESS_EQ_TRANS

### Name of formal statement
`LESS_LESS_EQ_TRANS`

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let LESS_LESS_EQ_TRANS = LTE_TRANS;;
```

### Informal statement
Transitivity of the less than or equal to relation: If `x < y` and `y < z`, then `x < z`.

### Informal sketch
The theorem `LESS_LESS_EQ_TRANS` is simply defined as being equal to the theorem `LTE_TRANS`. Thus, the proof and its underlying mathematical structure are the same as those for `LTE_TRANS`.
- The theorem `LTE_TRANS` states that if `x <= y` and `y <= z`, then `x <= z`.
- The proof (which is not visible as it is a pre-existing theorem alias) presumably proceeds by induction on the definitions of the involved less than or equal relations.

### Mathematical insight
The transitivity of the less than or equal to relation is a fundamental property of ordered sets and is essential for reasoning about inequalities. This theorem allows us to chain inequalities together.

### Dependencies
- `LTE_TRANS`


---

## SUB_SUB

### Name of formal statement
SUB_SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
ARITH_RULE
  `!b c. c <= b ==> (!a:num. a - (b - c) = (a + c) - b)`
```

### Informal statement
For all natural numbers `b` and `c`, if `c` is less than or equal to `b`, then for all natural numbers `a`, `a` minus (`b` minus `c`) is equal to (`a` plus `c`) minus `b`.

### Informal sketch
The proof uses the arithmetic rule `ARITH_RULE`, which likely contains a suite of simplification tactics tailored for arithmetic reasoning on natural numbers. The core idea is to leverage the properties of subtraction and addition on natural numbers to show the equivalence. The assumption `c <= b` is crucial, as it ensures that `b - c` is a natural number. The strategy probably involves expanding the definitions of subtraction and addition in terms of repeated increment/decrement (if that's how they're defined) or using existing lemmas regarding addition/subtraction associativity and commutativity, followed by simplification to arrive at the desired equality. The key logical step is probably manipulating the expressions on both sides of equality by adding/subtracting `c` and `b` until they become identical.

### Mathematical insight
This theorem demonstrates an important property of natural number arithmetic relating addition and subtraction. It reveals that subtracting a difference is equivalent to adding and then subtracting. This is a canonical algebraic identity useful in program verification and other formal reasoning tasks involving arithmetic. It is important to establish such identities in a proof assistant to enable rewriting and simplification of arithmetic expressions.

### Dependencies
- Theorem: `ARITH_RULE`

### Porting notes (optional)
The main challenge when porting will be ensuring that the target proof assistant has suitable automation for arithmetic reasoning, similar to HOL Light's `ARITH_RULE`. If not, the proof may need to be expanded into more elementary steps. Specifically, it is necessary to check how subtraction is axiomatized (or defined) in the target system, particularly how the condition `c <= b` is handled formally to ensure `b - c` is a natural number. Similarly, the properties of addition will need to be proven and applied if the automation is insufficient.


---

## LESS_CASES_IMP

### Name of formal statement
LESS_CASES_IMP

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_CASES_IMP = ARITH_RULE
  `!m n:num. ~(m < n) /\ ~(m = n) ==> n < m`;;
```
### Informal statement
For all natural numbers `m` and `n`, if it is not the case that `m` is less than `n` and it is not the case that `m` equals `n`, then `n` is less than `m`.

### Informal sketch
*   The theorem `LESS_CASES_IMP` is proved by applying the arithmetic decision procedure `ARITH_RULE` to the goal `!m n:num. ~(m < n) /\ ~(m = n) ==> n < m`. The `ARITH_RULE` tactic automatically proves arithmetic theorems such as this one.
*   There are no further logical steps presented at this level of detail.

### Mathematical insight
The theorem captures the exhaustiveness of the trichotomy law for natural numbers. Either `m < n`, `m = n`, or `n < m`. The theorem formalizes that if the first two possibilities do not hold, then the third one must. This is a basic property of the ordering on natural numbers.

### Dependencies
*   Tactics: `ARITH_RULE`


---

## SUB_LESS_EQ

### Name of formal statement
SUB_LESS_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_LESS_EQ = ARITH_RULE
  `!n m:num. (n - m) <= n`;;
```

### Informal statement
For all natural numbers `n` and `m`, `n - m` is less than or equal to `n`.

### Informal sketch
The statement `!n m:num. (n - m) <= n` is proved by arithmetic reasoning using the tactic `ARITH_RULE`.

*   The `ARITH_RULE` tactic automatically discharges the goal using built-in arithmetic decision procedures.
* The underlying proof likely involves unfolding the definition of natural number subtraction and subsequently proving that, the result of the subtraction will always be less or equal to the number that was initially supplied to the subtraction operation.

### Mathematical insight
This theorem expresses a fundamental property of natural number subtraction: subtracting a natural number from another can only result in a smaller or equal number. It relies on the definition of natural numbers and the properties of the subtraction operation. This is a standard and expected property in any axiomatization of arithmetic.

### Dependencies
*   `ARITH_RULE`


---

## SUB_EQ_EQ_0

### Name of formal statement
SUB_EQ_EQ_0

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_EQ_EQ_0 = ARITH_RULE
 `!m n:num. (m - n = m) <=> (m = 0) \/ (n = 0)`;;
```
### Informal statement
For all natural numbers `m` and `n`, `m - n = m` if and only if `m = 0` or `n = 0`.

### Informal sketch
*   The proof establishes a bi-implication between `m - n = m` and `m = 0 \/ n = 0` for natural numbers `m` and `n`.
*   One direction (=>) proceeds by considering the equation `m - n = m`. Adding `n` to both sides yields `m = m + n`. Then, it is shown that this implies `n = 0`. Substituting `n = 0` back into the original equation simplifies it to `m = m`, which results in `m = 0`. Proving the implication `m - n = m ==> m = 0 \/ n = 0`, therefore, leads to `m = 0 \/ n = 0` because `n = 0` implies `m = 0 \/ n = 0`.
*   The other direction (<=) proves `(m = 0 \/ n = 0) ==> m - n = m`. If `m = 0`, then `0 - n = 0` holds directly because `0 - n` simplifies to `0`. If `n = 0`, then `m - 0 = m` which holds directly.

### Mathematical insight
This theorem characterizes when subtracting a natural number `n` from `m` leaves `m` unchanged. This occurs only when either `m` is zero (subtracting anything from zero leaves zero in natural number arithmetic) or `n` is zero (subtracting zero from anything leaves it unchanged).

### Dependencies
*   `ARITH_RULE`


---

## SUB_LEFT_LESS_EQ

### Name of formal statement
SUB_LEFT_LESS_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_LEFT_LESS_EQ = ARITH_RULE
  `!m n p:num. m <= (n - p) <=> (m + p) <= n \/ m <= 0`;;
```
### Informal statement
For all natural numbers `m`, `n`, and `p`, `m` is less than or equal to `n` minus `p` if and only if `m` plus `p` is less than or equal to `n` or `m` is less than or equal to 0.

### Informal sketch
The theorem `SUB_LEFT_LESS_EQ` relates the inequality `m <= n - p` to the inequality `m + p <= n` and the condition `m <= 0`. The proof likely proceeds by considering cases based on whether `p` is greater than `n`.

*   The statement should hold if `n - p` is interpreted as the natural number subtraction, which returns 0 if `p > n` with the ordinary difference if `p <= n`.
* One direction `m <= (n - p) ==> (m + p <= n) \/ (m <= 0)` should be proved by considering two cases. If `p <= n`, then `n - p` is `n - p` (ordinary subtraction) and the desired inequality follows. If `p > n`, then `n - p` is `0`, and thus `m <= (n - p)` means `m <= 0`, which also satisfies to the right hand side.
* Converse direction `(m + p <= n) \/ (m <= 0) ==> m <= (n - p)` should be proved by cases.
    * If `m <= 0` then `m = 0` (since we operate with natural numbers), so `m <= (n - p)` is trivially satisfied, because `n - p` is non-negative and `m = 0`.
    * If `m + p <= n` then `m <= n - p`, because that is how natural number subtraction is defined.

### Mathematical insight
The theorem helps to eliminate subtraction in favor of addition when dealing with inequalities, except one must consider the edge case when `m <= 0` due to the nature of natural number arithmetic, where `n - p` is defined to be 0 when `p > n`. This is a useful result when automating arithmetic reasoning.

### Dependencies
*   `ARITH_RULE` (likely a tactic or rule for arithmetic reasoning, possibly discharging the theorem directly or used in its proof)

### Porting notes (optional)
When porting to a system with a different flavor of arithmetic (e.g., integer arithmetic), the `m <= 0` condition should likely be dropped if negative numbers are allowed, or adapted, e.g., in Coq one can use the predicate `le` or `leb` to represent the less than or equal relationship. Also, the implementation of subtraction on natural numbers might differ across systems. In Coq, for example, subtraction on natural numbers will return 0 if the subtrahend is larger than the minuend, so one has to know the library intimately.


---

## SUB_LEFT_GREATER_EQ

### Name of formal statement
SUB_LEFT_GREATER_EQ

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB_LEFT_GREATER_EQ =
  ARITH_RULE `!m n p:num. m >= (n - p) <=> (m + p) >= n`;;
```
### Informal statement
For all natural numbers `m`, `n`, and `p`, `m` is greater than or equal to `n` minus `p` if and only if `m` plus `p` is greater than or equal to `n`.

### Informal sketch
The proof comes directly from the arithmetic library `ARITH_RULE`. The `ARITH_RULE` tactic is a decision procedure for linear arithmetic over the natural numbers, so it automatically proves this statement via quantifier elimination and linear inequality reasoning. This theorem represents a standard manipulation of inequalities involving subtraction and addition.

### Mathematical insight
This theorem expresses a fundamental property of natural numbers relating subtraction and addition with respect to the greater-than-or-equal-to relation. It states that subtracting a number `p` from `n` and comparing the result to `m` is equivalent to adding `p` to `m` and comparing the result to `n`. This equivalence is essential for manipulating inequalities and solving equations involving natural numbers.

### Dependencies
- Arithmetic Library: `ARITH_RULE`


---

## LESS_EQ_LESS_TRANS

### Name of formal statement
LESS_EQ_LESS_TRANS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_LESS_TRANS = LET_TRANS;;
```
### Informal statement
Given three natural numbers `x`, `y`, and `z`, if `x` is less than or equal to `y` and `y` is less than `z`, then `x` is less than `z`.

### Informal sketch
- The theorem `LESS_EQ_LESS_TRANS` states the transitivity property when relating "less than or equal to" with "less than". It is shown that if `x <= y` and `y < z` then `x < z`.
- The proof relies on the more general theorem `LET_TRANS` which proves transitivity for any relations `R`, `S`, and `T` when `R ==> S ==> T`. In this case `R` is `x <= y`, `S` is `y < z` and `T` is `x < z`.

### Mathematical insight
This theorem establishes a fundamental transitivity property when combining the "less than or equal to" and "less than" relations on natural numbers. It is a crucial part of reasoning about inequalities and order.

### Dependencies
- `LET_TRANS`


---

## LESS_0_CASES

### Name of formal statement
LESS_0_CASES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;
```
### Informal statement
For all natural numbers `m`, either `0` is equal to `m`, or `0` is less than `m`.

### Informal sketch
The proof proceeds by arithmetic reasoning using the rule `ARITH_RULE`. The statement expresses a basic property that any natural number is either zero or greater than zero.

### Mathematical insight
This theorem formalizes the fundamental property that the natural numbers are non-negative. It is a basic case analysis principle frequently used in proofs about natural numbers. It captures the trichotomy law for the natural numbers with respect to zero.

### Dependencies
- `ARITH_RULE`


---

## LESS_OR

### Name of formal statement
LESS_OR

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_OR = ARITH_RULE `!m n. m < n ==> (SUC m) <= n`;;
```
### Informal statement
For all natural numbers `m` and `n`, if `m` is less than `n`, then the successor of `m` is less than or equal to `n`.

### Informal sketch
The proof proceeds by applying the arithmetic rule `ARITH_RULE`. This rule likely contains or invokes the basic axioms and definitions about the less-than (`<`) and less-than-or-equal (`<=`) relations on natural numbers, and the properties of the successor function `SUC`. The tactic automatically handles the basic arithmetic reasoning required to derive the conclusion from the premise based on the definitions of `<` , `<=` and `SUC`.

### Mathematical insight
The theorem formalizes the basic intuition about the ordering of natural numbers: if `m` is strictly less than `n`, then incrementing `m` by one will still result in a number that is at most `n`, formalizing a relation between strict and non-strict inequality of natural numbers. It is a fundamental property used in many proofs involving inequalities.

### Dependencies
- Theories:
  - Arithmetic (`ARITH`)

- Rules:
  - `ARITH_RULE`

### Porting notes (optional)
Most proof assistants have built-in support for arithmetic reasoning, although the automation level may vary. In systems with weaker automation, it might be necessary to explicitly unfold the definitions of `<` , `<=` and `SUC` and apply rewrite rules to complete the proof.


---

## SUB

### Name of formal statement
SUB

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUB = ARITH_RULE
  `(!m. 0 - m = 0) /\
   (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))`;;
```
### Informal statement
The following holds for all natural numbers:
- For all `m`, `0 - m` is equal to `0`.
- For all `m` and `n`, `(SUC m) - n` is equal to `0` if `m < n`, and equal to `SUC(m - n)` otherwise.

### Informal sketch
The theorem gives a recursive definition of subtraction on natural numbers, ensuring that subtraction always results in a natural number. The proof is done via the tactic `ARITH_RULE` which likely expands into a proof by induction.

*   The first clause `!m. 0 - m = 0` defines subtracting any number `m` from zero to be `0`.

*   The second clause `!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n))` recursively defines subtracting `n` from the successor of `m`. If `m` is less than `n`, the result is `0`. Otherwise, it's the successor of the result of subtracting `n` from `m`.

### Mathematical insight
This theorem defines subtraction on natural numbers, ensuring the result is always a natural number (i.e., no negative numbers). This is a standard way to define subtraction within a system that only has natural numbers. The use of a conditional expression ensures that the subtraction operation "bottoms out" at 0 when a larger number is subtracted from a smaller one.

### Dependencies
None

### Porting notes (optional)
When porting this definition, ensure that the target proof assistant supports defining functions recursively with pattern matching and conditional expressions. The natural number type and its successor function (`SUC`) need to be available. In systems like Coq, you might define subtraction as a fixpoint using pattern matching on the first argument. In Lean, you might use `nat.cases_on` or pattern matching.


---

## LESS_MULT_MONO

### Name of formal statement
LESS_MULT_MONO

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_MULT_MONO = prove
 (`!m i n. ((SUC n) * m) < ((SUC n) * i) <=> m < i`,
  REWRITE_TAC[LT_MULT_LCANCEL; NOT_SUC]);;
```
### Informal statement
For all natural numbers `m`, `i`, and `n`, `(SUC n) * m` is less than `(SUC n) * i` if and only if `m` is less than `i`.

### Informal sketch
The theorem states that multiplication by a successor is monotonic with respect to the less-than relation on natural numbers. The proof uses:
- `LT_MULT_LCANCEL`: This likely states that if `k * m < k * i` then `m < i` when `k` is positive, which is accomplished by multiplying with `(SUC n)`. This removes `(SUC n)` from both sides of the `<` sign.
- `NOT_SUC`: This likely refers to the fact that `m < i` if and only if `(SUC n) * m < (SUC n) * i`.

The overall structure is therefore a rewrite using these two theorems to accomplish the equivalence.

### Mathematical insight
This theorem establishes a fundamental property of the natural numbers: multiplication by a positive integer preserves the order relation. This is important because it allows one to cancel a common factor in inequalities when that factor is known to be positive (a successor of a natural number). This result underpins many arguments in number theory and real analysis, where inequalities are manipulated.

### Dependencies
- Theorems: `LT_MULT_LCANCEL`, `NOT_SUC`

### Porting notes (optional)
The main difficulty in porting this theorem lies in ensuring the counterparts of `LT_MULT_LCANCEL` and `NOT_SUC` are available and correctly applied. The bi-implication requires both directions to be established, so special care should be taken to verify that the cancellation operation works in both directions.


---

## LESS_MONO_MULT

### Name of formal statement
LESS_MONO_MULT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_MONO_MULT = prove
 (`!m n p. m <= n ==> (m * p) <= (n * p)`,
  SIMP_TAC[LE_MULT_RCANCEL]);;
```
### Informal statement
For all natural numbers `m`, `n`, and `p`, if `m` is less than or equal to `n`, then `m * p` is less than or equal to `n * p`.

### Informal sketch
The theorem states that multiplication by a natural number preserves the less than or equal to relation on natural numbers.

*   The proof is achieved using `SIMP_TAC` with the provided lemma `LE_MULT_RCANCEL`. This tactic likely simplifies the goal by applying pre-existing theorems about inequalities and multiplication, including the right cancellation property of multiplication with respect to the less than or equal to relation.

### Mathematical insight
This theorem establishes a fundamental property of the natural numbers, showing that the order relation is preserved under multiplication by a non-negative number. It's a basic result used in many arguments involving inequalities.

### Dependencies
- Theorems: `LE_MULT_RCANCEL`


---

## LESS_MULT2

### Name of formal statement
LESS_MULT2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_MULT2 = prove
 (`!m n. 0 < m /\ 0 < n ==> 0 < (m * n)`,
  REWRITE_TAC[LT_MULT]);;
```
### Informal statement
For all natural numbers `m` and `n`, if `0` is less than `m` and `0` is less than `n`, then `0` is less than `m * n`.

### Informal sketch
The theorem `LESS_MULT2` is proved by rewriting with the theorem `LT_MULT`. The theorem `LT_MULT` states that for all natural numbers `m`, `n`, and `p`, if `p` is greater than zero, then `m` is less than `n` if and only if `p * m` is less than `p * n`. Instantiating `LT_MULT` with `p` as `m`, and using the assumption that `0 < m` with the assumption that `0 < n`, we can show that `0 < m * n`.

### Mathematical insight
The theorem states a fundamental property of the natural numbers: the product of two positive natural numbers is positive. This is an essential result in arithmetic.

### Dependencies
- Theorems: `LT_MULT`


---

## SUBSET_FINITE

### Name of formal statement
SUBSET_FINITE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUBSET_FINITE = prove
 (`!s. FINITE s ==> (!t. t SUBSET s ==> FINITE t)`,
  MESON_TAC[FINITE_SUBSET]);;
```
### Informal statement
For any set `s`, if `s` is finite, then for any set `t`, if `t` is a subset of `s`, then `t` is finite.

### Informal sketch
The proof relies on the theorem `FINITE_SUBSET`, which directly states that any subset of a finite set is finite. The tactic `MESON_TAC[FINITE_SUBSET]` is used to apply this theorem, thereby proving the statement.

### Mathematical insight
This theorem formalizes the fundamental concept that subsets of finite sets are also finite. This is a basic result in set theory and is essential for reasoning about finiteness in various mathematical contexts.

### Dependencies
- Theorems: `FINITE_SUBSET`


---

## LESS_EQ_SUC

### Name of formal statement
LESS_EQ_SUC

### Type of the formal statement
theorem

### Formal Content
```ocaml
let LESS_EQ_SUC = prove
 (`!n. m <= SUC n <=> (m = SUC n) \/ m <= n`,
  REWRITE_TAC[LE]);;
```
### Informal statement
For all natural numbers `n`, `m`, `m` is less than or equal to the successor of `n` if and only if `m` is equal to the successor of `n` or `m` is less than or equal to `n`.

### Informal sketch
The theorem states an equivalence relation. The proof proceeds by:
- Rewriting the goal using the definition of less than or equal to (`LE`).

### Mathematical insight
This theorem provides a useful way to reason about the less than or equal to relation (`<=`) in terms of the successor function (`SUC`). It essentially states that `m <= SUC n` holds if either `m` is equal to `SUC n` (the maximum possible value) or `m` is already less than or equal to `n`. This is a fundamental property when reasoning inductively about inequalities.

### Dependencies
- Definitions: `LE`


---

## ANTE_RES_THEN

### Name of formal statement
ANTE_RES_THEN

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let ANTE_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP t th));;
```

### Informal statement
Given a tactic `ttac` and a theorem `th`, the theorem `ANTE_RES_THEN ttac th` applies the tactic `ttac` to the result of applying modus ponens (`MATCH_MP`) to the first assumption `t` for which `MATCH_MP t th` succeeds.

### Informal sketch
- The statement defines a tactic combinator `ANTE_RES_THEN`.
- The tactic `FIRST_ASSUM` attempts to apply a given function to each assumption in the goal, one at a time, from left to right and succeeds when the function succeeds for the first time.
- The function being applied is `fun t -> ttac (MATCH_MP t th)`.
- `MATCH_MP t th` attempts to match assumption `t` as the antecedent of the implication in the theorem `th`. If successful, it returns the instantiated consequent of `th`.
- The tactic `ttac` is then applied to the result of `MATCH_MP`.

### Mathematical insight
This tactic combinator is useful for applying a resolution-like inference step using a given assumption as the antecedent. It mechanizes the step of finding a matching assumption and applying a tactic to the result of the modus ponens.

### Dependencies
- `FIRST_ASSUM`
- `MATCH_MP`


---

## IMP_RES_THEN

### Name of formal statement
IMP_RES_THEN

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IMP_RES_THEN ttac th = FIRST_ASSUM(fun t -> ttac (MATCH_MP th t));;
```

### Informal statement
Given a tactic `ttac` and a theorem `th`, the tactic `IMP_RES_THEN ttac th` applies `ttac` to the result of Modus Ponens (MP) using `th` against the first assumption in the goal to which it applies. More precisely, it applies `MATCH_MP th t` where `t` is the first assumption, and then applies `ttac` to the resulting term.

### Informal sketch
The theorem defines a tactic combinator `IMP_RES_THEN`.

- The main idea is to take a theorem `th` and use it to perform Modus Ponens (`MATCH_MP th t`) with the first assumption `t` of the subgoal.
- The resulting term from the Modus Ponens application is then subjected to the tactic `ttac`.
- The `FIRST_ASSUM` tactic is used to find and apply the Modus Ponens result to the first assumption available.

### Mathematical insight
This tactic combinator provides a way to apply a theorem using Modus Ponens to an assumption, and then apply some other tactic to the result. This can be useful for chaining together inference steps. `IMP_RES_THEN` is essentially a resolution tactic.

### Dependencies
- `FIRST_ASSUM`
- `MATCH_MP`


---

## INFINITE_MEMBER

### Name of formal statement
INFINITE_MEMBER

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INFINITE_MEMBER = prove(
  `!s. INFINITE(s:A->bool) ==> ?x. x IN s`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(s:A->bool = {})` MP_TAC THENL
   [UNDISCH_TAC `INFINITE (s:A->bool)` THEN
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INFINITE; FINITE_EMPTY];
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
    PURE_ONCE_REWRITE_TAC[NOT_FORALL_THM] THEN
    REWRITE_TAC[]]);;
```
### Informal statement
For all sets `s` of type `A->bool`, if `s` is infinite, then there exists an `x` such that `x` is an element of `s`.

### Informal sketch
*   The proof proceeds by contradiction. It starts by assuming that `s` is infinite, and then introduces a subgoal assuming that `s` is empty.
*   It then uses the contrapositive of the definition of `INFINITE` and rewrites using the definitions of `INFINITE` and `FINITE_EMPTY`.
*   Then it uses `EXTENSION` to show that the set is not empty and uses `NOT_FORALL_THM` to introduce the existential quantifier.

### Mathematical insight
This theorem states a fundamental property of infinite sets: an infinite set must have at least one member. This is a basic result linking infinity and set membership.

### Dependencies
*   Definitions: `INFINITE`
*   Theorems: `EXTENSION`, `FINITE_EMPTY`, `NOT_IN_EMPTY`, `NOT_FORALL_THM`


---

## INFINITE_CHOOSE

### Name of formal statement
INFINITE_CHOOSE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INFINITE_CHOOSE = prove(
  `!s:A->bool. INFINITE(s) ==> ((@) s) IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_MEMBER) THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[IN] THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN REWRITE_TAC[]);;
```
### Informal statement
For any set `s` of type `A->bool`, if `s` is infinite, then the choice function applied to `s`, denoted by `(@) s`, is an element of `s`.

### Informal sketch
The proof proceeds as follows:
- Assume that `s` is infinite.
- Apply `INFINITE_MEMBER`, which states that if a set `s` is infinite, then there exists an element `x` in `s` such that `s` without `x` is infinite.
- Apply the `SELECT_RULE`, which essentially introduces Hilbert's choice operator `@` to pick an element from the infinite set.
- Rewrite using `IN` which characterizes membership using a set representation `s x`. The goal is now s((@) s).
- Apply `ETA_CONV` to simplify the term.
- Finally, rewrite using an empty rewrite tactic to complete the proof.

### Mathematical insight
This theorem states that if a set is infinite, then the choice function, which selects an arbitrary element from a set, will select an element that is indeed within the set. This is a basic property of the choice operator when applied to infinite sets and connects the notion of infinity with the ability to select elements from those sets.

### Dependencies
- Theorems: `INFINITE_MEMBER`
- Definitions: `IN`


---

## INFINITE_DELETE

### Name of formal statement
INFINITE_DELETE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INFINITE_DELETE = prove(
  `!(t:A->bool) x. INFINITE (t DELETE x) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_DELETE]);;
```
### Informal statement
For any predicate `t` on type `A` and any element `x` of type `A`, the set obtained by removing `x` from the set defined by `t` is infinite if and only if the set defined by `t` is infinite.

### Informal sketch
The proof proceeds by rewriting the goal using the definitions of `INFINITE` and `FINITE_DELETE`.
- The main step relies on the theorem `FINITE_DELETE`, which states that deleting an element from a finite set results in a finite set.
- The goal is `INFINITE (t DELETE x) = INFINITE t`. The theorem `FINITE_DELETE` is stated as `FINITE (t DELETE x) = FINITE t`.
- By negating both sides, we have `~(FINITE (t DELETE x)) = ~ (FINITE t)`.
- Then, the theorem `INFINITE t = ~(FINITE t)` transforms the goal into `~(FINITE (t DELETE x)) = ~ (FINITE t)`, which is the negated form of `FINITE_DELETE`.

### Mathematical insight
This theorem formalizes the intuitive idea that removing a single element from an infinite set does not change its infiniteness. It expresses that deleting an element `x` from a set selected by the filter `t` preserves infiniteness if and only if the original set was infinite.

### Dependencies
- Definitions: `INFINITE`
- Theorems: `FINITE_DELETE`


---

## INFINITE_INSERT

### Name of formal statement
INFINITE_INSERT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INFINITE_INSERT = prove(
  `!(x:A) t. INFINITE(x INSERT t) = INFINITE(t)`,
  REWRITE_TAC[INFINITE; FINITE_INSERT]);;
```
### Informal statement
For any set `t` of type `:A -> bool` and any element `x` of type `:A`, the set `x INSERT t` is infinite if and only if the set `t` is infinite.

### Informal sketch
The proof proceeds by rewriting the assertion using the definitions of `INFINITE` and `FINITE_INSERT`.
- The theorem expresses a fundamental relationship between the infiniteness of a set and the addition of a new element to that set. Specifically, adding a single element to a set does not change its infiniteness.

### Mathematical insight
The insight is that a finite modification (adding a single element) to a set cannot change its infiniteness. If the original set is infinite, adding an element won't make it finite. If the original set is finite, adding an element will keep it finite. This is a fundamental property when reasoning about the cardinality of sets.

### Dependencies
- Definitions:
    - `INFINITE`
    - `FINITE_INSERT`


---

## SIZE_INSERT

### Name of formal statement
SIZE_INSERT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIZE_INSERT = prove(
  `!(x:A) t. ~(x IN t) /\ t HAS_SIZE n ==> (x INSERT t) HAS_SIZE (SUC n)`,
  SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_RULES]);;
```
### Informal statement
For all `x` of type `A` and sets `t` of type `A`, if `x` is not in `t` and the size of `t` is `n`, then the size of `x INSERT t` is the successor of `n`.

### Informal sketch
The proof attempts to show that the cardinality of the set obtained by inserting an element `x` into a set `t` is the successor of the cardinality of `t`, given that `x` is not already in `t`.

- The proof uses simplification with the theorems related to `HAS_SIZE`, clause of `CARD_CLAUSES` and `FINITE_RULES`. These simplification rules likely reduce the statement to a more basic form that can be directly proven, possibly using the definition of `HAS_SIZE` over the cardinality of `t`, and the properties of `CARD_CLAUSES` (which describe the cardinality of various set operations) and `FINITE_RULES` (which are inference rules about finite sets).

### Mathematical insight
The theorem expresses the intuitive idea that adding a new element to a set increases its size by one. The condition `~(x IN t)` is crucial, as it ensures that `x` is not already a member of `t`; otherwise, inserting `x` would not change the size of the set. This is a fundamental result in set theory and is essential for reasoning about cardinalities and sizes of finite sets.

### Dependencies
- Definitions: `HAS_SIZE`
- Theorems/Rules: `CARD_CLAUSES`, `FINITE_RULES`


---

## SIZE_DELETE

### Name of formal statement
SIZE_DELETE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIZE_DELETE = prove(
  `!(x:A) t. x IN t /\ t HAS_SIZE (SUC n) ==> (t DELETE x) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE_SUC]);;
```
### Informal statement
For any set `t` of type `A` and any element `x` of type `A`, if `x` is in `t` and the size of `t` is the successor of `n`, then the size of `t` with `x` deleted is `n`.

### Informal sketch
The proof proceeds by simplifying using the theorem `HAS_SIZE_SUC`. This theorem likely provides a way to decompose the condition `t HAS_SIZE (SUC n)` into a statement involving an element and a set of size `n`, allowing the deletion to be directly related to that smaller set.

### Mathematical insight
The theorem states that if an element `x` is removed from a finite set `t` of size `n+1`, and `x` is an element of `t`, then the resulting set `t DELETE x` has size `n`. This aligns with the intuitive understanding of set cardinality and removal of elements. This theorem is useful for inductive proofs about set sizes.

### Dependencies
- Theorems: `HAS_SIZE_SUC`


---

## SIZE_EXISTS

### Name of formal statement
SIZE_EXISTS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SIZE_EXISTS = prove(
  `!s N. s HAS_SIZE (SUC N) ==> ?x:A. x IN s`,
  SIMP_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY]);;
```
### Informal statement
For all sets `s` and natural numbers `N`, if the set `s` has size `SUC N` (the successor of `N`), then there exists an element `x` in the universal type `:A` such that `x` is in `s`.

### Informal sketch
The proof proceeds as follows:
- Assume that the set `s` has size `SUC N`.
- Use `HAS_SIZE_SUC` to decompose the assumption `s HAS_SIZE (SUC N)` into a nonempty set membership.
- Use `GSYM MEMBER_NOT_EMPTY` to rewrite the conclusion.
- The theorem follows.

### Mathematical insight
This theorem states that if a set has a size that is the successor of a natural number, then the set is non-empty and contains at least one element.

### Dependencies
- Definitions: `HAS_SIZE_SUC`, `MEMBER_NOT_EMPTY`

### Porting notes (optional)
- The main challenge might be in finding or proving the equivalent of `HAS_SIZE_SUC` and `MEMBER_NOT_EMPTY` in the target proof assistant. The first likely comes from the definition of `HAS_SIZE`, the second from the fundamental nature of set theory.


---

## SUBSET_DELETE

### Name of formal statement
SUBSET_DELETE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let SUBSET_DELETE = prove(
  `!s t (x:A). s SUBSET t ==> (s DELETE x) SUBSET t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET]);;
```
### Informal statement
For all sets `s` and `t` of type A, and for all elements `x` of type A, if `s` is a subset of `t`, then `s` with element `x` removed (i.e., `s DELETE x`) is a subset of `t`.

### Informal sketch
The proof proceeds as follows:

- Assume `s SUBSET t`.
- By transitivity of `SUBSET` (using `SUBSET_TRANS`), reduce the goal to showing that `s DELETE x` is a subset of `s`.
- Existentially instantiate the subset with `s`.
- Rewrite using the definition of `DELETE_SUBSET` to show that `s DELETE x` is a subset of `s`.

### Mathematical insight
This theorem states that removing an element from a set `s` will result in a smaller set that is still a subset of the original containing set `t`. This is a standard property of sets and a fundamental lemma when manipulating sets within a formal system.

### Dependencies
- `SUBSET_TRANS`
- `DELETE_SUBSET`


---

## INFINITE_FINITE_CHOICE

### Name of formal statement
INFINITE_FINITE_CHOICE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let INFINITE_FINITE_CHOICE = prove(
  `!n (s:A->bool). INFINITE(s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  INDUCT_TAC THEN GEN_TAC THEN DISCH_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN
    REWRITE_TAC[HAS_SIZE; EMPTY_SUBSET; HAS_SIZE_0];
    FIRST_ASSUM(UNDISCH_TAC o check is_forall o concl) THEN
    DISCH_THEN(MP_TAC o SPEC `s DELETE ((@) s :A)`) THEN
    ASM_REWRITE_TAC[INFINITE_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `((@) s :A) INSERT t` THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
        GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        REWRITE_TAC[IN_DELETE] THEN CONV_TAC(EQT_INTRO o TAUT)];
        MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN UNDISCH_TAC `t SUBSET (s DELETE ((@) s:A))` THEN
        REWRITE_TAC[SUBSET; IN_DELETE] THEN
        DISCH_THEN(IMP_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]);;
```
### Informal statement
For all `n` and for all predicates `s` from `A` to boolean, if `s` is infinite then there exists a predicate `t` from `A` to boolean such that `t` is a subset of `s` and the size of `t` is `n`.

### Informal sketch
The proof proceeds by induction on `n`.
- Base case: Show that if `s` is infinite, there exists a set `t` which is a subset of `s` and the size of `t` is 0. We choose the empty set for `t`.
- Inductive step: Assume that for some `n`, if `s` is infinite, there exists a set `t` which is a subset of `s` and the size of `t` is `n`. We need to show that there exists a set `t'` which is a subset of `s` and the size of `t'` is `n+1`.
  - Since `s` is infinite, `s DELETE ((@) s)` is also infinite, where `(@)` is the Hilbert choice operator.
  - By the induction hypothesis, there exists a set `t` such that `t` is a subset of `s DELETE ((@) s)` and the size of `t` is `n`.
  - Let `t'` be `((@) s) INSERT t`. We need to show that `t'` is a subset of `s` and the size of `t'` is `n+1`.
    - `t'` is a subset of `s` because `((@) s)` is an element of `s` (by the properties of the Hilbert choice operator), and `t` is a subset of `s DELETE ((@) s)`, which is a subset of `s`.
    - The size of `t'` is `n+1` because the size of `t` is `n` and `((@) s)` is not an element of `t` (since `t` is a subset of `s DELETE ((@) s)`).

### Mathematical insight
This theorem states a fundamental property connecting infinite sets and finite subsets. It asserts that any infinite set contains subsets of every finite cardinality. This theorem may be considered as a choice principle stating that we can always choose subsets of any finite size from an infinite set.

### Dependencies
- Definitions: `INFINITE`, `SUBSET`, `HAS_SIZE`
- Theorems: `HAS_SIZE`, `EMPTY_SUBSET`, `HAS_SIZE_0`, `INFINITE_DELETE`, `SIZE_INSERT`, `INSERT_SUBSET`
- Axioms: `INFINITE_CHOOSE`

### Porting notes (optional)
This theorem relies on the Hilbert choice operator (`@`). Proof assistants that do not have this operator as primitive need to either import an axiom of choice or use a constructive equivalent which will substantially change the proof structure. Careful consideration is needed when porting the proof to systems like Coq, which favor constructive foundations. The induction tactic used in HOL Light may require adaptation to the specific induction schemes provided in the target proof assistant.


---

## IMAGE_WOP_LEMMA

### Name of formal statement
IMAGE_WOP_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let IMAGE_WOP_LEMMA = prove(
  `!N (t:num->bool) (u:A->bool).
        u SUBSET (IMAGE f t) /\ u HAS_SIZE (SUC N) ==>
        ?n v. (u = (f n) INSERT v) /\
              !y. y IN v ==> ?m. (y = f m) /\ n < m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\n:num. ?y:A. y IN u /\ (y = f n)` num_WOP) THEN BETA_TAC THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  FIRST_ASSUM(X_CHOOSE_TAC `y:A` o MATCH_MP SIZE_EXISTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `y:A` o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
       funpow 2 (fst o dest_imp) o snd) THENL
   [MAP_EVERY EXISTS_TAC [`n:num`; `y:A`] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `u DELETE (x:A)`] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INSERT_DELETE THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    X_GEN_TAC `z:A` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:A` o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[GSYM NOT_LESS_EQUAL] THEN
    REWRITE_TAC[LESS_OR_EQ; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [DISCH_THEN(ANTE_RES_THEN (MP_TAC o CONV_RULE NOT_EXISTS_CONV)) THEN
      DISCH_THEN(MP_TAC o SPEC `z:A`) THEN REWRITE_TAC[] THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(z:A = x)` THEN ASM_REWRITE_TAC[]]]);;
```

### Informal statement
For any natural number `N`, any set `t` of natural numbers, and any set `u` of elements of type `A`, if `u` is a subset of the image of `t` under the function `f`, and `u` has size `SUC N` (the successor of N), then there exist a natural number `n` and a set `v` of elements of type `A` such that `u` equals the insertion of `f n` into `v`, and for all `y` in `v`, there exists a natural number `m` such that `y` equals `f m` and `n` is less than `m`.

### Informal sketch
The proof proceeds by induction on the size of the set `u`.

- First, the well-ordering principle for natural numbers (`num_WOP`) is applied to the set of numbers `n` for which `f n` is an element of `u`, establishing the existence of a minimal such `n`.
- Then, a witness `n` is chosen so that `f n` is in `u`.
- We show that the set `u` is equal to `INSERT (f n) (u DELETE (f n))`. This involves showing that `f n` is in `u` and `u DELETE (f n)` has the appropriate properties.
- The goal is to show that `u = (f n) INSERT v` for some `v:A->bool` such that `!y. y IN v ==> ?m. (y = f m) /\ n < m`.
- We define `v` as `u DELETE (x:A)` where `x` is in `u` such that `x = f n`.
- We prove the equality `u = INSERT (f n) (u DELETE (f n))`.  Since `x = f n`, using properties of `INSERT` and `DELETE`, we show that inserting `f n` into what remains after deleting `x` ( where `x = f n`) produces `u`.
- We need to show that any element `y` in `v` has the form `f m` where `n < m`. Thus, we assume z is in the set `u DELETE x` and show that `z = f k` where `n < k` for some `k`.
- Since `z` is in `u DELETE x` then `z` is in `u` and `z` is not `x`. Since `u` is a subset of `IMAGE f t`, then `z = f k` for some `k`.
- Further, since x was chosen to be `f n` where n is the smallest number satisfying this property, we show that `n < k` must hold by contradiction.

### Mathematical insight
The theorem states that if a set `u` of size `SUC N` is a subset of the image of a function `f` applied to a set of natural numbers `t`, then `u` can be expressed as the insertion of `f n` into a set `v`, where every element in `v` is in the image of `f` and its pre-image is greater than `n`. In other words, it decomposes a finite set `u` contained in the image of `f` into the smallest element (according to `f`'s pre-image) and the rest. This is a useful step in many inductive proofs.

### Dependencies
- `num_WOP`
- `SIZE_EXISTS`
- `SUBSET`
- `IN_IMAGE`
- `INSERT_DELETE`
- `IN_DELETE`
- `NOT_LESS_EQUAL`
- `LESS_OR_EQ`
- `DE_MORGAN_THM`
- `NOT_EXISTS_CONV`


---

## COLOURING_LEMMA

### Name of formal statement
COLOURING_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLOURING_LEMMA = prove(
  `!M col s. (INFINITE(s) /\ !n:A. n IN s ==> col(n) <= M) ==>
          ?c t. t SUBSET s /\ INFINITE(t) /\ !n:A. n IN t ==> (col(n) = c)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LESS_EQ_0] THEN REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`0`; `s:A->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL];
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `INFINITE { x:A | x IN s /\ (col x = SUC M) } \/
      INFINITE { x:A | x IN s /\ col x <= M}`
    DISJ_CASES_TAC THENL
     [UNDISCH_TAC `INFINITE(s:A->bool)` THEN
      REWRITE_TAC[INFINITE; GSYM DE_MORGAN_THM; GSYM FINITE_UNION] THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
      DISCH_THEN(MATCH_MP_TAC o MATCH_MP SUBSET_FINITE) THEN
      REWRITE_TAC[SUBSET; IN_UNION] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM LESS_EQ_SUC] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`SUC M`; `{ x:A | x IN s /\ (col x = SUC M)}`] THEN
      ASM_REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `!n:A. n IN { x | x IN s /\ col x <= M } ==> col(n) <= M`
      MP_TAC THENL
       [GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_THEN(MATCH_ACCEPT_TAC o CONJUNCT2);
        FIRST_X_ASSUM(MP_TAC o SPECL [`col:A->num`;
                                        `{ x:A | x IN s /\ col x <= M}`]) THEN
        ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC(TAUT `(c ==> d) ==> (b ==> c) ==> b ==> d`) THEN
        DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `t:A->bool`)) THEN
        MAP_EVERY EXISTS_TAC [`c:num`; `t:A->bool`] THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `{ x:A | x IN s /\ col x <= M }` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]]]);;
```

### Informal statement
For any set `s` of type `A` (where `A` is the type of the natural numbers) and any natural number `M`, if `s` is infinite, and for all `n` in `s`, the color of `n` (given by the function `col`) is less than or equal to `M`, then there exists a color `c` and a set `t` which is a subset of `s` such that `t` is infinite and for all `n` in `t`, the color of `n` is equal to `c`.

### Informal sketch
The proof proceeds by induction on `M`.
- **Base case (M = 0):**
  -  If all elements `n` in `s` have `col(n) <= 0`, then since `col(n)` is a natural number, it must be 0. So we can take `c = 0` and `t = s` which satisfies the desired condition, since `s` is infinite by assumption.
- **Inductive step:**
  - Assume the statement holds for `M`. We want to prove it for `SUC M`.
  - We know that `INFINITE(s)` and `!n:A. n IN s ==> col(n) <= SUC M`.
  - Perform a case split on whether the set `{ x:A | x IN s /\ (col x = SUC M) }` is infinite or the set `{ x:A | x IN s /\ col x <= M }` is infinite.
    - **Case 1: `{ x:A | x IN s /\ (col x = SUC M) }` is infinite.** In this case, take `c = SUC M` and `t = { x:A | x IN s /\ (col x = SUC M) }`.  Then `t` is a subset of `s`, `t` is infinite, and every element in `t` has color `SUC M`.
    - **Case 2: `{ x:A | x IN s /\ col x <= M }` is infinite.** Apply the inductive hypothesis to the set `{ x:A | x IN s /\ col x <= M }`. This gives us a color `c` and an infinite subset `t` of `{ x:A | x IN s /\ col x <= M }` such that all elements in `t` have color `c` and `c <= M`. Since `t` is a subset of `{ x:A | x IN s /\ col x <= M }`, it is also a subset of `s`.

### Mathematical insight
This lemma formalizes the pigeonhole principle for infinite sets with a bounded number of colors. It essentially says that if you color an infinite set of natural numbers with finitely many colors (bounded by `M`), then there must exist an infinite subset of those numbers that all have the same color. This is a crucial step in many Ramsey theory arguments.

### Dependencies
- `INFINITE`
- `FINITE_UNION`
- `DE_MORGAN_THM`
- `SUBSET_FINITE`
- `SUBSET`
- `IN_UNION`
- `IN_ELIM_THM`
- `LESS_EQ_SUC`
- `SUBSET_REFL`
- `LESS_EQ_0`

### Porting notes (optional)
- The HOL Light library `finite.ml` contains formalizations of `INFINITE` and `FINITE` that are useful in this proof.
- The proof relies on rewriting and simplification tactics which may need to be adapted to the specific rewriting engines of other proof assistants.
- The underlying concepts should be readily portable to systems like Coq, Lean, or Isabelle, although the inductive tactic structure may differ.


---

## COLOURING_THM

### Name of formal statement
COLOURING_THM

### Type of the formal statement
theorem

### Formal Content
```ocaml
let COLOURING_THM = prove(
  `!M col. (!n. col n <= M) ==>
           ?c s. INFINITE(s) /\ !n:num. n IN s ==> (col(n) = c)`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL [`M:num`; `col:num->num`; `UNIV:num->bool`] COLOURING_LEMMA) THEN
  ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_TAC `t:num->bool`)) THEN
  MAP_EVERY EXISTS_TAC [`c:num`; `t:num->bool`] THEN ASM_REWRITE_TAC[]);;
```

### Informal statement
For all `M` and `col`, if for all `n`, `col(n)` is less than or equal to `M`, then there exists `c` and `s` such that `s` is infinite and for all `n`, if `n` is in `s`, then `col(n)` equals `c`.

### Informal sketch
The proof demonstrates that if a function `col` from natural numbers to natural numbers is bounded above by some `M`, then there exists an infinite set `s` of natural numbers such that `col` is constant on `s`.
- Start by stripping the quantifiers and implication.
- Apply `COLOURING_LEMMA` with appropriate specializations for `M`, `col`, and the universal set `UNIV`. `COLOURING_LEMMA` likely asserts that for any bounded coloring of the natural numbers, there exists a color and an infinite set such that all elements of the set are mapped to that color.
- Rewrite using the definition of `num_INFINITE` (likely a definition of what it means for a set of numbers to be infinite).
- Discharge the assumption and choose witness `c` and `t` (representing an infinite set) using `X_CHOOSE_TAC`.
- Introduce the existential quantifiers for `c` and `t`, asserting the existence of a color and an infinite set.
- Rewrite with assumptions.

### Mathematical insight
This theorem states that any bounded coloring of the natural numbers must have a monochromatic infinite subset. This captures a basic version of the infinite Ramsey theorem for numbers. It is important because it shows that even with infinitely many numbers, if colored according to some bounded scheme, there must be infinite order.

### Dependencies
- `COLOURING_LEMMA`
- `num_INFINITE`

### Porting notes (optional)
The main challenge in porting this proof lies in the tactic `X_CHOOSE_TAC`, which performs a choice operation based on provability. In other proof assistants, one would need to explicitly invoke the axiom of choice to obtain the witnesses `c` and `t` and then proceed with the proof by explicitly constructing the existential witnesses. Ensuring that `num_INFINITE` is defined appropriately in the target system is crucial for the rewriting step to succeed.


---

## RAMSEY_LEMMA1

### Name of formal statement
RAMSEY_LEMMA1

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA1 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
         ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                   (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                      (!u. u SUBSET t /\ u HAS_SIZE N
                           ==> (C(((@) s) INSERT u) = c))`,
  DISCH_THEN((THEN) (REPEAT STRIP_TAC) o MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `\u. C (((@) s :A) INSERT u):num`) THEN
  DISCH_THEN(MP_TAC o SPEC `s DELETE ((@)s:A)`) THEN BETA_TAC THEN
  ASM_REWRITE_TAC[INFINITE_DELETE] THEN
  W(C SUBGOAL_THEN (fun t ->REWRITE_TAC[t]) o
        funpow 2 (fst o dest_imp) o snd) THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `t SUBSET (s DELETE ((@) s :A))` THEN
      REWRITE_TAC[SUBSET; IN_INSERT; IN_DELETE; NOT_IN_EMPTY] THEN
      DISCH_TAC THEN GEN_TAC THEN DISCH_THEN DISJ_CASES_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC INFINITE_CHOOSE;
        FIRST_ASSUM(ANTE_RES_THEN ASSUME_TAC)] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `t SUBSET (s DELETE ((@) s :A))` THEN
      ASM_REWRITE_TAC[SUBSET; IN_DELETE] THEN
      DISCH_THEN(MP_TAC o SPEC `(@)s:A`) THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`t:A->bool`; `c:num`] THEN ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_DELETE]) THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN
      GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN(fun th -> REWRITE_TAC[th]));
      DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[]]]);;
```

### Informal statement
For all colorings `C` of sets and for all sets `s` of elements of type `A`, if `s` is infinite and for all sets `t` that are subsets of `s` and have size `N`, the color `C(t)` is less than or equal to `M`, then there exists a set `t` and a color `c` such that `t` is infinite, `t` is a subset of `s` and for all sets `u` that are subsets of `t` and have size `N`, the color `C(u)` is equal to `c`; implies that for all colorings `C` of sets and for all sets `s` of elements of type `A`, if `s` is infinite and for all sets `t` that are subsets of `s` and have size `SUC N` (the successor of `N`), the color `C(t)` is less than or equal to `M`, then there exists a set `t` and a color `c` such that `t` is infinite, `t` is a subset of `s`, the element `@ s` (an arbitrary element from `s`) is not in `t`, and for all sets `u` that are subsets of `t` and have size `N`, the color `C` applied to the set obtained by inserting the element `@ s` into `u` is equal to `c`.

### Informal sketch
The proof proceeds by induction on the size of the coloured sets.

- The theorem is proved by discharging the assumption of the implication, applying the first assumption to a suitably instantiated function and a set. 
- The instantiation uses `\u. C (((@) s :A) INSERT u):num` and `s DELETE ((@)s:A)`. Then `BETA_TAC` is used for beta reduction.
- Using `INFINITE_DELETE`, the goal is rewritten. The goal is then split into two subgoals utilizing the assumption `INFINITE(s:A->bool) /\ (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M) ==> ?t c. INFINITE(t) /\ t SUBSET s /\ (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c))`.
- The first subgoal is proved by rewriting with `SUBSET`, the definition of `IN_INSERT`, `IN_DELETE` and `NOT_IN_EMPTY`. Then by considering cases (with `DISJ_CASES_TAC`) of whether `@ s` is an element of `t`. We use `INFINITE_CHOOSE` and assumption discharging.
- The second subgoal is proved by choosing `t:A->bool` and `c:num`. Then we rewrite using `SUBSET` and assumption discharging.

### Mathematical insight
This theorem is a step towards a Ramsey-type result. It establishes a relationship between colorings of sets of size `SUC N` and the existence of a homogeneous subset for sets of size `N`. This serves as an inductive step for proving a more general Ramsey theorem.

### Dependencies
- `INFINITE_DELETE`
- `SUBSET`
- `IN_INSERT`
- `IN_DELETE`
- `NOT_IN_EMPTY`
- `INFINITE_CHOOSE`
- `SIZE_INSERT`

### Porting notes (optional)
- The heavy use of tactics such as `DISCH_THEN` and `ASM_REWRITE_TAC` suggests that significant automation is being employed in this proof. Recreating this proof in other systems might require similar automation capabilities or a more manual, step-by-step approach.
- The manipulation of sets using operations like `INSERT` and `DELETE`, as well as reasoning about `SUBSET` relationships, will need to be translated carefully into the target proof assistant's library for sets.


---

## RAMSEY_LEMMA2

### Name of formal statement
RAMSEY_LEMMA2

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA2 = prove(
 `(!C s. INFINITE(s:A->bool) /\
         (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\ ~(((@) s) IN t) /\
                  (!u. u SUBSET t /\ u HAS_SIZE N
                       ==> (C(((@) s) INSERT u) = c)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t x col. (!n. col n <= M) /\
                          (!n. (t n) SUBSET s) /\
                          (!n. t(SUC n) SUBSET (t n)) /\
                          (!n. ~((x n) IN (t n))) /\
                          (!n. x(SUC n) IN (t n)) /\
                          (!n. (x n) IN s) /\
                          (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                 ==> (C((x n) INSERT u) = col n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `\s (n:num). @t:A->bool. ?c:num.
      INFINITE(t) /\
      t SUBSET s /\
      ~(((@) s) IN t) /\
      !u. u SUBSET t /\ u HAS_SIZE N ==> (C(((@) s) INSERT u) = c)`]
    num_Axiom) THEN DISCH_THEN(MP_TAC o BETA_RULE o EXISTENCE) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->(A->bool)` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n:num. (f n) SUBSET (s:A->bool) /\
    ?c. INFINITE(f(SUC n)) /\ f(SUC n) SUBSET (f n) /\
        ~(((@)(f n)) IN (f(SUC n))) /\
        !u. u SUBSET (f(SUC n)) /\ u HAS_SIZE N ==>
          (C(((@)(f n)) INSERT u) = c:num)`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      FIRST_ASSUM(SUBST1_TAC o SPEC `0`) THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `f(n:num):A->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      FIRST_ASSUM(SUBST1_TAC o SPEC `SUC n`) THEN CONV_TAC SELECT_CONV THEN
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
      TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC SUBSET_TRANS THEN
        FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
        CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC])) THEN
      MATCH_ACCEPT_TAC SUBSET_REFL];
    PURE_REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM;
                     FORALL_AND_THM] THEN
    DISCH_THEN(REPEAT_TCL (CONJUNCTS_THEN2 ASSUME_TAC) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `col:num->num` o CONV_RULE SKOLEM_CONV) THEN
    MAP_EVERY EXISTS_TAC
      [`\n:num. f(SUC n):A->bool`; `\n:num. (@)(f n):A`] THEN
    BETA_TAC THEN EXISTS_TAC `col:num->num` THEN CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP INFINITE_FINITE_CHOICE o SPEC `n:num`) THEN
      DISCH_THEN(CHOOSE_THEN MP_TAC o SPEC `N:num`) THEN
      DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
          ANTE_RES_THEN MP_TAC th) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
         [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          EXISTS_TAC `n:num` THEN MATCH_MP_TAC INFINITE_CHOOSE THEN
          SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
          TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `f(SUC n):A->bool` THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC SIZE_INSERT THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `!n:num. ~(((@)(f n):A) IN (f(SUC n)))` THEN
        DISCH_THEN(MP_TAC o SPEC `n:num`) THEN CONV_TAC CONTRAPOS_CONV THEN
        REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_ACCEPT_TAC o REWRITE_RULE[SUBSET])];
      REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM MATCH_ACCEPT_TAC) THENL
       [GEN_TAC; INDUCT_TAC THENL
         [ASM_REWRITE_TAC[];
          FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          EXISTS_TAC `SUC n`]] THEN
      MATCH_MP_TAC INFINITE_CHOOSE THEN ASM_REWRITE_TAC[]]]);;
```

### Informal statement
For all sets `C` of sets of elements of type `A`, and for all infinite sets `s` of type `A->bool`, if every subset `t` of `s` of size `SUC N` has `C(t)` less than or equal to `M`, then there exist an infinite set `t` and an element `c` such that `t` is a subset of `s`, `@ s` is not in `t`, and for all `u` which is a subset of `t` and has size `N`, `C((@ s) INSERT u)` equals `c`; implies that for all sets `C` of sets of elements of type `A`, and for all infinite sets `s` of type `A->bool`, if every subset `t` of `s` of size `SUC N` has `C(t)` less than or equal to `M`, then there exist functions `t`, `x`, and `col` such that for all `n`, `col n` is less than or equal to `M`, for all `n`, `t n` is a subset of `s`, for all `n`, `t (SUC n)` is a subset of `t n`, for all `n`, `x n` is not in `t n`, for all `n`, `x (SUC n)` is in `t n`, for all `n`, `x n` is in `s`, and for all `n` and `u`, if `u` is a subset of `t n` and `u` has size `N`, then `C((x n) INSERT u)` equals `col n`.

### Informal sketch
The proof proceeds by induction. The main idea is to iteratively construct sets `t n` and elements `x n` such that the coloring `C`, when applied to sets formed by inserting `x n` into subsets of `t n` of size `N`, is constant, as expressed by the coloring function `col n`.

- The proof begins by stripping the quantifiers and assumptions.
- It uses the axiom of choice to show that there exists a function `f` that maps each natural number `n` to a boolean function `A->bool`.
- A subgoal is set up requiring that for every `n`, `f n` is a subset of `s`, and there exists an `c` such that `f (SUC n)` is infinite, `f (SUC n)` is a subset of `f n`, `@ (f n)` is not in `f (SUC n)`, and for all `u` which is a subset of `f (SUC n)` and has size `N`, `C((@ (f n)) INSERT u)` equals `c`.
- This subgoal is proven by induction on `n`.
  - In the base case (`n = 0`), we must show that `f 0` is a subset of `s`.
  - In the inductive step, we assume the subgoal holds for `n` and prove it for `SUC n`. This step involves showing that `f (SUC n)` is a subset of `f n`.
- After proving the subgoal, the main goal is approached.
- Skolemization is used to introduce a function `col` that maps natural numbers to numbers.
- Existential quantifiers are introduced for the functions `t`, `x`, and `col`.
- The remaining proof steps involve demonstrating that the constructed functions satisfy the required conditions. Notably, the use of `INFINITE_FINITE_CHOICE` and `INFINITE_CHOOSE` become necessary to ensure that infinite subsets are properly constructed and elements are selected in the inductive steps of this construction.

### Mathematical insight
This lemma is part of a proof related to Ramsey's theorem. The intuition is that given an infinite set `s` and a coloring `C` of its subsets of a certain size, one can find a structured way (via functions `t`, `x`, and `col`) to extract elements and sets such that the coloring `C` exhibits a degree of uniformity. Specifically, `col n` represents a coloring applied to the subsets created by inserting `x n` into appropriate subsets of `t n`.

### Dependencies
- Axioms:
  - `num_Axiom`

- Theorems:
  - `SUBSET_REFL`
  - `SUBSET_TRANS`
  - `LEFT_EXISTS_AND_THM`
  - `RIGHT_EXISTS_AND_THM`
  - `FORALL_AND_THM`
  - `INSERT_SUBSET`
  - `INFINITE_FINITE_CHOICE`
  - `INFINITE_CHOOSE`
  - `SIZE_INSERT`

- Definitions:
  - `SUBSET`
  - `HAS_SIZE`
  - `INSERT`
  - `INFINITE`

### Porting notes (optional)
*   The proof makes extensive use of higher-order functions and choice principles, requiring careful attention to the handling of quantifiers and binders in the target proof assistant.
*   The tactics `STRIP_TAC`, `MP_TAC`, `DISCH_TAC`, `X_CHOOSE_TAC`, `SUBGOAL_THEN`, `MATCH_MP_TAC`, `ASM_REWRITE_TAC`, `CONV_TAC`, `EXISTS_TAC`, `CONJ_TAC`, `FIRST_ASSUM`, `MATCH_ACCEPT_TAC`, `REPEAT`, `PURE_REWRITE_TAC`, `MAP_EVERY`, `BETA_TAC`, `X_GEN_TAC`, `ANTE_RES_THEN`, `UNDISCH_TAC`, `TRY`, `GEN_TAC`,`INDUCT_TAC` indicates the goal-directed style used in HOL Light. Recreating the proof may benefit from a more declarative style in systems like Isabelle/Isar or Coq.
*   The reliance on `SKOLEM_CONV` to introduce `col` suggests a need for proper Skolemization support in the target system.


---

## RAMSEY_LEMMA3

### Name of formal statement
RAMSEY_LEMMA3

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RAMSEY_LEMMA3 = prove(
 `(!C s. INFINITE(s:A->bool) /\
             (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
             ==> ?t x col. (!n. col n <= M) /\
                           (!n. (t n) SUBSET s) /\
                           (!n. t(SUC n) SUBSET (t n)) /\
                           (!n. ~((x n) IN (t n))) /\
                           (!n. x(SUC n) IN (t n)) /\
                           (!n. (x n) IN s) /\
                           (!n u. u SUBSET (t n) /\ u HAS_SIZE N
                                  ==> (C((x n) INSERT u) = col n)))
  ==> !C s. INFINITE(s:A->bool) /\
            (!t. t SUBSET s /\ t HAS_SIZE (SUC N) ==> C(t) <= M)
            ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                      (!u. u SUBSET t /\ u HAS_SIZE (SUC N) ==> (C(u) = c))`,
  DISCH_THEN((THEN) (REPEAT STRIP_TAC) o MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`C:(A->bool)->num`; `s:A->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->(A->bool)` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->A` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `col:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`M:num`; `col:num->num`; `UNIV:num->bool`]
    COLOURING_LEMMA) THEN ASM_REWRITE_TAC[num_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (x:num->A) t`; `c:num`] THEN
  SUBGOAL_THEN `!m n. m <= n ==> (t n:A->bool) SUBSET (t m)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[LESS_EQ_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t(m + d):A->bool` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> (x n:A) IN (t m)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`m:num`; `m + d`]) THEN
    REWRITE_TAC[LESS_EQ_ADD; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM ADD1; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ((x:num->A) m = x n) <=> (m = n)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (SPECL [`m:num`; `n:num`] LESS_LESS_CASES) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      FIRST_ASSUM(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REFL_TAC]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `INFINITE(t:num->bool)` THEN
    MATCH_MP_TAC INFINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN GEN_TAC THEN
    DISCH_THEN(CHOOSE_THEN (SUBST1_TAC o CONJUNCT1)) THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(MP_TAC o MATCH_MP IMAGE_WOP_LEMMA) THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `v:A->bool` MP_TAC)) THEN
    DISCH_THEN STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c = (col:num->num) n` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `u SUBSET (IMAGE (x:num->A) t)` THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `(x:num->A) n`) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN
      DISCH_THEN(CHOOSE_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN GEN_TAC THEN
        DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
        DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `v = u DELETE ((x:num->A) n)` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN REWRITE_TAC[DELETE_INSERT] THEN
          REWRITE_TAC[EXTENSION; IN_DELETE;
            TAUT `(a <=> a /\ b) <=> a ==> b`] THEN
          GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[] THEN
          DISCH_THEN SUBST1_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
          ASM_REWRITE_TAC[LESS_REFL];
          MATCH_MP_TAC SIZE_DELETE THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[IN_INSERT]; FIRST_ASSUM MATCH_ACCEPT_TAC]]]]]);;
```

### Informal statement
For any set `s` of type `A`, if `s` is infinite, and for any subset `t` of `s` that has size `SUC N` (where `N` is a natural number), a coloring `C` of `t` is bounded by `M` (where `M` is a natural number), then there exist a function `t` from natural numbers to sets of type `A`, a function `x` from natural numbers to `A`, and a function `col` from natural numbers to natural numbers, such that the coloring `col` is bounded by `M`, for any natural number `n`, `t n` is a subset of `s`, `t(SUC n)` is a subset of `t n`, `x n` is not an element of `t n`, `x(SUC n)` is an element of `t n`, `x n` is an element of `s`, and for any set `u` that is a subset of `t n` and has size `N`, `C((x n) INSERT u)` equals `col n`.
This implies that for any set `s` of type `A`, if `s` is infinite, and for any subset `t` of `s` that has size `SUC N`, a coloring `C` of `t` is bounded by `M`, then there exist a set `t` and a natural number `c` such that `t` is infinite, `t` is a subset of `s`, and for any set `u` that is a subset of `t` and has size `SUC N`, `C(u)` equals `c`.

### Informal sketch
The proof proceeds as follows:
- Assume that for any coloring `C` and infinite set `s`, if `C` is bounded on subsets of `s` of size `SUC N`, then there exist functions `t`, `x`, and `col` satisfying the given conditions.
- Instantiate `COLOURING_LEMMA` with `M`, `col`, and the universal set, obtaining a set `c` and a function `t` with certain properties.
- Construct the desired infinite set and coloring `c` by taking the image of `t` under `x` and the previously chosen `c`.
- Show that `t n` is a subset of `t m` if `m <= n`. This is proved by induction on `n`.
- Show that `x n` is an element of `t m` if `m < n`.
- Show that `x m = x n` if and only if `m = n`. This relies on case analysis using `<` and `>` to prove equality.
- Prove that `IMAGE x t` is infinite using `INFINITE_IMAGE_INJ`. This lemma states that the image of an infinite set under an injective function is infinite.
- Show that `IMAGE x t` is a subset of `s` given the properties of `x` and `t` from the initial `choose` assumptions.
- Show that for any `u` subset of `IMAGE x t` with size `SUC N`, `C u = c`.  This involves several steps:
  - Choose a witness for the definition of subset of the image.
  - Show that `v = u DELETE (x n)` for a suitable `n`, where `v` is a subset of `t n` with size `N`.
  - The proof then uses the fact that `C((x n) INSERT u) = col n = c`.

### Mathematical insight
This theorem is a version of Ramsey's theorem. It states that if we color the subsets of a certain size of an infinite set using a finite number of colors, then there exists an infinite subset all of whose subsets of the given size have the same color.

### Dependencies
- `INFINITE`
- `SUBSET`
- `HAS_SIZE`
- `INSERT`
- `COLOURING_LEMMA`
- `num_INFINITE`
- `IMAGE`
- `LESS_EQ_EXISTS`
- `LESS_ADD_1`
- `LESS_LESS_CASES`
- `INFINITE_IMAGE_INJ`
- `SUBSET`
- `IN_IMAGE`
- `IMAGE_WOP_LEMMA`
- `SUBSET`
- `IN_IMAGE`
- `IN_INSERT`
- `LESS_REFL`
- `SIZE_DELETE`
- `DELETE_INSERT`
- `EXTENSION`
- `IN_DELETE`

### Porting notes (optional)
- The heavy use of higher-order functions and set theory may require careful translation into systems with different foundations.
- The extensive use of `CHOOSE_THEN` indicates the need for good automation for existential reasoning.
- The proof involves significant rewriting and equational reasoning, so good support for these tactics is important.


---

## RAMSEY

### Name of formal statement
RAMSEY

### Type of the formal statement
theorem

### Formal Content
```ocaml
let RAMSEY = prove(
  `!M N C s.
        INFINITE(s:A->bool) /\
        (!t. t SUBSET s /\ t HAS_SIZE N ==> C(t) <= M)
        ==> ?t c. INFINITE(t) /\ t SUBSET s /\
                  (!u. u SUBSET t /\ u HAS_SIZE N ==> (C(u) = c))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:A->bool`; `(C:(A->bool)->num) {}`] THEN
    ASM_REWRITE_TAC[HAS_SIZE_0] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    MAP_EVERY MATCH_MP_TAC [RAMSEY_LEMMA3; RAMSEY_LEMMA2; RAMSEY_LEMMA1] THEN
    POP_ASSUM MATCH_ACCEPT_TAC]);;
```

### Informal statement
For all `M`, `N`, `C`, and `s`, if `s` is an infinite set (represented as a boolean function), and for all `t`, if `t` is a subset of `s` and `t` has size `N`, then `C(t)` is less than or equal to `M`, then there exist `t` and `c` such that `t` is an infinite set, `t` is a subset of `s`, and for all `u`, if `u` is a subset of `t` and `u` has size `N`, then `C(u)` equals `c`.

### Informal sketch
The proof proceeds by induction.

- The base case is handled by stripping the quantifiers, introducing existential variables using `EXISTS_TAC`, and rewriting with `HAS_SIZE_0`. After further quantifier stripping and rewriting with `SUBSET_REFL`, it closes automatically.
- The inductive step relies on applications of `RAMSEY_LEMMA1`, `RAMSEY_LEMMA2`, and `RAMSEY_LEMMA3`.

### Mathematical insight
This theorem expresses a form of Ramsey's theorem for infinite sets. It states that if we color the subsets of size `N` of an infinite set `s` with colors from `0` to `M`, then there exists an infinite subset `t` of `s` such that all subsets of `t` of size `N` have the same color.

### Dependencies
- Definitions: `INFINITE`, `SUBSET`, `HAS_SIZE`
- Theorems: `RAMSEY_LEMMA1`, `RAMSEY_LEMMA2`, `RAMSEY_LEMMA3`, `HAS_SIZE_0`, `SUBSET_REFL`

### Porting notes (optional)
The use of higher-order logic in representing sets as boolean functions might require adaptation depending on the target proof assistant. The specific lemmas `RAMSEY_LEMMA1`, `RAMSEY_LEMMA2`, and `RAMSEY_LEMMA3` are crucial; ensure that similar results are available or provable in the target system. The `GEN_TAC`, `INDUCT_TAC`, `STRIP_TAC`, `EXISTS_TAC`, `ASM_REWRITE_TAC`, `MATCH_MP_TAC`, and `POP_ASSUM MATCH_ACCEPT_TAC` tactics are HOL Light-specific, so the proof strategy must be re-implemented using equivalent tactics or proof methods in the target system.


---

