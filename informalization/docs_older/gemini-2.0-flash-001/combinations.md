# combinations.ml

## Overview

Number of statements: 2

`combinations.ml` defines binomial coefficients and formalizes their relationship to the number of combinations. It builds upon the theory of binomial coefficients from `binomial.ml` to establish their combinatorial interpretation. The file likely contains theorems connecting binomial coefficients to counting combinations.


## NUMBER_OF_COMBINATIONS

### Name of formal statement
NUMBER_OF_COMBINATIONS

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMBER_OF_COMBINATIONS = prove
 (`!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binom(n,m)`,
  MATCH_ACCEPT_TAC HAS_SIZE_RESTRICTED_POWERSET);;
```

### Informal statement
For all sets `s` of type `A->bool`, and for all natural numbers `n` and `m`, if the set `s` has size `n`, then the set of all subsets `t` of `s` such that `t` has size `m` has size equal to the binomial coefficient `binom(n, m)`.

### Informal sketch
The proof that the number of combinations of `n` items taken `m` at a time is equal to the binomial coefficient `binom(n,m)` is performed using the tactic `MATCH_ACCEPT_TAC` along with `HAS_SIZE_RESTRICTED_POWERSET`.

- The theorem relates the cardinality of the set of all subsets of a given size to the binomial coefficient. The proof relies on the already established theorem `HAS_SIZE_RESTRICTED_POWERSET` which likely captures the basic combinatorial argument.
- `MATCH_ACCEPT_TAC` suggests the matching process involves recognizing the form of existing theorem about cardinalities of restricted powersets (`HAS_SIZE_RESTRICTED_POWERSET`) and directly applying it.

### Mathematical insight
This theorem formalizes the combinatorial identity that the number of ways to choose `m` elements from a set of `n` elements is given by the binomial coefficient "n choose m". The set `s` represents the set with `n` elements, and the subsets `t` represent the selections of `m` elements from `s`. The theorem provides a formal link between set theory (specifically, the notion of set size) and combinatorics (specifically, binomial coefficients).

### Dependencies
- Requires: `Library/binomial.ml`
- Relies on: `HAS_SIZE_RESTRICTED_POWERSET`


---

## NUMBER_OF_COMBINATIONS_EXPLICIT

### Name of formal statement
NUMBER_OF_COMBINATIONS_EXPLICIT

### Type of the formal statement
theorem

### Formal Content
```ocaml
let NUMBER_OF_COMBINATIONS_EXPLICIT = prove
 (`!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE
            (if n < m then 0 else FACT(n) DIV (FACT(m) * FACT(n - m)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP NUMBER_OF_COMBINATIONS) THEN
  REWRITE_TAC[GSYM NOT_LE; COND_SWAP; BINOM; MULT_AC]);;
```
### Informal statement
For any predicate `s` on a type `A`, if the set represented by `s` has size `n`, then the set of all subsets `t` of `s` that have size `m` has size equal to `0` if `n` is less than `m`, and `FACT(n) DIV (FACT(m) * FACT(n - m))` otherwise.

### Informal sketch
The proof proceeds as follows:
- Introduce the variables `n`, `m`, and `s`.
- Apply the theorem `NUMBER_OF_COMBINATIONS`, substituting `m:num` for the variable.
- Rewrite using theorems `GSYM NOT_LE`, `COND_SWAP`, `BINOM` and `MULT_AC`.

### Mathematical insight
This theorem provides an explicit formula for calculating the number of combinations of selecting `m` items from a set of `n` items. It connects the cardinality of a set of subsets to the factorial function and integer division. This is a fundamental result in combinatorics and is essential for counting and probability calculations.

### Dependencies
- Theorems: `NUMBER_OF_COMBINATIONS`, `NOT_LE`, `COND_SWAP`, `BINOM`, `MULT_AC`
- Definitions: `FACT`, `HAS_SIZE`, `SUBSET`


---

