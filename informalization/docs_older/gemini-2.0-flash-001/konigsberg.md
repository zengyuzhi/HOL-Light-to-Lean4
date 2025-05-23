# konigsberg.ml

## Overview

Number of statements: 18

`konigsberg.ml` formalizes the problem of the Bridges of Königsberg. It proves the impossibility of finding an Eulerian path, i.e., a path that visits each bridge exactly once. This is achieved within the HOL Light theorem prover.


## edges

### Name of formal statement
edges

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let edges = new_definition
  `edges(E:E->bool,V:V->bool,Ter:E->V->bool) = E`;;
```

### Informal statement
The set of edges `E` in a graph, where `E` is a set of edges (a predicate on the type `E`), `V` is a set of vertices (a predicate on the type `V`), and `Ter` is a predicate specifying the termination of an edge at a vertex (a predicate of type `E -> V -> bool`), is simply the set `E` itself.

### Informal sketch
This definition simply introduces a constant `edges` which given a set of edges `E`, a set of vertices `V`, and a predicate `Ter` relating edges and vertices, simply returns `E`. There is no proof or construction involved, as it is simply a definition.

### Mathematical insight
This definition is a trivial accessor function. It takes a graph representation that includes edges, vertices, and a termination relation, and it returns the set of edges. The motivation is to provide a named function to extract the edge set from a graph representation.

### Dependencies
None


---

## vertices

### Name of formal statement
vertices

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let vertices = new_definition
  `vertices(E:E->bool,V:V->bool,Ter:E->V->bool) = V`;;
```

### Informal statement
The vertices of a hypergraph (E, V, Ter), where E is a set of hyperedges, V is a set of vertices, and Ter is a ternary relation indicating which vertices are in which hyperedges, are defined to be the set of vertices V.

### Informal sketch
The definition directly assigns the set of vertices `V` to the term `vertices(E, V, Ter)`. There is no proof involved, as it is a direct definition.

### Mathematical insight
This definition extracts the vertex set from a hypergraph representation. In HOL Light, this is represented as a set of hyperedges, a set of vertices and a ternary relation defining which vertices are associated to which edges. This definition projects out the set of vertices.

### Dependencies
None

### Porting notes (optional)
This definition is very straightforward and should port easily to other proof assistants. The key is to ensure that the types for hyperedges and vertices are appropriately defined in the target system. Some systems may require an explicit type for hypergraphs themselves, in which case this projection would become a method on that type.


---

## termini

### Name of formal statement
termini

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let termini = new_definition
  `termini(E:E->bool,V:V->bool,Ter:E->V->bool) = Ter`;;
```
### Informal statement
The function `termini` takes three arguments: `E`, a predicate on a type `E`; `V`, a predicate on a type `V`; and `Ter`, a predicate relating elements of type `E` and elements of type `V`; and it returns the predicate `Ter`.

### Informal sketch
The definition simply assigns the predicate `Ter` to the identifier `termini(E, V, Ter)`. There is no proof involved, as it is a direct definitional assignment.

### Mathematical insight
This definition appears to be a placeholder or a trivial definition. It might be used as a starting point for defining a more complex relationship or function involving the predicates `E`, `V`, and `Ter`. The definition effectively states that the `termini` relation is equivalent to the `Ter` relation.

### Dependencies
None

### Porting notes (optional)
This definition is trivial and should port directly to most proof assistants. Ensure that the type signatures of the predicates `E`, `V`, and `Ter` are correctly translated.


---

## graph

### Name of formal statement
- graph

### Type of the formal statement
- new_definition

### Formal Content
- The full HOL Light statement will be inserted here **after generation**.
```ocaml
let graph = new_definition
 `graph G <=>
        !e. e IN edges(G)
            ==> ?a b. a IN vertices(G) /\ b IN vertices(G) /\
                      termini G e = {a,b}`;;
```

### Informal statement
- A graph `G` is defined such that for all edges `e`, if an edge `e` is in the set of edges of `G`, then there exist vertices `a` and `b` such that `a` is in the set of vertices of `G`, `b` is in the set of vertices of `G`, and the termini of `G` for edge `e` is the set containing `a` and `b`.

### Informal sketch
- The definition introduces the concept of an undirected graph.
- The main point is to constrain what it means to be a graph `G`: Every edge `e` in `G` must connect two vertices `a` and `b` that are also members of `G`.
- The `termini G e = {a,b}` ensures the set of endpoints of the edge `e` is exactly those two vertices.

### Mathematical insight
- This definition captures the standard notion of an undirected graph where each edge connects two vertices.
- The condition `termini G e = {a,b}` ensures that the graph does not contain dangling edges (edges not connected to any vertex) or endpoints other than the specified pair. This definition lays the foundation for reasoning about graph properties and algorithms within the formal system.

### Dependencies
- Definitions: `edges`, `vertices`, `termini`

### Porting notes (optional)
- In other proof assistants, the definition of `graph` can be directly translated as a predicate on a type representing a graph.
- Ensure that the definitions of `edges`, `vertices`, and `termini` are consistent with the overall graph representation used in the target proof assistant.
- This definition relies on set theory. Ensure the target theorem prover has adequate set theory support.


---

## TERMINI_IN_VERTICES

### Name of formal statement
TERMINI_IN_VERTICES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let TERMINI_IN_VERTICES = prove
 (`!G e v. graph G /\ e IN edges(G) /\ v IN termini G e ==> v IN vertices G`,
  REWRITE_TAC[graph; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;
```
### Informal statement
For all graphs `G`, all edges `e`, and all vertices `v`, if `G` is a graph, `e` is in the set of edges of `G`, and `v` is in the set of termini of the edge `e` with respect to the graph `G`, then `v` is in the set of vertices of `G`.

### Informal sketch
The proof proceeds as follows:
- Start with the assumption that `G` is a graph, `e` is in the edges of `G`, and `v` is in the termini of `G` with respect to `e`.
- Expand the definition of `graph`, `TERMINI`, `edges`, and `vertices`.
- Use the fact that `v` is in either the source or the target of `e`, and that both source and target of `e` must be in the vertices of G.
- Conclude that `v` is in the vertices of `G`.
- The tactic `REWRITE_TAC` is used to expand the definitions of `graph`, `EXTENSION` (used in the definition of `vertices`), `IN_INSERT` and `NOT_IN_EMPTY` (used in the definition of `TERMINI`).
- `MESON_TAC` automatically finishes the proof based on the rewritten assumptions and goal.

### Mathematical insight
This theorem states that if a vertex is a terminus (either the source or target) of an edge in a graph, then that vertex must be a vertex of the graph. It is a fundamental property ensuring that the termini of edges are contained within the graph's vertex set. This links the edge and vertex components of a graph.

### Dependencies
- Definitions: `graph`, `EXTENSION`, `IN_INSERT`, `NOT_IN_EMPTY`, `vertices`,`edges`,`TERMINI`


---

## connects

### Name of formal statement
connects

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let connects = new_definition
 `connects G e (a,b) <=> termini G e = {a,b}`;;
```

### Informal statement
For a graph `G`, an edge `e`, and a pair of vertices `(a, b)`, `connects G e (a, b)` is true if and only if the termini of the edge `e` in the graph `G` is equal to the set containing `a` and `b`.

### Informal sketch
The definition introduces the predicate `connects G e (a, b)` to formalize the notion that an edge `e` connects vertices `a` and `b` in a graph `G`. It directly equates this predicate with the condition that the set of termini of `e` in `G` equals the set `{a, b}`. No proof is required since this is a definition.

### Mathematical insight
The definition captures the intuitive idea of an edge connecting two vertices -- that the edge's endpoints or termini are precisely those two vertices. This is a fundamental concept in graph theory.

### Dependencies
None


---

## delete_edge

### Name of formal statement
delete_edge

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let delete_edge = new_definition
 `delete_edge e (E,V,Ter) = (E DELETE e,V,Ter)`;;
```
### Informal statement
The function `delete_edge` applied to an edge `e` and a graph represented as a triple `(E, V, Ter)`, where `E` is the set of edges, `V` is the set of vertices, and `Ter` is a representation of the terminal nodes, results in a new graph `(E DELETE e, V, Ter)` where the set of edges is updated by removing the edge `e` from the original edge set `E`.

### Informal sketch
The definition introduces a function `delete_edge` whose purpose is to remove a given edge from a graph represented as a triple. The function takes an edge `e` and a graph `(E, V, Ter)` as input and constructs a new graph `(E DELETE e, V, Ter)`. The new graph has the same sets of vertices `V` and terminal nodes `Ter` as the original graph, but its set of edges is updated by removing the given edge `e` from the original set of edges `E`. The construction makes direct use of the HOL Light set operation `DELETE`, which removes an element from a set.

### Mathematical insight
The definition provides a basic operation for manipulating graphs by defining how to remove an edge from a graph structure. This is a fundamental building block for more complex graph algorithms and manipulations, such as finding spanning trees or shortest paths.

### Dependencies
- Sets theory, specifically the set operation `DELETE`.

### Porting notes (optional)
The main challenge for porting this definition might be the representation of graphs and the availability of a set-difference operation that functions similarly to `DELETE`. Ensure the target proof assistant has suitable set primitives and that the graph representation is compatible with set-theoretic manipulation.


---

## DELETE_EDGE_CLAUSES

### Name of formal statement
DELETE_EDGE_CLAUSES

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DELETE_EDGE_CLAUSES = prove
 (`(!G. edges(delete_edge e G) = (edges G) DELETE e) /\
   (!G. vertices(delete_edge e G) = vertices G) /\
   (!G. termini(delete_edge e G) = termini G)`,
  REWRITE_TAC[FORALL_PAIR_THM; delete_edge; edges; vertices; termini]);;
```
### Informal statement
For all graphs `G`, the edges of the graph resulting from deleting edge `e` from `G` are equal to the edges of `G` set-minus `e`; the vertices of the graph resulting from deleting edge `e` from `G` are equal to the vertices of `G`; and the termini of the graph resulting from deleting edge `e` from `G` are equal to the termini of `G`.

### Informal sketch
The proof unfolds in three conjunctive parts based on the definition `delete_edge`:

- The first conjunct states that `edges(delete_edge e G) = (edges G) DELETE e`. This is proved by rewriting using the theorem `FORALL_PAIR_THM`, the definition of `delete_edge`, and the definition of `edges`.
- The second conjunct states that `vertices(delete_edge e G) = vertices G`. This is proved by rewriting using the theorem `FORALL_PAIR_THM`, the definition of `delete_edge`, and the definition of `vertices`.
- The third conjunct states that `termini(delete_edge e G) = termini G`. This is proved by rewriting using the theorem `FORALL_PAIR_THM`, the definition of `delete_edge`, and the definition of `termini`.

### Mathematical insight
The theorem `DELETE_EDGE_CLAUSES` formally establishes the fundamental properties of the `delete_edge` function with respect to the `edges`, `vertices`, and `termini` functions on graphs. Namely, deleting an edge from a graph removes the edge from the set of edges, without changing the set of vertices or the set of termini (endpoints) of edges. This is an important result for reasoning about graph modifications.

### Dependencies
- `FORALL_PAIR_THM`
- `delete_edge`
- `edges`
- `vertices`
- `termini`


---

## GRAPH_DELETE_EDGE

### Name of formal statement
GRAPH_DELETE_EDGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let GRAPH_DELETE_EDGE = prove
 (`!G e. graph G ==> graph(delete_edge e G)`,
  REWRITE_TAC[graph; DELETE_EDGE_CLAUSES; IN_DELETE] THEN MESON_TAC[]);;
```

### Informal statement
For all `G` and `e`, if `G` is a graph, then `delete_edge e G` is also a graph.

### Informal sketch
The proof proceeds by:
- Rewriting using the definition of `graph`, and the clauses defining `delete_edge`. These rewrites reduce the goal to verifying the membership condition for the components of the new graph.
- Applying a MESON tactic to automatically discharge the resulting goal. This step uses facts about membership within the `delete` operation.

### Mathematical insight
The theorem expresses that deleting an edge from a graph preserves the graph property. This is a fundamental property for reasoning about graph transformations.

### Dependencies
- Definitions: `graph`
- Theorems/Definitions: `DELETE_EDGE_CLAUSES`, `IN_DELETE`


---

## locally_finite

### Name of formal statement
locally_finite

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let locally_finite = new_definition
 `locally_finite G <=>
     !v. v IN vertices(G) ==> FINITE {e | e IN edges G /\ v IN termini G e}`;;
```
### Informal statement
A graph `G` is locally finite if and only if for all vertices `v` in the vertices of `G`, the set of edges `e` such that `e` is in the edges of `G` and `v` is in the termini of `G` is finite.

### Informal sketch
The definition `locally_finite` introduces the concept of a locally finite graph. A graph `G` is locally finite if, for every vertex `v` in the graph, the set of edges that have `v` as an endpoint is finite.

### Mathematical insight
The concept of local finiteness is crucial in graph theory, particularly when dealing with infinite graphs. It provides a condition for controlling the complexity around each vertex. A locally finite graph is one where each vertex only has finitely many neighbors, which can simplify analysis and allow for certain results from finite graph theory to be generalized. This definition is foundational for proving properties about infinite graphs that resemble finite ones in some local sense.

### Dependencies
None


---

## localdegree

### Name of formal statement
localdegree

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let localdegree = new_definition
 `localdegree G v e =
        if termini G e = {v} then 2
        else if v IN termini G e then 1
        else 0`;;
```
### Informal statement
The `localdegree` of a graph `G` at vertex `v` with respect to edge `e` is defined as follows:
- If the set of termini of edge `e` is equal to the singleton set containing `v`, then the `localdegree` is 2.
- Otherwise, if `v` is an element of the set of termini of edge `e`, then the `localdegree` is 1.
- Otherwise,the `localdegree` is 0.

### Informal sketch
The definition of `localdegree` is a simple conditional statement based on whether a given vertex `v` is a terminus of a given edge `e` in a graph `G`.
- If the edge `e` is a self-loop at vertex `v` (i.e., `termini G e = {v}`), then the function returns 2.
- Otherwise, if the vertex `v` is one of the endpoints of the edge `e` (i.e., `v IN termini G e`), then the function returns 1.
- Otherwise, the vertex `v` is not an endpoint of the edge `e`, and the function returns 0.

### Mathematical insight
The `localdegree` function defines the contribution of a single edge to the degree of a vertex in a graph. Self-loops contribute 2 to the degree, regular edges contribute 1 to the degree of each of their endpoints, and edges that do not have the vertex as an endpoint contribute 0. The degree of a vertex is later defined as the sum of the local degrees over all edges in the graph. This approach of defining the degree via the local degree allows for a more fine-grained analysis.

### Dependencies
- Definition: `termini`


---

## degree

### Name of formal statement
degree

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let degree = new_definition
 `degree G v = nsum {e | e IN edges G /\ v IN termini G e} (localdegree G v)`;;
```
### Informal statement
The degree of a vertex `v` in a graph `G` is defined as the sum, over all edges `e` such that `e` is in the edges of `G` and `v` is in the termini of `G` for each such `e`, of the local degree of `v` with respect to `G` and `e`.

### Informal sketch
- The statement defines the degree of a vertex in a graph.
- It sums the local degree of each vertex on all edges in the graph where the vertex exists.
- `nsum` is used to perform the summation.
- The summation iterates over the set of edges `e` such that `e` is an edge of the graph `G` and the vertex `v` is a terminus of `e`.
 - For each such edge `e`, the local degree of `v` relative to `G` and `e` (`localdegree G v`) is accumulated.

### Mathematical insight
This definition formalizes the intuitive notion of the degree of a vertex in a graph as the number of edges incident to it, accounting for graphs that may allow multiple edges between the same vertices. The local degree refines this count, resolving any ambiguity and giving a value.

### Dependencies
- Definitions: `edges`, `termini`, `nsum`, `localdegree`


---

## DEGREE_DELETE_EDGE

### Name of formal statement
DEGREE_DELETE_EDGE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let DEGREE_DELETE_EDGE = prove
 (`!G e:E v:V.
        graph G /\ locally_finite G /\ e IN edges(G)
        ==> degree G v =
                if termini G e = {v} then degree (delete_edge e G) v + 2
                else if v IN termini G e then degree (delete_edge e G) v + 1
                else degree (delete_edge e G) v`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[degree; DELETE_EDGE_CLAUSES; IN_DELETE] THEN
  SUBGOAL_THEN
   `{e:E | e IN edges G /\ (v:V) IN termini G e} =
        if v IN termini G e
        then e INSERT {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
        else {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(v:V) IN termini G (e:E)` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    COND_CASES_TAC THENL [ASM_MESON_TAC[IN_SING; EXTENSION]; ALL_TAC] THEN
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; localdegree] THEN
    REWRITE_TAC[DELETE_EDGE_CLAUSES]] THEN
  SUBGOAL_THEN
   `FINITE {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}`
   (fun th -> SIMP_TAC[NSUM_CLAUSES; th])
  THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e:E | e IN edges G /\ (v:V) IN termini G e}` THEN
    SIMP_TAC[IN_ELIM_THM; SUBSET] THEN
    ASM_MESON_TAC[locally_finite; TERMINI_IN_VERTICES];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[localdegree] THEN
  SUBGOAL_THEN
   `nsum {e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}
         (localdegree (delete_edge e G) v) =
    nsum {e' | (e' IN edges G /\ ~(e' = e)) /\ v IN termini G e'}
         (localdegree G v)`
  SUBST1_TAC THENL
   [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[localdegree; DELETE_EDGE_CLAUSES]);;
```
### Informal statement
For all graphs `G`, edges `e`, and vertices `v`, if `G` is a graph and `G` is locally finite and `e` is an element of the edges of `G`, then the degree of `G` at `v` is equal to:
- the degree of the graph obtained by deleting edge `e` from `G` at `v` plus 2, if the termini of `G` at `e` is the singleton set containing `v`;
- the degree of the graph obtained by deleting edge `e` from `G` at `v` plus 1, if `v` is an element of the termini of `G` at `e`;
- the degree of the graph obtained by deleting edge `e` from `G` at `v`, otherwise.

### Informal sketch
The proof proceeds by induction and simplification.
- Start by stripping the quantifiers.
- Rewrite using definitions of `degree` and `DELETE_EDGE_CLAUSES`, and the theorem `IN_DELETE` to reduce the goal to reasoning about the set of edges incident to `v`.
- Prove the subgoal stating the equivalence of two edge sets involving `termini`, `edges` and `delete_edge` using set extensionality and conditional cases.
- Perform case analysis on whether `v` is in the termini of `G` at `e`.
- To deal with the case where `v` is in the termini of `G` at `e`, use conditional cases and meson to eliminate assumptions and use `IN_SING` and `EXTENSION`. Also, apply theorem `NSUM_EQ`, rewrite using `IN_ELIM_THM` and `localdegree`. Then rewrite using `DELETE_EDGE_CLAUSES`.
- Address the case where `v` is not in the termini of `G` at `e` similarly using conditional cases and `NSUM_EQ`, and rewrite using `IN_ELIM_THM` and `localdegree` as well as `DELETE_EDGE_CLAUSES`.
- Prove the subgoal that the set `{e':E | (e' IN edges G /\ ~(e' = e)) /\ (v:V) IN termini G e'}` is finite by showing that it's a subset of a finite set and using `FINITE_SUBSET`.
- Rewrite using `IN_ELIM_THM` and `localdegree`.
- The next subgoal proves the equality of two nsums based on whether the edge contains the vertex. Simplify using `NSUM_CLAUSES` to eliminate nsum whose domain is empty. Apply arithmetic.
- Finally apply `NSUM_EQ` and simplify using `localdegree` and `DELETE_EDGE_CLAUSES`.

### Mathematical insight
This theorem describes how the degree of a vertex changes when an edge is deleted from the graph. The degree of a vertex decreases by 2 if the edge connects the vertex to itself (a loop), and it decreases by 1 if the edge connects the vertex to another vertex. If the vertex is not an endpoint of the deleted edge, its degree does not change. This result is fundamental to understanding how graph operations affect vertex degrees.

### Dependencies
- Definitions: `degree`, `localdegree`
- Theorems: `DELETE_EDGE_CLAUSES`, `IN_DELETE`, `EXTENSION`, `IN_ELIM_THM`, `IN_INSERT`, `IN_SING`, `NSUM_EQ`, `localdegree`, `FINITE_SUBSET`, `TERMINI_IN_VERTICES`, `NSUM_CLAUSES`

### Porting notes (optional)
- The proof relies heavily on rewriting with the definition of `degree` and the clauses for `DELETE_EDGE`. Therefore, the target proof assistant needs similar automation capabilities for rewriting with definitions and inductive cases.
- The `NSUM` (numerical summation) and its associated theorems (`NSUM_CLAUSES`) need to be available or defined.
- The key step is recognizing and proving the set equality related to edge incidence, which depends on the properties of `termini`.


---

## eulerian_RULES,eulerian_INDUCT,eulerian_CASES

### Name of formal statement
- eulerian_RULES,eulerian_INDUCT,eulerian_CASES

### Type of the formal statement
- new_inductive_definition

### Formal Content
```ocaml
let eulerian_RULES,eulerian_INDUCT,eulerian_CASES = new_inductive_definition
 `(!G a. a IN vertices G /\ edges G = {} ==> eulerian G [] (a,a)) /\
  (!G a b c e es. e IN edges(G) /\ connects G e (a,b) /\
                  eulerian (delete_edge e G) es (b,c)
                  ==> eulerian G (CONS e es) (a,c))`;;
```
### Informal statement
The predicate `eulerian G es (a,c)` holds if and only if one of the following conditions is true:

1. The set of edges of the graph `G` is empty, `a` is a vertex of `G`, and `a` is equal to `c`, and `es` is the empty list.
2. There exist vertices `a`, `b`, and `c`, an edge `e`, and a list of edges `es` such that `e` is an edge of `G`, `e` connects `a` to `b` in `G`, and `eulerian (delete_edge e G) es (b,c)` holds, then `eulerian G (CONS e es) (a,c)` holds.

### Informal sketch
This defines an inductive relation `eulerian G es (a,c)` that specifies when a list of edges `es` forms an Eulerian path from vertex `a` to vertex `c` in a graph `G`.

-   The base case states that if the graph `G` has no edges and `a` is a vertex then the empty path `[]` is an Eulerian path from `a` to `a`.

-   The inductive step states that if `e` is an edge in `G` connecting `a` to `b`, and `es` form an Eulerian path from `b` to `c` in the graph `delete_edge e G`, then `CONS e es` forms an Eulerian path from `a` to `c` in the graph `G`. The `delete_edge e G` removes the edge `e` from the graph `G`.

### Mathematical insight
This inductive definition captures the essence of an Eulerian path. The path is constructed edge by edge, ensuring that each edge is used exactly once. The base case handles the trivial scenario where the graph has no edges. The inductive step extends an existing Eulerian path by adding a new edge, ensuring that the connections between vertices are maintained. This is a standard way to formalize graph traversal properties.

### Dependencies
-   `vertices`
-   `edges`
-   `connects`
-   `delete_edge`
-   `IN` (set membership)
-   `CONS`

### Porting notes (optional)
When porting this definition, special care should be taken regarding the definitions of `vertices`, `edges`, `connects` and `delete_edge`. Make sure to choose a suitable representation of graphs and edges in the target proof assistant. Also, the handling of inductive definitions varies among proof assistants, so the syntax and approach might need adjustments. For example, in Coq and Lean, one might need to explicitly define the graph type and edge type, and then define these functions accordingly.


---

## EULERIAN_FINITE

### Name of formal statement
EULERIAN_FINITE

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULERIAN_FINITE = prove
 (`!G es ab. eulerian G es ab ==> FINITE (edges G)`,
  MATCH_MP_TAC eulerian_INDUCT THEN
  SIMP_TAC[DELETE_EDGE_CLAUSES; FINITE_DELETE; FINITE_RULES]);;
```
### Informal statement
For all graphs `G`, edge selectors `es`, starting point `a`, and ending point `b`, if `G` is Eulerian with respect to `es`, `a`, and `b`, then the set of edges of `G` is finite.

### Informal sketch
The proof proceeds by induction on the `eulerian` predicate using `eulerian_INDUCT`. Then, simplification is performed using the clauses for `DELETE_EDGE` and finiteness lemmas.

- Base case: If the graph is empty, the set of edges is trivially finite.
- Inductive step: Assume the graph `G` is Eulerian from `a` to `b` via edge selector `es`. Assume removing an edge from `G`, obtaining `DELETE_EDGE G e`, results in an Eulerian graph also implying that the remaining set of edges `edges (DELETE_EDGE G e)` is finite.
- Goal: Show that `edges G` is finite.
- Since `edges G = insert e (edges (DELETE_EDGE G e))` and `edges (DELETE_EDGE G e)` is finite by the inductive hypothesis, then `edges G` is also finite.

### Mathematical insight
This theorem states that an Eulerian graph, as defined by the `eulerian` predicate, must have a finite number of edges. This is a necessary condition for a graph to be considered Eulerian, as an infinite graph cannot have an Eulerian path or cycle. This theorem justifies that the inductive definition of `eulerian` only applies to finite graphs.

### Dependencies
- Definitions: `eulerian`
- Theorems: `FINITE_DELETE`, `FINITE_RULES` , `DELETE_EDGE_CLAUSES`
- Induction principle: `eulerian_INDUCT`


---

## EULERIAN_ODD_LEMMA

### Name of formal statement
EULERIAN_ODD_LEMMA

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULERIAN_ODD_LEMMA = prove
 (`!G:(E->bool)#(V->bool)#(E->V->bool) es ab.
        eulerian G es ab
        ==> graph G
            ==> FINITE(edges G) /\
                !v. v IN vertices G
                    ==> (ODD(degree G v) <=>
                         ~(FST ab = SND ab) /\ (v = FST ab \/ v = SND ab))`,
  MATCH_MP_TAC eulerian_INDUCT THEN CONJ_TAC THENL
   [SIMP_TAC[degree; NOT_IN_EMPTY; SET_RULE `{x | F} = {}`] THEN
    SIMP_TAC[NSUM_CLAUSES; FINITE_RULES; ARITH];
    ALL_TAC] THEN
  SIMP_TAC[GRAPH_DELETE_EDGE; FINITE_DELETE; DELETE_EDGE_CLAUSES] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[GRAPH_DELETE_EDGE] THEN STRIP_TAC THEN
  X_GEN_TAC `v:V` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(E->bool)#(V->bool)#(E->V->bool)`; `e:E`; `v:V`]
                DEGREE_DELETE_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[locally_finite] THEN GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `edges(G:(E->bool)#(V->bool)#(E->V->bool))` THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G:(E->bool)#(V->bool)#(E->V->bool)`; `e:E`]
         TERMINI_IN_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connects]) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `b:V = a` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SET_RULE `{a,a} = {v} <=> v = a`] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[ODD_ADD; ARITH];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SET_RULE `{a,b} = {v} <=> a = b /\ a = v`] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ODD_ADD; ARITH] THEN ASM_MESON_TAC[]);;
```

### Informal statement
For any graph `G` (represented by functions `es`, `ab`), where `es` determines the edges, `ab` maps edges to vertices, if `G` is Eulerian, and `G` is a graph, then the set of edges of `G` is finite. Further, for any vertex `v` in the vertices of `G`, the degree of `v` in `G` is odd if and only if `v` is not equal to the first element of `ab` and `v` is not equal to the second element of `ab`, where the first and second elements of `ab` are not equal, i.e., are distinct.

### Informal sketch
The proof proceeds by induction on the `eulerian` property using `eulerian_INDUCT`.

- The base case involves showing that for the empty graph, the lemma holds. This is done by simplifying using definitions of `degree`, `NOT_IN_EMPTY`, and set theory rules, and then using arithmetic simplification to show the equivalence.
- The inductive step assumes the lemma holds for a graph `G` and proves it for the graph obtained by deleting an edge `e` from `G`. Simplification rules for `GRAPH_DELETE_EDGE`, `FINITE_DELETE`, and `DELETE_EDGE_CLAUSES` are used.
- The induction hypothesis is discharged and simplified using `GRAPH_DELETE_EDGE`. We introduce a variable `v` of type `V`.
- The theorem `DEGREE_DELETE_EDGE` is applied to relate the degree of a vertex in the original graph to its degree in the graph with an edge deleted. The assumptions of `DEGREE_DELETE_EDGE` are addressed using `locally_finite`, the finiteness of edges, and set subset reasoning.
- Then, we substitute using the result about degree from the previous steps.
- The theorem `TERMINI_IN_VERTICES` is applied to state that endpoints of an edge are vertices of the graph.
- Rewrite rules regarding `connects` are used to simplify the inductive step.
- Cases are considered based on whether the vertex `v` is equal to one of the endpoints (`a`) of the deleted edge. Simplify using set theory rules for set equality of singletons, use conditional cases, simplify with `ODD_ADD` and arithmetic.
- Another case split is used based on whether the vertices are equal and then the proof is concluded.
- Finally, `ASM_MESON_TAC` tries to complete the proof by exhausting consequences of assumptions and the goal.

### Mathematical insight
The theorem relates the Eulerian property of a graph to the degrees of its vertices. In particular, it establishes that in an Eulerian graph, a vertex has an odd degree if and only if it is one of the two distinct endpoints of the `ab` function (which seem to correspond to the start and end points of the Eulerian path/circuit).

### Dependencies
- `eulerian_INDUCT`
- `degree`
- `NOT_IN_EMPTY`
- `SET_RULE `{x | F} = {}``
- `NSUM_CLAUSES`
- `FINITE_RULES`
- `ARITH`
- `GRAPH_DELETE_EDGE`
- `FINITE_DELETE`
- `DELETE_EDGE_CLAUSES`
- `DEGREE_DELETE_EDGE`
- `locally_finite`
- `FINITE_SUBSET`
- `SUBSET`
- `IN_ELIM_THM`
- `TERMINI_IN_VERTICES`
- `connects`
- `IN_INSERT`
- `NOT_IN_EMPTY`
- `SET_RULE `{a,a} = {v} <=> v = a``
- `ODD_ADD`
- `ARITH`
- `SET_RULE `{a,b} = {v} <=> a = b /\ a = v``

### Porting notes (optional)
This lemma and its proof heavily rely on set theory and arithmetic reasoning. The porter should ensure that the target proof assistant has adequate support for these areas. Differences in how graphs are represented might also require careful adaptation of the proof. Specifically, the relationship between edges and vertices captured by the `ab` function may need to be expressed differently.


---

## EULERIAN_ODD

### Name of formal statement
EULERIAN_ODD

### Type of the formal statement
theorem

### Formal Content
```ocaml
let EULERIAN_ODD = prove
 (`!G es a b.
        graph G /\ eulerian G es (a,b)
        ==> !v. v IN vertices G
                ==> (ODD(degree G v) <=> ~(a = b) /\ (v = a \/ v = b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP EULERIAN_ODD_LEMMA) THEN
  ASM_SIMP_TAC[FST; SND]);;
```

### Informal statement
For any graph `G`, any list of edges `es`, and any vertices `a` and `b`, if `G` is a graph and `es` is an Eulerian trail of `G` from `a` to `b`, then for any vertex `v`, `v` is in the vertices of `G` implies that the degree of `G` at `v` is odd if and only if it is not the case that `a` equals `b` and `v` is either `a` or `b`.

### Informal sketch
The proof proceeds as follows:
- Assume `graph G` and `eulerian G es (a, b)`.
- Assume that `v` is in the vertices of `G`.
- Apply `EULERIAN_ODD_LEMMA` to deduce `!v. v IN vertices G ==> (ODD (degree G v) <=> (a = b /\ v = a /\ ~mem v es) \/ (a = b /\ v = b /\ ~mem v es) \/ (~(a = b) /\ (v = a \/ v = b) /\ ~mem v es))`.
- Simplify using the assumptions to show `ODD (degree G v) <=> ~(a = b) /\ (v = a \/ v = b)`.
- Use `FST` and `SND` as assumptions for simplification.

### Mathematical insight
This theorem states that in a graph with an Eulerian trail, a vertex has an odd degree if and only if the start and end vertices of the trail are distinct, and the vertex is one of the start or end vertices. It characterizes the vertex degrees in terms of the existence of an Eulerian path.

### Dependencies
- `EULERIAN_ODD_LEMMA`
- `FST`
- `SND`


---

## KOENIGSBERG

### Name of formal statement
KOENIGSBERG

### Type of the formal statement
theorem

### Formal Content
```ocaml
let KOENIGSBERG = prove
 (`!G. vertices(G) = {0,1,2,3} /\
       edges(G) = {10,20,30,40,50,60,70} /\
       termini G (10) = {0,1} /\
       termini G (20) = {0,2} /\
       termini G (30) = {0,3} /\
       termini G (40) = {1,2} /\
       termini G (50) = {1,2} /\
       termini G (60) = {2,3} /\
       termini G (70) = {2,3}
       ==> ~(?es a b. eulerian G es (a,b))`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `G:(num->bool)#(num->bool)#(num->num->bool)` EULERIAN_ODD) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[graph] THEN GEN_TAC THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE
     `{a,b} = {x,y} <=> a = x /\ b = y \/ a = y /\ b = x`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  ASM_REWRITE_TAC[degree; edges] THEN
  SIMP_TAC[TAUT `a IN s /\ k IN t <=> ~(a IN s ==> ~(k IN t))`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P(x)} = a INSERT {x | P(x)}`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  ASM_REWRITE_TAC[localdegree; IN_INSERT; NOT_IN_EMPTY; ARITH] THEN
  REWRITE_TAC[SET_RULE `{a,b} = {x} <=> x = a /\ a = b`] THEN
  DISCH_THEN(fun th ->
   MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th) THEN
   MP_TAC(SPEC `2` th) THEN MP_TAC(SPEC `3` th)) THEN
  REWRITE_TAC[ARITH] THEN ARITH_TAC);;
```

### Informal statement
For all graphs `G`, if the vertices of `G` are the set `{0, 1, 2, 3}`, the edges of `G` are the set `{10, 20, 30, 40, 50, 60, 70}`, the termini of edge `10` in `G` are the set `{0, 1}`, the termini of edge `20` in `G` are the set `{0, 2}`, the termini of edge `30` in `G` are the set `{0, 3}`, the termini of edge `40` in `G` are the set `{1, 2}`, the termini of edge `50` in `G` are the set `{1, 2}`, the termini of edge `60` in `G` are the set `{2, 3}`, and the termini of edge `70` in `G` are the set `{2, 3}`, then there do not exist lists of edges `es` and vertices `a`, `b` such that `es` forms an Eulerian path in `G` starting at `a` and ending at `b`.

### Informal sketch
The theorem states that the Königsberg graph has no Eulerian path. The proof proceeds as follows:
- Assume that a graph `G` is given, with the specified vertices and edges. Assume also that `G` has the given `termini` function, associating edges with their endpoints. Assume, for the sake of contradiction, that there exist lists `es` and vertices `a` and `b` such that `eulerian G es (a,b)` holds.
- Instantiate the theorem `EULERIAN_ODD` (which presumably states something like: if there exists an eulerian path, there exist at most two vertices with odd degree)
- Rewrite using the definition of the `degree` function.
- By simplifying set membership for sets explicitly constructed via insertions, and rewriting with arithmetic, we obtain the local degree of each vertex.
- Establish that each vertex has degree 3, and therefore there are four vertices of odd degree.
- This contradicts `EULERIAN_ODD`, so no such Eulerian path exists.

### Mathematical insight
The Königsberg bridge problem is a classic example in graph theory demonstrating that a path traversing each edge exactly once is only possible if either zero or two vertices have an odd degree. The theorem formalizes this and applies it to the specific graph representing the city of Königsberg.

### Dependencies
- `EULERIAN_ODD`
- `vertices`
- `edges`
- `termini`
- `eulerian`
- `graph`
- `degree`
- `localdegree`
- `NSUM_CLAUSES`
- `FINITE_INSERT`
- `FINITE_EMPTY`

### Porting notes (optional)
- The proof relies heavily on rewriting and simplification. In other provers, this might require more explicit unfolding of definitions and application of lemmas.
- The use of `ARITH_TAC` suggests that the arithmetic reasoning is straightforward. However, in some systems, more manual proof steps may be needed if the arithmetic automation is not as strong.


---

