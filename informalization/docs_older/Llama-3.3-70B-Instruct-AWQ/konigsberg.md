# konigsberg.ml

## Overview

Number of statements: 18

The `konigsberg.ml` file formalizes the impossibility of an Eulerian path for the bridges of Königsberg. It proves a theorem related to this historic problem in graph theory, demonstrating the non-existence of such a path. The file is self-contained, with no dependencies on other modules. Its key content revolves around the formal proof of this impossibility, contributing to the library's collection of graph theory results.

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
The `edges` function takes three arguments: a predicate `E` on edges, a predicate `V` on vertices, and a predicate `Ter` on edges and vertices, and returns the predicate `E`.

### Informal sketch
* The definition of `edges` is a straightforward assignment of the input predicate `E` to the output.
* The function `edges` does not perform any complex operations on the input predicates `E`, `V`, or `Ter`.
* The purpose of `edges` seems to be a simple wrapper or selector for the edge predicate `E`, potentially for use in a larger context or theory.

### Mathematical insight
The `edges` definition appears to be part of a larger formalization related to graph theory, specifically concerning the impossibility of an Eulerian path for bridges of Koenigsberg. The key idea is to define a basic component, in this case, a function that simply returns the edge predicate, which can then be used to build more complex arguments or theorems about graph properties.

### Dependencies
* No explicit dependencies are listed in the provided formal content, but based on the context, it may rely on basic definitions and properties of graphs, vertices, and edges, such as:
  - `E` (edge predicate)
  - `V` (vertex predicate)
  - `Ter` (terminal predicate for edges and vertices)

### Porting notes
When translating this definition into another proof assistant like Lean, Coq, or Isabelle, pay attention to how these systems handle function definitions and predicate types. Specifically, ensure that the target system's type system and syntax for defining and applying predicates are correctly utilized. For example, in Lean, you might use the `def` keyword for defining `edges`, while in Coq, you could use `Definition`. In Isabelle, the `definition` command would be appropriate.

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
The `vertices` function takes three arguments: `E`, `V`, and `Ter`, where `E` is a predicate on edges, `V` is a predicate on vertices, and `Ter` is a predicate on edges and vertices. It returns the predicate `V` on vertices.

### Informal sketch
* The definition of `vertices` is straightforward, directly returning the `V` predicate.
* No specific proof or construction is required, as this is a simple definition.
* The `vertices` function seems to be extracting or identifying the vertex predicate `V` from a given context involving edges `E` and a termination condition `Ter`.

### Mathematical insight
The `vertices` definition appears to be part of a larger context where edges and vertices are being defined or manipulated, possibly in a graph theory setting. The function's simplicity suggests it might be a foundational or auxiliary definition, providing a way to explicitly reference the vertex predicate in further constructions or theorems.

### Dependencies
* None explicitly mentioned in the given formal content.

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, ensure that the predicate types for `E`, `V`, and `Ter` are correctly defined and that the function `vertices` is declared with the appropriate type signature. Note that the specific syntax for defining such a function will vary between proof assistants, but the logical content should remain straightforward to translate.

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
The `termini` definition takes three parameters: a predicate `E` of type `E->bool`, a predicate `V` of type `V->bool`, and a predicate `Ter` of type `E->V->bool`. It simply returns the `Ter` predicate.

### Informal sketch
* The definition of `termini` is straightforward and does not involve any complex logical deductions.
* It directly assigns the `Ter` predicate to the `termini` definition, without any additional processing or transformation.
* No specific HOL Light tactics are required to understand this definition, as it is a simple assignment.

### Mathematical insight
The `termini` definition appears to be a basic building block or a placeholder for more complex definitions or theorems. It defines a relationship between three predicates, but does not impose any specific constraints or conditions on them. This definition might be used as a starting point for more advanced constructions or proofs.

### Dependencies
* None

### Porting notes
When porting this definition to other proof assistants, note that the syntax for defining predicates and assigning them to new definitions may vary. For example, in Lean, this definition might be written using the `def` keyword, while in Coq, it might be written using the `Definition` keyword. Additionally, the type annotations for the predicates `E`, `V`, and `Ter` may need to be adjusted to match the type systems of the target proof assistant.

---

## graph

### Name of formal statement
graph

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let graph = new_definition
 `graph G <=>
        !e. e IN edges(G)
            ==> ?a b. a IN vertices(G) /\ b IN vertices(G) /\
                      termini G e = {a,b}`;;
```

### Informal statement
A graph G satisfies the property `graph` if and only if for all edges e in G, there exist vertices a and b in G such that the endpoints of e in G are exactly {a, b}.

### Informal sketch
* The definition of a graph G involves quantifying over all edges e in G.
* For each edge e, we assert the existence of two vertices a and b that are in the set of vertices of G.
* The `termini` function is used to specify that the endpoints of edge e in graph G are precisely the set {a, b}.
* This definition captures the essence of an undirected graph, where each edge connects two vertices.

### Mathematical insight
This definition formalizes the concept of an undirected graph, emphasizing that each edge has two distinct endpoints that are vertices of the graph. This construction is fundamental in graph theory, as it provides a basis for studying graph properties and algorithms.

### Dependencies
* `edges`
* `vertices`
* `termini`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay attention to how each system handles existential quantification and set notation. Specifically, the use of `?a b` for existential quantification and `{a, b}` for set notation may need to be adapted to the target system's syntax and semantics. Additionally, ensure that the `termini` function is properly defined and imported in the target system.

---

## TERMINI_IN_VERTICES

### Name of formal statement
TERMINI_IN_VERTICES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let TERMINI_IN_VERTICES = prove
 (`!G e v. graph G /\ e IN edges(G) /\ v IN termini G e ==> v IN vertices G`,
  REWRITE_TAC[graph; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;
```

### Informal statement
For all graphs `G`, edges `e`, and vertices `v`, if `G` is a graph and `e` is an edge in `G` and `v` is a terminus of `e` in `G`, then `v` is a vertex in `G`.

### Informal sketch
* The proof starts with the assumption that `G` is a graph, `e` is an edge in `G`, and `v` is a terminus of `e` in `G`.
* It then applies `REWRITE_TAC` to expand the definitions of `graph`, `EXTENSION`, `IN_INSERT`, and `NOT_IN_EMPTY`.
* The `MESON_TAC` tactic is used to automatically prove the resulting goal, likely by applying basic properties of sets and membership.

### Mathematical insight
This theorem establishes a fundamental property of graphs, namely that the terminus of an edge in a graph is indeed a vertex of that graph. This property is crucial for ensuring the consistency and well-formedness of graph structures.

### Dependencies
* `graph`
* `edges`
* `termini`
* `vertices`
* `EXTENSION`
* `IN_INSERT`
* `NOT_IN_EMPTY`

### Porting notes
When translating this theorem into other proof assistants, pay attention to the handling of graph structures and the definitions of `termini` and `vertices`. The `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics or strategies in the target system. Additionally, the automation provided by `MESON_TAC` may not be directly available, requiring manual application of basic properties or the use of other automated reasoning tools.

---

## connects

### Name of formal statement
connects

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let connects = new_definition `connects G e (a,b) <=> termini G e = {a,b}`
```

### Informal statement
The `connects` relation holds between a graph `G`, an edge `e`, and a pair of vertices `(a, b)` if and only if the set of termini of `e` in `G` is equal to the set containing `a` and `b`.

### Informal sketch
* The definition of `connects` involves the `termini` function, which returns the set of vertices that an edge connects in a graph.
* To prove a statement involving `connects`, one would likely need to unfold this definition and reason about the properties of `termini` and set equality.
* Key steps might involve:
  + Unfolding the definition of `connects` to reveal the `termini` function
  + Using properties of set equality to reason about the vertices connected by an edge
  + Possibly using `termini` properties to deduce information about the edge and its connected vertices

### Mathematical insight
The `connects` definition formalizes the intuitive notion of an edge connecting two vertices in a graph. This definition is fundamental in graph theory, as it provides a basis for reasoning about the structure of graphs and the relationships between their components.

### Dependencies
* `termini`
 
### Porting notes
When translating this definition into another proof assistant, ensure that the equivalent of `termini` is defined and that set equality is handled appropriately. Note that different systems may have varying levels of automation for set properties, which could affect the proof strategy.

---

## delete_edge

### Name of formal statement
delete_edge

### Type of the formal statement
new_definition

### Formal Content
```ocaml
let delete_edge = new_definition `delete_edge e (E,V,Ter) = (E DELETE e,V,Ter)`;;
```

### Informal statement
The function `delete_edge` takes an edge `e` and a graph `(E, V, Ter)`, and returns a new graph where the edge `e` is deleted from the set of edges `E`, while keeping the set of vertices `V` and the termination condition `Ter` unchanged.

### Informal sketch
* The `delete_edge` function is defined as a transformation on a graph, which is represented as a triple `(E, V, Ter)`.
* The function takes an edge `e` as input and applies the `DELETE` operation to remove `e` from the set of edges `E`.
* The resulting graph has the same set of vertices `V` and termination condition `Ter` as the original graph.
* The key step involves applying the `DELETE` operation, which is a set difference operation in this context.

### Mathematical insight
The `delete_edge` function represents a basic graph modification operation, which is essential in graph theory and its applications. It allows for the removal of an edge from a graph while preserving the rest of the graph's structure. This operation is crucial in various graph algorithms and is often used in combination with other graph operations to construct or transform graphs.

### Dependencies
* `DELETE` (set difference operation)
* Graph representation as a triple `(E, V, Ter)`

### Porting notes
When porting this definition to other proof assistants like Lean, Coq, or Isabelle, note that the `DELETE` operation may be represented differently, and the graph data structure might need to be defined explicitly. Additionally, the `new_definition` construct may have an equivalent in the target system, but its syntax and usage might vary.

---

## DELETE_EDGE_CLAUSES

### Name of formal statement
DELETE_EDGE_CLAUSES

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let DELETE_EDGE_CLAUSES = prove
 (`(!G. edges(delete_edge e G) = (edges G) DELETE e) /\
   (!G. vertices(delete_edge e G) = vertices G) /\
   (!G. termini(delete_edge e G) = termini G)`,
  REWRITE_TAC[FORALL_PAIR_THM; delete_edge; edges; vertices; termini])
```

### Informal statement
For all graphs `G`, the following properties hold: 
1. The edges of the graph resulting from deleting an edge `e` from `G` are equal to the edges of `G` with `e` removed.
2. The vertices of the graph resulting from deleting an edge `e` from `G` are equal to the vertices of `G`.
3. The termini of the graph resulting from deleting an edge `e` from `G` are equal to the termini of `G`.

### Informal sketch
* The proof involves showing that deleting an edge `e` from a graph `G` preserves the vertices and termini of `G`, while modifying its edges by removing `e`.
* The `REWRITE_TAC` tactic is used with theorems `FORALL_PAIR_THM`, `delete_edge`, `edges`, `vertices`, and `termini` to simplify and establish the equalities.

### Mathematical insight
This theorem provides a fundamental property of graph manipulation, specifically how deleting an edge affects the graph's structure. It is essential for reasoning about graph transformations and is likely used as a foundation for more complex graph algorithms or properties.

### Dependencies
* Theorems:
  + `FORALL_PAIR_THM`
* Definitions:
  + `delete_edge`
  + `edges`
  + `vertices`
  + `termini`

### Porting notes
When translating this theorem into another proof assistant, pay special attention to how graphs and their operations (`delete_edge`, `edges`, `vertices`, `termini`) are defined and handled. Ensure that the target system's `REWRITE_TAC` equivalent or similar mechanism for applying theorems and definitions during proof construction is used appropriately. Note that differences in how binders or quantifiers are treated may require adjustments to the proof strategy.

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
For all graphs `G` and edges `e`, if `G` is a graph, then the result of deleting edge `e` from `G` is also a graph.

### Informal sketch
* The proof starts with the assumption that `G` is a graph.
* It then applies the `REWRITE_TAC` tactic to rewrite the `graph` and `delete_edge` terms using their respective definitions (`graph`, `DELETE_EDGE_CLAUSES`, and `IN_DELETE`).
* The `MESON_TAC` tactic is used to automatically prove the resulting goal, which is that the deleted graph is still a graph.
* The key insight is that deleting an edge from a graph preserves the graph structure, as the `delete_edge` function only removes the edge `e` from `G` without affecting the underlying graph properties.

### Mathematical insight
This theorem is important because it ensures that the `delete_edge` operation is well-defined and preserves the graph structure. It is a fundamental property of graphs and is used extensively in graph theory and computer science. The theorem provides a guarantee that deleting an edge from a graph will not result in an invalid or ill-defined structure.

### Dependencies
* `graph`
* `delete_edge`
* `DELETE_EDGE_CLAUSES`
* `IN_DELETE`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the `delete_edge` function is defined correctly and that the `graph` predicate is properly applied. Additionally, the `REWRITE_TAC` and `MESON_TAC` tactics may need to be replaced with equivalent tactics in the target proof assistant.

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
     !v. v IN vertices(G) ==> FINITE {e | e IN edges G /\ v IN termini G e}`
```

### Informal statement
A graph `G` is `locally_finite` if and only if for all vertices `v` in `G`, the set of edges `e` in `G` such that `v` is in the termini of `e` is finite.

### Informal sketch
* The definition of `locally_finite` involves a universal quantification over all vertices `v` in the graph `G`.
* For each vertex `v`, we consider the set of edges `e` in `G` such that `v` is an endpoint of `e`, i.e., `v IN termini G e`.
* The graph `G` is `locally_finite` if and only if this set of edges is finite for all vertices `v`.
* The proof of a graph being `locally_finite` would involve showing that for any given vertex, the set of edges incident on it can be put into a one-to-one correspondence with a finite set.

### Mathematical insight
The concept of `locally_finite` is important in graph theory as it ensures that every vertex has only a finite number of edges connected to it. This property is crucial for many graph algorithms and theorems, as it prevents the presence of vertices with an infinite number of edges, which could lead to inconsistencies or undefined behavior.

### Dependencies
* `vertices`
* `edges`
* `termini`
* `FINITE`

### Porting notes
When translating this definition into other proof assistants, care should be taken to preserve the quantification and the finiteness condition. In particular, the use of `!v` for universal quantification and `FINITE` for finiteness should be replaced with the corresponding constructs in the target proof assistant. Additionally, the `IN` notation for set membership and the `/\` notation for conjunction may need to be translated accordingly.

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
        else 0`
```

### Informal statement
The `localdegree` function calculates the degree of a vertex `v` in a graph `G` with respect to an edge `e`. It returns 2 if the edge `e` is a loop at vertex `v` (i.e., `v` is the only terminus of `e`), 1 if `v` is one of the termini of `e` but not the only one, and 0 otherwise.

### Informal sketch
* The definition first checks if the set of termini of edge `e` in graph `G` contains only the vertex `v`. If so, it returns 2, indicating that `e` is a loop at `v`.
* If `v` is not the sole terminus of `e`, it then checks if `v` is among the termini of `e`. If `v` is a terminus, it returns 1, signifying that `v` is connected by `e` but `e` is not a loop.
* If neither condition is met, it returns 0, indicating that `v` is not a terminus of `e`.

### Mathematical insight
The `localdegree` function provides a way to determine the local connectivity of a vertex in a graph with respect to a specific edge. This is useful in graph theory for analyzing properties of graphs, such as vertex degrees, which are crucial in understanding graph structures and behaviors.

### Dependencies
- `termini`
 
### Porting notes
When translating this definition into other proof assistants, pay attention to how each system handles graph theory constructs, especially the representation of graphs and edges, and how vertex degrees are calculated. For example, in systems like Lean, Coq, or Isabelle, you might need to define a graph data structure and then implement the `localdegree` function accordingly, possibly leveraging existing libraries or modules for graph theory.

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
The degree of a vertex `v` in a graph `G` is defined as the sum of the local degrees of `v` with respect to all edges `e` in `G` for which `v` is a terminal, where the sum is taken over all such edges.

### Informal sketch
* The definition of `degree` involves a summation over a set of edges `e` in the graph `G` for which the vertex `v` is a terminal.
* For each such edge `e`, the `localdegree` of `v` with respect to `e` is computed.
* The `nsum` function is then used to sum up these local degrees.
* The overall process can be viewed as aggregating the contributions of each edge incident on `v` to obtain the total degree of `v`.

### Mathematical insight
The `degree` definition captures the notion of the number of edges incident on a vertex in a graph, which is a fundamental concept in graph theory. This definition is important because it provides a way to quantify the connectivity of a vertex within the graph.

### Dependencies
* `edges`
* `termini`
* `localdegree`
* `nsum`

### Porting notes
When translating this definition into other proof assistants, care should be taken to ensure that the summation is properly defined and that the `localdegree` function is correctly applied to each edge. Additionally, the handling of binders and the representation of graphs and vertices may differ between systems, requiring adjustments to the definition.

---

## DEGREE_DELETE_EDGE

### Name of formal statement
DEGREE_DELETE_EDGE

### Type of the formal statement
Theorem

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
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[localdegree; DELETE_EDGE_CLAUSES])
```

### Informal statement
For all graphs `G`, edges `e`, and vertices `v`, if `G` is a graph, `G` is locally finite, and `e` is an edge in `G`, then the degree of `v` in `G` equals the degree of `v` in the graph obtained by deleting `e` from `G`, plus 2 if `v` is the only vertex incident to `e`, plus 1 if `v` is one of the vertices incident to `e`, and unchanged otherwise.

### Informal sketch
* The proof begins by assuming the antecedent conditions: `G` is a graph, `G` is locally finite, and `e` is an edge in `G`.
* It then considers cases based on whether `v` is incident to `e` and whether `v` is the only vertex incident to `e`.
* The `REWRITE_TAC` steps apply definitions of `degree`, `DELETE_EDGE_CLAUSES`, and `IN_DELETE` to transform the goal.
* A key step involves showing that the set of edges incident to `v` (excluding `e`) is finite, which follows from `locally_finite` and `TERMINI_IN_VERTICES`.
* The proof then applies `NSUM_EQ` to equate the sums of local degrees over these sets of edges, leveraging `localdegree` and `DELETE_EDGE_CLAUSES`.
* The final steps simplify the resulting expression to match the desired conclusion.

### Mathematical insight
This theorem provides a way to relate the degree of a vertex in a graph to its degree in a modified graph where an edge has been deleted. The intuition is that deleting an edge can reduce the degree of its incident vertices. The theorem carefully considers the cases where a vertex is incident to the deleted edge, either as the sole vertex or as one of multiple vertices, and provides a precise formula for the change in degree.

### Dependencies
* Theorems:
  + `NSUM_EQ`
  + `IN_ELIM_THM`
  + `IN_SING`
  + `EXTENSION`
* Definitions:
  + `degree`
  + `delete_edge`
  + `localdegree`
  + `locally_finite`
  + `TERMINI_IN_VERTICES`
* Axioms or assumptions:
  + `graph`
  + `edges`
  + `termini`

### Porting notes
When translating this theorem into another proof assistant, pay close attention to the handling of `nsum` (which may be represented differently) and the application of `MATCH_MP_TAC` with `NSUM_EQ`, as these steps are critical to the proof. Additionally, the representation of graphs, edges, and vertices, as well as the definitions of `degree` and `delete_edge`, may vary between systems, requiring careful adaptation.

---

## eulerian_RULES,eulerian_INDUCT,eulerian_CASES

### Name of formal statement
eulerian_RULES,eulerian_INDUCT,eulerian_CASES

### Type of the formal statement
new_inductive_definition

### Formal Content
```ocaml
let eulerian_RULES,eulerian_INDUCT,eulerian_CASES = new_inductive_definition
 `(!G a. a IN vertices G /\ edges G = {} ==> eulerian G [] (a,a)) /\
  (!G a b c e es. e IN edges(G) /\ connects G e (a,b) /\
                  eulerian (delete_edge e G) es (b,c)
                  ==> eulerian G (CONS e es) (a,c))
```

### Informal statement
For all graphs `G` and vertices `a`, if `a` is in the vertices of `G` and the edges of `G` are empty, then `G` has an Eulerian path from `(a, a)` with an empty path. For all graphs `G`, vertices `a`, `b`, `c`, edges `e`, and paths `es`, if `e` is in the edges of `G`, `e` connects `G` from `(a, b)`, and `G` with `e` deleted has an Eulerian path from `(b, c)` with path `es`, then `G` has an Eulerian path from `(a, c)` with path `e` prepended to `es`.

### Informal sketch
* The definition of Eulerian paths in a graph `G` is inductive, with two main cases:
  * The base case: if a graph `G` has no edges, then there is an Eulerian path from any vertex `a` to itself, represented by an empty path.
  * The inductive step: if an edge `e` connects vertices `a` and `b` in `G`, and there is an Eulerian path in the graph with `e` removed from `(b, c)` with path `es`, then there is an Eulerian path in the original graph `G` from `(a, c)` by prepending `e` to `es`.
* The `connects` relation is used to ensure that the edge `e` indeed connects `a` and `b` in the graph.
* The `delete_edge` function is used to remove the edge `e` from the graph `G` in the inductive step.

### Mathematical insight
This definition captures the essence of an Eulerian path in graph theory, which is a path that visits every edge in a graph exactly once. The inductive definition provided here breaks down the problem into manageable cases, allowing for the construction of such paths in a step-by-step manner. It's crucial for proving properties about Eulerian paths and for algorithms designed to find such paths in graphs.

### Dependencies
* `vertices`
* `edges`
* `connects`
* `delete_edge`
* `eulerian`

### Porting notes
When translating this definition into other proof assistants like Lean, Coq, or Isabelle, pay special attention to how these systems handle inductive definitions, especially those involving recursive data structures like paths and graphs. The `connects` and `delete_edge` functions, as well as the `vertices` and `edges` predicates, need to be defined or imported from a graph theory library within the target system. Additionally, the handling of the empty path and the prepending of edges to paths (`CONS e es`) may require careful consideration due to differences in how these systems represent lists or sequences.

---

## EULERIAN_FINITE

### Name of formal statement
EULERIAN_FINITE

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULERIAN_FINITE = prove
 (`!G es ab. eulerian G es ab ==> FINITE (edges G)`,
  MATCH_MP_TAC eulerian_INDUCT THEN
  SIMP_TAC[DELETE_EDGE_CLAUSES; FINITE_DELETE; FINITE_RULES])
```

### Informal statement
For all graphs `G` and edges `es` and `ab`, if `G` is Eulerian with respect to `es` and `ab`, then the set of edges in `G` is finite.

### Informal sketch
* The proof starts by assuming `G` is Eulerian with respect to `es` and `ab`.
* It then applies `eulerian_INDUCT`, which is likely an inductive rule for Eulerian graphs.
* The `MATCH_MP_TAC` tactic is used to apply a theorem to the current goal, which involves `eulerian_INDUCT`.
* The `SIMP_TAC` tactic is then applied with a list of theorems (`DELETE_EDGE_CLAUSES`, `FINITE_DELETE`, `FINITE_RULES`) to simplify the goal, likely to show that the edges in `G` are finite.

### Mathematical insight
This theorem provides a fundamental property of Eulerian graphs, which are graphs that have an Eulerian path (a path that visits every edge exactly once). The theorem states that if a graph is Eulerian, then it must have a finite number of edges. This is an important result because it provides a necessary condition for a graph to be Eulerian.

### Dependencies
* `eulerian_INDUCT`
* `DELETE_EDGE_CLAUSES`
* `FINITE_DELETE`
* `FINITE_RULES`

### Porting notes
When porting this theorem to another proof assistant, care should be taken to ensure that the inductive rule `eulerian_INDUCT` is correctly translated. Additionally, the `MATCH_MP_TAC` and `SIMP_TAC` tactics may need to be replaced with equivalent tactics in the target system. The `DELETE_EDGE_CLAUSES`, `FINITE_DELETE`, and `FINITE_RULES` theorems will also need to be ported or re-proven in the target system.

---

## EULERIAN_ODD_LEMMA

### Name of formal statement
EULERIAN_ODD_LEMMA

### Type of the formal statement
Theorem

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
  COND_CASES_TAC THEN ASM_SIMP_TAC[ODD_ADD; ARITH] THEN ASM_MESON_TAC[])
```

### Informal statement
For all graphs `G` with edge set `es` and vertices `ab`, if `G` is Eulerian, then `G` is a graph and has a finite number of edges. Moreover, for every vertex `v` in `G`, the degree of `v` is odd if and only if the first and second elements of `ab` are distinct and `v` is equal to either the first or the second element of `ab`.

### Informal sketch
* The proof proceeds by induction on the `eulerian` property.
* The base case involves simplifying the degree of a vertex using `SIMP_TAC` and `NSUM_CLAUSES`.
* The inductive step uses `MATCH_MP_TAC` with `eulerian_INDUCT` and then applies `CONJ_TAC` to split the goal into two parts.
* The proof then uses `GEN_TAC`, `DISCH_THEN`, and `MP_TAC` to manipulate the assumptions and apply various theorems such as `DEGREE_DELETE_EDGE` and `TERMINI_IN_VERTICES`.
* The `ASM_CASES_TAC` and `COND_CASES_TAC` are used to handle different cases for the vertex `v` and the edge `e`.
* The `ASM_REWRITE_TAC` and `ASM_SIMP_TAC` are used to simplify the expressions and apply various rules such as `ODD_ADD` and `ARITH`.
* The `ASM_MESON_TAC` is used to apply the `MESON` tactic to prove the final goal.

### Mathematical insight
The `EULERIAN_ODD_LEMMA` theorem provides a characterization of Eulerian graphs in terms of the parity of the degree of their vertices. It states that a graph is Eulerian if and only if it has a finite number of edges and for every vertex, the degree is odd if and only if the vertex is one of the two distinct vertices that form the edge set `ab`. This theorem is important in graph theory as it provides a way to check if a graph is Eulerian by examining the degrees of its vertices.

### Dependencies
* Theorems:
	+ `eulerian_INDUCT`
	+ `DEGREE_DELETE_EDGE`
	+ `TERMINI_IN_VERTICES`
	+ `ODD_ADD`
	+ `ARITH`
* Definitions:
	+ `eulerian`
	+ `graph`
	+ `degree`
	+ `edges`
	+ `vertices`

### Porting notes
When porting this theorem to another proof assistant, one should be careful with the handling of binders and the application of tactics. The `MATCH_MP_TAC` and `CONJ_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `ASM_REWRITE_TAC` and `ASM_SIMP_TAC` tactics may need to be replaced with equivalent tactics that apply the same set of rules. The `MESON` tactic may also need to be replaced with an equivalent tactic that applies the same set of rules.

---

## EULERIAN_ODD

### Name of formal statement
EULERIAN_ODD

### Type of the formal statement
Theorem

### Formal Content
```ocaml
let EULERIAN_ODD = prove
 (`!G es a b.
        graph G /\ eulerian G es (a,b)
        ==> !v. v IN vertices G
                ==> (ODD(degree G v) <=> ~(a = b) /\ (v = a \/ v = b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP EULERIAN_ODD_LEMMA) THEN
  ASM_SIMP_TAC[FST; SND])
```

### Informal statement
For all graphs G, and for all pairs of vertices (a, b) in G, if G is eulerian with respect to the pair (a, b), then for all vertices v in G, the degree of v is odd if and only if a and b are distinct and v is either a or b.

### Informal sketch
* The proof begins by assuming that G is a graph and (a, b) is a pair of vertices in G such that G is eulerian with respect to (a, b).
* It then considers an arbitrary vertex v in G.
* The `EULERIAN_ODD_LEMMA` is applied to establish a relationship between the oddness of the degree of v and the conditions on a, b, and v.
* The proof uses `REPEAT GEN_TAC` to generalize the statement, and `DISCH_THEN` with `CONJUNCTS_THEN2 ASSUME_TAC MP_TAC` to manage the assumptions and implications.
* The `ASM_SIMP_TAC` with `FST` and `SND` is used to simplify the resulting expression.

### Mathematical insight
This theorem provides a characterization of the vertices with odd degree in an eulerian graph. It states that in an eulerian graph, a vertex has odd degree if and only if it is one of the two distinct vertices that the eulerian graph is defined with respect to. This is important because it helps in understanding the structure of eulerian graphs and has implications for graph theory and its applications.

### Dependencies
* `graph`
* `eulerian`
* `EULERIAN_ODD_LEMMA`
* `ODD`
* `degree`

### Porting notes
When porting this theorem to another proof assistant, special attention should be paid to the handling of the `EULERIAN_ODD_LEMMA` and the `ASM_SIMP_TAC` tactic, as these may have different equivalents in other systems. Additionally, the use of `REPEAT GEN_TAC` and `DISCH_THEN` with `CONJUNCTS_THEN2 ASSUME_TAC MP_TAC` may require careful translation to ensure that the proof strategy is preserved.

---

## KOENIGSBERG

### Name of formal statement
KOENIGSBERG

### Type of the formal statement
Theorem

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
  REWRITE_TAC[ARITH] THEN ARITH_TAC)
```

### Informal statement
For all graphs `G` where the vertices of `G` are `{0,1,2,3}`, the edges of `G` are `{10,20,30,40,50,60,70}`, and the termini of `G` for each edge are as specified, there does not exist an Eulerian path `es` from a vertex `a` to a vertex `b`.

### Informal sketch
* The proof starts by assuming the existence of a graph `G` with the given vertices and edges, and then applies the `EULERIAN_ODD` theorem to derive a contradiction.
* It uses `GEN_TAC` and `STRIP_TAC` to set up the proof and then applies `MP_TAC` with `ISPEC` to instantiate the `EULERIAN_ODD` theorem for the graph `G`.
* The proof then proceeds to rewrite the goal using `NOT_EXISTS_THM` and applies `MATCH_MP_TAC` with `MONO_FORALL` to introduce a universal quantifier.
* It then uses `DISCH_THEN` and `MP_TAC` to discharge assumptions and apply theorems, and `ANTS_TAC` to split the proof into cases.
* The proof uses various rewriting tactics, such as `ASM_REWRITE_TAC` and `SIMP_TAC`, to simplify the goal and apply theorems like `DE_MORGAN_THM` and `SET_RULE`.
* The `localdegree` and `degree` functions are used to analyze the degree of vertices in the graph.
* The proof finally uses `ARITH_TAC` to perform arithmetic simplifications and reach a contradiction.

### Mathematical insight
The KOENIGSBERG theorem is a classic result in graph theory, stating that there is no Eulerian path in the Koenigsberg graph, which is a graph with 4 vertices and 7 edges. This theorem is important because it shows that not all graphs have Eulerian paths, and it has implications for the study of graph theory and network analysis.

### Dependencies
* Theorems:
	+ `EULERIAN_ODD`
	+ `NOT_EXISTS_THM`
	+ `DE_MORGAN_THM`
	+ `SET_RULE`
* Definitions:
	+ `graph`
	+ `edges`
	+ `vertices`
	+ `termini`
	+ `eulerian`
	+ `localdegree`
	+ `degree`

### Porting notes
When porting this theorem to other proof assistants, note that the `GEN_TAC` and `STRIP_TAC` tactics may need to be replaced with equivalent tactics in the target system. Additionally, the `ISPEC` and `MP_TAC` tactics may need to be adjusted to match the specific instantiation and modus ponens rules in the target system. The use of `DISCH_THEN` and `MP_TAC` to discharge assumptions and apply theorems may also require adjustments. The `localdegree` and `degree` functions may need to be defined or imported from a library in the target system.

---

