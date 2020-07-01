import tactic
-- there is no definition of a graph in mathlib

/-- an undirected graph with possible loops -/
structure graph (V : Type) :=
(E : set (V × V))
(symm : ∀ e ∈ E, (prod.snd e, prod.fst e) ∈ E)

-- Example of a graph with two vertices, a and b

/-- let v2 be a type with two terms a and b -/
inductive v2 
| a : v2
| b : v2

-- v2 = {a,b} from a set theory point of view

open v2

def G : graph v2 :=
{ E := {(a,b),(b,a)},
  symm := begin
    -- check all the cases
    intros e he,
    cases he, cases he, simp, cases he, simp
  end }


-- Can you define a tree?
-- Can you prove G is a tree?
-- Can you define the graph with vertices {0,1,2,...,n} and edges
-- from x to x+1? Can you prove it's a tree?
