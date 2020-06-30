import tactic
-- there is no definition of a graph in mathlib

structure graph (V : Type) :=
(E : set (V × V))
(symm : ∀ e ∈ E, (prod.snd e, prod.fst e) ∈ E)

-- Example of a graph with two vertices, a and b

inductive v2 
| a : v2
| b : v2

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
