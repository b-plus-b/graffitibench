import TxGraffitiBench.Invariants.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Metric

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open Classical

/--
SHIM DEFINITIONS FOR CONJECTURE USAGE
The output of TxGraffiti2 uses slighly different names which we define as syntactic sugar here.
This allows the output to be effectively directly exportable into Lean.
-/
alias max_degree := maximum_degree
alias min_degree := minimum_degree
def order (_ : SimpleGraph V) := Fintype.card V
abbrev nontrivial (_ : SimpleGraph V) : Prop := Nontrivial V
noncomputable def size (G : SimpleGraph V) := G.edgeFinset.card
def connected (G : SimpleGraph V) := G.Connected
def bipartite (G : SimpleGraph V) := G.IsBipartite

def tree (G : SimpleGraph V) := G.IsTree
def triangle_free (G : SimpleGraph V) := G.CliqueFree 3
def K_4_free (G : SimpleGraph V) := G.CliqueFree 4

def has_claw (G : SimpleGraph V) :=
  ∃ (a b c d : V), G.Adj a b ∧ G.Adj a c ∧ G.Adj a d
  ∧ (¬G.Adj b c) ∧ (¬G.Adj b d) ∧ (¬G.Adj c d)

def claw_free (G : SimpleGraph V) :=
  ¬ has_claw G

def regular (G : SimpleGraph V) :=
  ∃ d, G.IsRegularOfDegree d

def cubic (G : SimpleGraph V) :=
  G.IsRegularOfDegree 3

def subcubic (G : SimpleGraph V) :=
  ∀ v : V, G.degree v ≤ 3

def eulerian (G : SimpleGraph V) :=
  ∃ u, ∃ (p : G.Walk u u), p.IsEulerian ∧ p.IsCircuit

noncomputable def diameter (G : SimpleGraph V) : ℕ :=
  G.diam

-- make radius a nat in case
noncomputable def radius (G : SimpleGraph V) : ℕ :=
  G.radius.toNat

noncomputable def triameter (G : SimpleGraph V) : ℕ :=
  let S : Set ℕ :=
    {n : ℕ | ∃ u v w : V, G.dist u v + G.dist u w + G.dist v w = n}
  sSup S
