import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Multiset.Lattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Complex.Basic

open SimpleGraph
open scoped Classical

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

-- MATRIX INVARIANTS
/--
If you use this code instead
```
noncomputable def adjacency_matrix (G: SimpleGraph V) :=
  G.adjMatrix ℕ
noncomputable def adjacency_eigenvalues (G : SimpleGraph V) : Set ℝ :=
  spectrum ℝ (adjacency_eigenvalues G))
```
there is this type error:

failed to synthesize
  Algebra ℝ (Matrix V V ℚ)

Thus I manually do the cast.

MRD: I think it's OK to use adjMatrix ℝ rather than casting adjacency_matrix.
-/

noncomputable def adjacency_matrix (G: SimpleGraph V) : Matrix V V ℕ :=
  G.adjMatrix ℕ

-- I realized if this returns a Set, there is no multiplicity.
-- This makes counting zero eigenvalues difficult.
noncomputable def adjacency_eigenvalues_set (G : SimpleGraph V) : Set ℝ :=
  let real_adj_matrix : Matrix V V ℝ := (adjacency_matrix G).map (↑)
  spectrum ℝ real_adj_matrix

noncomputable def adjacency_eigenvalues_set' (G : SimpleGraph V) :=
  spectrum ℝ (G.adjMatrix ℝ)

-- Alternatively, eigenvalues can return an indexable object
noncomputable def adjacency_eigenvalues_ind (G : SimpleGraph V) : V → ℝ := by
  let real_adj_matrix : Matrix V V ℝ := (G.adjMatrix ℝ) -- (adjacency_matrix G).map (↑)
  have hS : Matrix.IsSymm real_adj_matrix := G.isSymm_adjMatrix
  have hA : Matrix.IsHermitian real_adj_matrix := by
    simpa [Matrix.conjTranspose,hS]
  exact hA.eigenvalues

-- by default, return a set of eigenvalues
noncomputable def adjacency_eigenvalues (G : SimpleGraph V) := adjacency_eigenvalues_set G

noncomputable def smallest_adjacency_eigenvalue (G : SimpleGraph V) :=
  sInf (adjacency_eigenvalues_set G)

noncomputable def spectral_radius (G : SimpleGraph V) :=
  sSup ((adjacency_eigenvalues_set G).image abs)

-- To count the zero eigenvales:
-- number of zero eigenvalues = dimension kernel = n - dim image
noncomputable def zero_adjacency_eigenvalues_count (G : SimpleGraph V) :=
  Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)))

noncomputable def zero_adjacency_eigenvalues_count' (G: SimpleGraph V) :=
    Module.rank ℝ (LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)))

noncomputable def algebraic_connectivity (G : SimpleGraph V) : Option ℝ :=
  let eigval_func := adjacency_eigenvalues_ind G
  let image := Finset.image eigval_func Finset.univ
  let sorted := image.sort (· ≤ ·)
  sorted[1]?

/--
(s.erase s.sup).sup does not work because ℝ doesn't have ⊥ element.
-/
noncomputable def second_largest_adjacency_eigenvalue
      (G : SimpleGraph V) [h : Nontrivial V] := by
  -- I think we have to work over ℂ in order to say that the
  -- number of roots is precisely equal.
  -- however, working over ℂ produces issues with sorting the eigenvalues
  -- (I will have to define a custom order on ℂ)
  -- Instead, I will take advantage of the fact that undirected graphs
  -- have symmetric adjacency matrices, so all the eigenvalues are real. by sorry
  let eigval_func : V → ℝ := adjacency_eigenvalues_ind G
  let eigval_list : List ℝ := List.map eigval_func (Finset.univ).toList
  have eigval_list_card_len_2 : eigval_list.length ≥ 2 := by
    rw [List.length_map]
    simp only [Finset.length_toList, Finset.card_univ, ge_iff_le]
    exact Fintype.one_lt_card_iff_nontrivial.mpr h
  let sorted_evals := eigval_list.mergeSort (· ≥ ·)
  have right_len : sorted_evals.length ≥ 2 := by
    rw [List.length_mergeSort]
    exact eigval_list_card_len_2
  exact sorted_evals[1]

/--
Because G.degree returns a ℕ, it doesn't suffice to assume
the matrix entries are of type α with [Neg α] [Zero α] [One α]
-/
noncomputable def laplacian_matrix (G : SimpleGraph V): Matrix V V ℤ :=
  Matrix.of fun u v =>
    if u == v then
        G.degree u
    else if G.Adj u v then
        -1
    else
        0

def laplacian_eigenvalues (G : SimpleGraph V) : Set ℝ :=
  let real_lap_matrix : Matrix V V ℝ := (laplacian_matrix G).map (↑)
  spectrum ℝ real_lap_matrix

noncomputable def largest_laplacian_eigenvalue (G : SimpleGraph V) :=
  sSup (laplacian_eigenvalues G)
