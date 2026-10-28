module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing.Reduction
import Mathlib.Tactic.FinCases

/-!
# Coordinates and standard subspaces of the binary SL₅ exterior square

The basis is ordered 12, 13, 14, 15, 23, 24, 25, 34, 35, 45, with zero-based
indices in Lean. Its coordinate equivalence intertwines the actual determinant-one
matrix action with the matrix of two-by-two minors. Coordinate spans define the
five standard subspaces used in Aschbacher--Smith, §12.5, printed pp.817–821
(PDF pp.834–838). The finite enumeration is adapted from this project's
`ExteriorVanishing/SquareRelations.lean`; all calculations use the actual exterior
power, not an abstract ten-dimensional space with a family label.
-/

@[expose] public section

open scoped BigOperators
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

abbrev V := ExteriorModule 2
abbrev Coordinates := Fin 10 → ZMod 2

def index : Fin 10 → ExteriorIndex 2 := ![
  ⟨{0, 1}, by change Finset.card _ = 2; decide⟩,
  ⟨{0, 2}, by change Finset.card _ = 2; decide⟩,
  ⟨{0, 3}, by change Finset.card _ = 2; decide⟩,
  ⟨{0, 4}, by change Finset.card _ = 2; decide⟩,
  ⟨{1, 2}, by change Finset.card _ = 2; decide⟩,
  ⟨{1, 3}, by change Finset.card _ = 2; decide⟩,
  ⟨{1, 4}, by change Finset.card _ = 2; decide⟩,
  ⟨{2, 3}, by change Finset.card _ = 2; decide⟩,
  ⟨{2, 4}, by change Finset.card _ = 2; decide⟩,
  ⟨{3, 4}, by change Finset.card _ = 2; decide⟩]

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

theorem index_injective : Function.Injective index := by decide

theorem index_bijective : Function.Bijective index := by
  apply (Fintype.bijective_iff_injective_and_card index).mpr
  refine ⟨index_injective, ?_⟩
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, Set.powersetCard.card]
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

def pair : Fin 10 → Fin 2 → Fin 5 :=
  ![![0,1], ![0,2], ![0,3], ![0,4], ![1,2], ![1,3], ![1,4], ![2,3], ![2,4], ![3,4]]

def pairEmbedding (s : Fin 10) : Fin 2 ↪o Fin 5 :=
  OrderEmbedding.ofStrictMono (pair s) ((by decide : ∀ s, StrictMono (pair s)) s)

theorem index_emb (s : Fin 10) : index s = Set.powersetCard.ofFinEmbEquiv (pairEmbedding s) := by
  fin_cases s <;> decide

theorem index_order (s : Fin 10) : Set.powersetCard.ofFinEmbEquiv.symm (index s) = pairEmbedding s := by
  rw [index_emb, Equiv.symm_apply_apply]

/-- Lexicographic identification of the exterior-basis indices. -/
noncomputable def indexEquiv : Fin 10 ≃ ExteriorIndex 2 :=
  Equiv.ofBijective index index_bijective

/-- The standard wedge basis in lexicographic order. -/
noncomputable def basis : Module.Basis (Fin 10) (ZMod 2) V :=
  (exteriorBasis 2).reindex indexEquiv.symm

/-- Coordinates in the ordered wedge basis. -/
noncomputable def coordinates : V ≃ₗ[ZMod 2] Coordinates := basis.equivFun

@[simp] theorem basis_apply (i : Fin 10) : basis i = exteriorBasis 2 (index i) := by
  simp [basis, indexEquiv]

@[simp] theorem coordinates_apply (v : V) (i : Fin 10) :
    coordinates v i = exteriorCoordinates 2 v (index i) := rfl

/-- The ordered basis consists of genuine wedges of standard vectors. -/
theorem basis_wedge (s : Fin 10) :
    basis s = exteriorPower.ιMulti (ZMod 2) 2
      (fun i => Pi.single (pair s i) 1) := by
  simp only [basis_apply, exteriorBasis, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, index_order, pairEmbedding,
    Function.comp_def, Pi.basisFun_apply]
  rfl

/-- The explicit minor matrix for the exterior-square action. -/
def actionMatrix (g : Group) : Matrix (Fin 10) (Fin 10) (ZMod 2) := fun s t =>
  g.val (pair s 0) (pair t 0) * g.val (pair s 1) (pair t 1) -
    g.val (pair s 1) (pair t 0) * g.val (pair s 0) (pair t 1)

theorem actionMatrix_entry (g : Group) (s t : Fin 10) :
    exteriorMatrix 2 g (index s) (index t) = actionMatrix g s t := by
  simp [exteriorMatrix, Matrix.det_fin_two, index_order, pairEmbedding, actionMatrix]

/-- Equivariance of the coordinate equivalence, including its actual group action. -/
theorem coordinates_action (g : Group) (v : V) :
    coordinates (exteriorAction 2 g v) = (actionMatrix g).mulVec (coordinates v) := by
  ext s
  rw [coordinates_apply, exteriorCoordinates_action]
  change (∑ t, exteriorMatrix 2 g (index s) t * exteriorCoordinates 2 v t) = _
  rw [← indexEquiv.sum_comp]
  change (∑ t, exteriorMatrix 2 g (index s) (index t) *
    exteriorCoordinates 2 v (index t)) = _
  simp only [actionMatrix_entry, ← coordinates_apply]
  rfl

/-- The span of a specified subset of the wedge basis. -/
noncomputable def coordinateSpan (S : Finset (Fin 10)) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) (basis '' (S : Set (Fin 10)))

/-- Membership is exactly vanishing of all coordinates outside the subset. -/
theorem mem_coordinateSpan (S : Finset (Fin 10)) (v : V) :
    v ∈ coordinateSpan S ↔ ∀ i, i ∉ S → coordinates v i = 0 := by
  rw [coordinateSpan, basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    coordinates, Module.Basis.equivFun_apply]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h i hn)
  · intro h i hi
    by_contra hn
    exact hi (h i hn)

/-- The dimension of a coordinate span is the number of its basis vectors. -/
theorem finrank_coordinateSpan (S : Finset (Fin 10)) :
    Module.finrank (ZMod 2) (coordinateSpan S) = S.card := by
  have hr : basis '' (S : Set (Fin 10)) = Set.range (fun i : S => basis i) := by
    ext x
    simp
  rw [coordinateSpan, hr]
  simpa only [Function.comp_def, Fintype.card_coe] using
    finrank_span_eq_card (basis.linearIndependent.comp
      (fun i : S => (i : Fin 10)) Subtype.val_injective)

/-- Λ²Γ₂. -/
noncomputable def V₁ : Submodule (ZMod 2) V := coordinateSpan {0}
/-- Λ²Γ₃. -/
noncomputable def V₃ : Submodule (ZMod 2) V := coordinateSpan {0, 1, 4}
/-- Γ₁ ∧ Γ. -/
noncomputable def V₄ : Submodule (ZMod 2) V := coordinateSpan {0, 1, 2, 3}
/-- Λ²Γ₄. -/
noncomputable def V₆ : Submodule (ZMod 2) V := coordinateSpan {0, 1, 2, 4, 5, 7}
/-- Γ₂ ∧ Γ. -/
noncomputable def V₇ : Submodule (ZMod 2) V := coordinateSpan {0, 1, 2, 3, 4, 5, 6}
/-- Γ₁ ∧ Γ₄, denoted V₃′ in 12.5.7 and 12.5.10. -/
noncomputable def V₃' : Submodule (ZMod 2) V := coordinateSpan {0, 1, 2}

/-- The two source representatives, before proving orbit exhaustion. -/
noncomputable def decomposable : V := basis 0
noncomputable def nondecomposable : V := basis 0 + basis 7

theorem standard_dimensions :
    Module.finrank (ZMod 2) V₁ = 1 ∧ Module.finrank (ZMod 2) V₃ = 3 ∧
    Module.finrank (ZMod 2) V₄ = 4 ∧ Module.finrank (ZMod 2) V₆ = 6 ∧
    Module.finrank (ZMod 2) V₇ = 7 ∧ Module.finrank (ZMod 2) V₃' = 3 := by
  exact ⟨(finrank_coordinateSpan _).trans (by decide),
    (finrank_coordinateSpan _).trans (by decide),
    (finrank_coordinateSpan _).trans (by decide),
    (finrank_coordinateSpan _).trans (by decide),
    (finrank_coordinateSpan _).trans (by decide),
    (finrank_coordinateSpan _).trans (by decide)⟩

end Representation.SL5ExteriorSquare
