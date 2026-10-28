module
public import Glauberman.FixedNormalPairDoubleLattice
public import Theory.GroupTheory.SubgroupTransport.IntersectionCommutators
public import Theory.GroupTheory.DisjointConjugateCenter

/-!
# The shifted-center commutator estimate for the numerical pair

Both original members normalize their common intersection and therefore its
full center. The exact center cell translates these normality facts into the
two bounds used by the rectangle commutator theorem. The resulting deeper
cell contains the commutator of the left boundary cell with that center.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(f),
printed pages 46–47. This retains the elementary row, center markings and
reconstruction through 2v - 1 for the later natural-module covering step.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

theorem IntersectionPair.exists_double_lattice_center_commutator (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
    ∃ v : ℕ, 0 < v ∧
      IsElementaryAbelian 2 ↥(intervalCell P.equiv 1 v) ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.left ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.right ∧
      (∀ a b : ℕ, 1 ≤ a + b → a + b < 2 * v →
        intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
          intervalCell P.equiv a b) ∧
      centerIn P.left = intervalCell P.equiv v (v + 1) ∧
      centerIn P.right = intervalCell P.equiv (v + 1) v ∧
      centerIn (P.left ⊓ P.right) = intervalCell P.equiv v v ∧
      ⁅intervalCell P.equiv 0 (2 * v), intervalCell P.equiv v v⁆ ≤
        intervalCell P.equiv v (2 * v) := by
  obtain ⟨v, hv, hE, hS, hT, hgen, hzS, hzT, hzQ⟩ := P.exists_double_lattice_center_cells h
  have hnS := normalizes_centerIn (S := P.left ⊓ P.right) (A := P.left) h.normal_left
  have hnT := normalizes_centerIn (S := P.left ⊓ P.right) (A := P.right) h.normal_right
  rw [hzQ] at hnS hnT
  exact ⟨v, hv, hE, hS, hT, hgen, hzS, hzT, hzQ,
    intervalCell_center_commutator_bound P.equiv v hv hnS hnT⟩

end Glauberman
