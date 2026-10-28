module
public import Glauberman.FixedNormalPairLattice
public import Theory.GroupTheory.SubgroupTransport.IntersectionCenters
public import Theory.ElementaryAbelian.Injective

/-!
# The centers as exact cells of the intersection diagram

Finite descent supplies a first elementary intersection of maximum abelian
order. Literal restrictions identify all cells on that diagonal, so its
cells inside either original member are also maximum abelian. Reconstructing
the strips above it gives the center formulas for both members and their
intersection, all at the same diagonal parameter.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(b),(d),(e),
printed page 46. The existence theorem retains the elementary maximum cell
and initial reconstruction identities for subsequent commutator arguments.
-/

public section
open Subgroup Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G] {S T : Subgroup G}

omit [Finite G] in
private theorem elementary_cell_of_same_diagonal (φ : S ≃* T) {a b c d : ℕ}
    (hsum : a + b = c + d) [IsElementaryAbelian 2 (intervalCell φ c d)] :
    IsElementaryAbelian 2 (intervalCell φ a b) := by
  obtain ⟨e⟩ := intervalCell_equiv φ hsum
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

omit [Finite G] in
private theorem maximum_cell_of_same_diagonal (φ : S ≃* T) {a b c d : ℕ}
    (hsum : a + b = c + d) [IsElementaryAbelian 2 (intervalCell φ c d)]
    {R : Subgroup G} (hmax : intervalCell φ c d ∈ thompsonAbelianSubgroups R)
    (hle : intervalCell φ a b ≤ R) : intervalCell φ a b ∈ thompsonAbelianSubgroups R := by
  let _ := elementary_cell_of_same_diagonal φ hsum
  have hc : Nat.card (intervalCell φ a b) = Nat.card (intervalCell φ c d) := by
    rw [card_intervalCell φ a b, card_intervalCell φ c d, hsum]
  exact ⟨hle, inferInstance, fun B hB hBc => (hmax.2.2 B hB hBc).trans_eq hc.symm⟩

private theorem center_cell_of_elementary_maximum (φ : S ≃* T) (v a b n : ℕ)
    [IsElementaryAbelian 2 (intervalCell φ 1 v)]
    (hmax : intervalCell φ 1 v ∈ thompsonAbelianSubgroups (intervalCell φ a b))
    (hsum : a + b + n = v + 1) (hpos : 1 ≤ a + b)
    (hgen : ∀ c d : ℕ, 1 ≤ c + d → c + d ≤ v →
      intervalCell φ c (d + 1) ⊔ intervalCell φ (c + 1) d = intervalCell φ c d) :
    centerIn (intervalCell φ a b) = intervalCell φ (a + n) (b + n) := by
  apply intervalCell_center_eq
  · have hm := maximum_cell_of_same_diagonal φ (a := a) (b := b + n)
      (by omega) hmax (intervalCell_antitone φ le_rfl (by omega))
    exact le_maximum_abelian_of_centralizes hm inf_le_left
      (inf_le_right.trans (centralizer_le hm.1))
  · have hm := maximum_cell_of_same_diagonal φ (a := a + n) (b := b)
      (by omega) hmax (intervalCell_antitone φ (by omega) le_rfl)
    exact le_maximum_abelian_of_centralizes hm inf_le_left
      (inf_le_right.trans (centralizer_le hm.1))
  · intro i j hij
    let _ := elementary_cell_of_same_diagonal φ (a := a + i) (b := b + j)
      (c := 1) (d := v) (by omega)
    infer_instance
  · intro i j hij
    exact hgen (a + i) (b + j) (by omega) (by omega)

/-- The original member centers and intersection center are literal cells
of the same partial-isomorphism rectangle. -/
theorem centers_eq_cells_of_elementary_maximum_lattice (φ : S ≃* T) (v : ℕ)
    (hv : 0 < v) [IsElementaryAbelian 2 (intervalCell φ 1 v)]
    (hS : intervalCell φ 1 v ∈ thompsonAbelianSubgroups S)
    (hT : intervalCell φ 1 v ∈ thompsonAbelianSubgroups T)
    (hgen : ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ v →
      intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b) :
    centerIn S = intervalCell φ v (v + 1) ∧
      centerIn T = intervalCell φ (v + 1) v ∧
      centerIn (S ⊓ T) = intervalCell φ v v := by
  have hQ : intervalCell φ 1 v ∈ thompsonAbelianSubgroups (S ⊓ T) :=
    ⟨le_inf hS.1 hT.1, hS.2.1, fun B hB hBc => hS.2.2 B (hB.trans inf_le_left) hBc⟩
  have hs := center_cell_of_elementary_maximum φ v 0 1 v
    (by simpa only [intervalCell_initial_left] using hS) (by omega) (by omega) hgen
  have ht := center_cell_of_elementary_maximum φ v 1 0 v
    (by simpa only [intervalCell_initial_right] using hT) (by omega) (by omega) hgen
  have hq := center_cell_of_elementary_maximum φ v 1 1 (v - 1)
    (by simpa only [intervalCell_intersection] using hQ) (by omega) (by omega) hgen
  simpa only [intervalCell_initial_left, intervalCell_initial_right, intervalCell_intersection,
    Nat.zero_add, show 1 + v = v + 1 by omega, show 1 + (v - 1) = v by omega] using
      And.intro hs (And.intro ht hq)

/-- Finite descent supplies the exact center cells under the numerical
pair hypotheses, including their common elementary-row parameter. -/
theorem IntersectionPair.exists_center_cells (P : IntersectionPair G)
    (h : NumericalPair P.left P.right P.equiv) :
    ∃ v : ℕ, 0 < v ∧
      IsElementaryAbelian 2 ↥(intervalCell P.equiv 1 v) ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.left ∧
      intervalCell P.equiv 1 v ∈ thompsonAbelianSubgroups P.right ∧
      (∀ a b : ℕ, 1 ≤ a + b → a + b ≤ v →
        intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
          intervalCell P.equiv a b) ∧
      centerIn P.left = intervalCell P.equiv v (v + 1) ∧
      centerIn P.right = intervalCell P.equiv (v + 1) v ∧
      centerIn (P.left ⊓ P.right) = intervalCell P.equiv v v := by
  obtain ⟨n, hE, hS, hT, hnum, _⟩ := P.exists_first_elementary_maximum_row h
  rw [P.row_intersection_cell] at hE hS hT
  let _ := hE
  have hi := P.rectangleStepIndex_next_eq_four n hnum
  have hgen : ∀ a b : ℕ, 1 ≤ a + b → a + b ≤ n + 1 →
      intervalCell P.equiv a (b + 1) ⊔ intervalCell P.equiv (a + 1) b =
        intervalCell P.equiv a b := by
    intro a b hab hbound
    apply intervalCell_sup_of_stepIndex_lower P.equiv hab (show a + b + 1 ≤ n + 2 by omega)
    rw [P.rectangleStepIndex_eq_four 0 h, hi]
  exact ⟨n + 1, by omega, hE, hS, hT, hgen,
    centers_eq_cells_of_elementary_maximum_lattice P.equiv (n + 1) (by omega) hS hT hgen⟩

end Glauberman
