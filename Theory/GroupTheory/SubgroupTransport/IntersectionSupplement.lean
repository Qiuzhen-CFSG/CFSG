module
public import Theory.GroupTheory.SubgroupTransport.IntersectionLattice

/-!
# Boundary supplements in the intersection rectangle

Repeated adjacent reconstruction expresses the original left member as
the join of the terminal left boundary cell and the original intersection.
This supplies the supplement used to replace the shifted-center commutator
by the full Sylow commutator.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6(g),
printed page 47.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- A reconstructed left boundary supplies a supplement to the initial
intersection, at the last permitted depth. -/
theorem intervalCell_left_supplement (φ : S ≃* T) (w : ℕ) (hw : 0 < w)
    (hgen : ∀ b : ℕ, 1 ≤ b → b < w →
      intervalCell φ 0 (b + 1) ⊔ intervalCell φ 1 b = intervalCell φ 0 b) :
    intervalCell φ 0 w ⊔ (S ⊓ T) = S := by
  have hle : intervalCell φ 0 w ⊔ (S ⊓ T) ≤ S := by
    refine sup_le ?_ inf_le_left
    rw [show w = (w - 1) + 1 by omega]
    exact intervalCell_le_domain φ 0 (w - 1)
  apply le_antisymm hle
  have key : ∀ n : ℕ, n < w →
      intervalCell φ 0 (w - n) ≤ intervalCell φ 0 w ⊔ (S ⊓ T) := by
    intro n
    induction n with
    | zero => intro _; simpa only [Nat.sub_zero] using (le_sup_left : intervalCell φ 0 w ≤ _)
    | succ n ih =>
      intro hn
      rw [← hgen (w - (n + 1)) (by omega) (by omega)]
      refine sup_le ?_ ?_
      · simpa only [show w - (n + 1) + 1 = w - n by omega] using ih (by omega)
      · apply le_sup_of_le_right
        rw [← intervalCell_intersection φ]
        exact intervalCell_antitone φ le_rfl (by omega)
  have hh := key (w - 1) (by omega)
  simpa only [show w - (w - 1) = 1 by omega, intervalCell_initial_left] using hh

end Theory.GroupTheory.SubgroupTransport
