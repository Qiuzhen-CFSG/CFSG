module
public import Glauberman.FixedNormalPairRectangle
public import Glauberman.PushingUpIntersectionRows

/-!
# A maximum elementary cell for the original twisted Sylow isomorphism

The elementary maximum row from the original Main Hypothesis is identified
with a cell of the actual partial-isomorphism rectangle. This retains the
specified Sylow automorphism, the chosen conjugating element and the ambient
subgroup, so later diagram arguments use the original subgroup embeddings.

Source: Niles, *Pushing-up in finite groups* (1979), Sections 2 and 4,
especially Proposition 4.6(b). No natural-action premise remains explicit.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

theorem original_psl2_four_elementary_maximum_cell
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α) :
    ∃ g : H,
      (S : Subgroup H) ⊔ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (S : Subgroup H) ⊓ (S : Subgroup H).map (MulAut.conj g).toMonoidHom = pCore 2 H ∧
      ∃ n, let A := intervalCell (twistedConjugacy (S : Subgroup H) α g) 1 (n + 1)
        IsElementaryAbelian 2 A ∧ A ∈ thompsonAbelianSubgroups (S : Subgroup H) ∧
          A ∈ thompsonAbelianSubgroups ((S : Subgroup H).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨g, hgen, hinter, n, hE, hL, hR⟩ :=
    original_psl2_four_elementary_maximum_row hF S α hu K e hf hno
  rw [IntersectionPair.row_intersection_cell] at hE hL hR
  exact ⟨g, hgen, hinter, n, hE, hL, hR⟩

end Glauberman
