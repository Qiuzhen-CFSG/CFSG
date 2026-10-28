module

public import Theory.SpecificGroups.PSL3Even.LargePlaneNormalizers.Planes

/-!
# Automorphism stabilizers of subgroups meeting a PSL₃ plane largely

For a subgroup Q of the upper-unitriangular Sylow subgroup, an intersection
with one root plane larger than |F| determines either that plane or the Sylow
subgroup under every automorphism stabilizing Q. If every element of Q squares
to one, the coordinate geometry puts Q in the chosen plane, which is its full
centralizer. Otherwise the two-core of the centralizer of its squares recovers
the Sylow subgroup. The alternative is uniform over the entire stabilizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
§5.3.5–7, printed p.660; the PSL₃ lower obstruction in E.1.14(1), p.214.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.LargePlaneNormalizers
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private theorem le_marked_plane (A : Subgroup (U F)) (b : Bool)
    (he : ∀ a ∈ A, a^2 = 1)
    (hc : Nat.card F < Nat.card (A ⊓ (if b then V₁ F else V₂ F) : Subgroup (U F))) :
    A ≤ if b then V₁ F else V₂ F := by
  have hbound (h : A ⊓ (if b then V₁ F else V₂ F) ≤ Z F) : False := by
    have hcard := Subgroup.card_le_of_le h
    rw [card_Z] at hcard
    exact (not_le_of_gt hc) hcard
  rcases le_plane_of_exponent_two F A he with h₁ | h₂
  · cases b
    · exact False.elim (hbound (fun a ha =>
        (mem_Z F a).mpr ⟨(mem_V₂ F a).mp ha.2, (mem_V₁ F a).mp (h₁ ha.1)⟩))
    · exact h₁
  · cases b
    · exact h₂
    · exact False.elim (hbound (fun a ha =>
        (mem_Z F a).mpr ⟨(mem_V₂ F a).mp (h₂ ha.1), (mem_V₁ F a).mp ha.2⟩))

/-- Large plane intersections give a uniform alternative for the whole automorphism
stabilizer of Q, not a separate choice for each automorphism. -/
theorem automorphism_alternative (Q : Subgroup PSL(3,F)) (hQ : Q ≤ unipotent F)
    (b : Bool) {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (hc : Nat.card F < Nat.card (Q ⊓
      (if b then V₁ F else V₂ F).map (projective F) : Subgroup PSL(3,F))) :
    (∀ α : MulAut PSL(3,F), Q.map α.toMonoidHom = Q →
      ((if b then V₁ F else V₂ F).map (projective F)).map α.toMonoidHom =
        (if b then V₁ F else V₂ F).map (projective F)) ∨
    (∀ α : MulAut PSL(3,F), Q.map α.toMonoidHom = Q →
      (unipotent F).map α.toMonoidHom = unipotent F) := by
  by_cases he : ∀ q ∈ Q, q^2 = 1
  · left
    let A := Q.comap (projective F)
    have hAr : A.map (projective F) = Q :=
      map_comap_eq_self (by rw [projective_range]; exact hQ)
    have hAi : (A ⊓ (if b then V₁ F else V₂ F)).map (projective F) =
        Q ⊓ (if b then V₁ F else V₂ F).map (projective F) := by
      rw [map_inf _ _ _ (projective_injective F), hAr]
    have hcard : Nat.card F < Nat.card
        (A ⊓ (if b then V₁ F else V₂ F) : Subgroup (U F)) := by
      rw [← hAi, Subgroup.card_map_of_injective (projective_injective F)] at hc
      exact hc
    have hAe : ∀ a ∈ A, a^2 = 1 := by
      intro a ha
      apply projective_injective F
      rw [map_pow, map_one]
      exact he _ ha
    have hAP := le_marked_plane F A b hAe hcard
    have hcQ : centralizer (Q : Set PSL(3,F)) =
        (if b then V₁ F else V₂ F).map (projective F) := by
      rw [← hAr]
      exact centralizer_large_plane F A b hAP
        (hcard.trans_le (Subgroup.card_le_of_le inf_le_left))
    intro α hα
    rw [← hcQ, Theory.Quasithin.map_centralizer, hα]
  · push Not at he
    exact Or.inr (fun α hα => map_unipotent_of_square_ne_one F Q hQ he hf hF α hα)

end Matrix.PSL3Even.LargePlaneNormalizers
