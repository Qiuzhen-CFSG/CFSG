module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.Noncentral
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.CentralReduction

/-!
# Reduction of characteristic-two Goldschmidt amalgams

If both original vertices move the common Sylow omega center, each vertex
is S₄ or C₂×S₄ and has order at most 48. Otherwise exactly one vertex
centralizes that omega center. The latter is the remaining source branch;
no universal order bound or six-case exhaustion is asserted here.

The imported coset-kernel theorem also identifies the degree-six quotient
of either original vertex and proves its order divides 48. The final
application retains the actual images and original overlap in G/O₂(G).

Source: Aschbacher–Smith F.6.5 and Stellmacher §7, (8.2).
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.SectionsFiveToSeven
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The complete noncentral branch and the two remaining central orientations. -/
theorem IsGoldschmidtTriple.characteristic_two_order_or_central_omega
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂) :
    (Nat.card G₁ ≤ 48 ∧ Nat.card G₂ ≤ 48) ∨
      (⁅G₁, omegaOneCenter (G₁ ⊓ G₂)⁆ = ⊥ ∧
        ⁅G₂, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥) ∨
      (⁅G₂, omegaOneCenter (G₁ ⊓ G₂)⁆ = ⊥ ∧
        ⁅G₁, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥) := by
  by_cases hc₁ : ⁅G₁, omegaOneCenter (G₁ ⊓ G₂)⁆ = ⊥
  · exact Or.inr (Or.inl ⟨hc₁,(h.omega_center_moved hcore).resolve_left (not_not.mpr hc₁)⟩)
  by_cases hc₂ : ⁅G₂, omegaOneCenter (G₁ ⊓ G₂)⁆ = ⊥
  · exact Or.inr (Or.inr ⟨hc₂,hc₁⟩)
  exact Or.inl (h.local_card_le_forty_eight_of_noncentral_omega hcore hgood₁ hgood₂ hc₁ hc₂)

/-- The source reduction on the original quotient images and whole overlap image. -/
theorem IsGoldschmidtTriple.quotient_characteristic_two_order_or_central_omega
    (h : IsGoldschmidtTriple G₁ G₂)
    (hgood₁ : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (hgood₂ : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G)))) :
    let q := QuotientGroup.mk' (pCore 2 G)
    let A := G₁.map q
    let B := G₂.map q
    let W := omegaOneCenter ((G₁ ⊓ G₂).map q)
    (Nat.card A ≤ 48 ∧ Nat.card B ≤ 48) ∨
      (⁅A,W⁆ = ⊥ ∧ ⁅B,W⁆ ≠ ⊥) ∨ (⁅B,W⁆ = ⊥ ∧ ⁅A,W⁆ ≠ ⊥) := by
  dsimp only
  rw [h.quotient_twoCore_intersection]
  exact h.quotient_twoCore.characteristic_two_order_or_central_omega
    h.quotient_twoCore_eq_bot hgood₁ hgood₂

end CFSG.Quasithin.ChapterF
