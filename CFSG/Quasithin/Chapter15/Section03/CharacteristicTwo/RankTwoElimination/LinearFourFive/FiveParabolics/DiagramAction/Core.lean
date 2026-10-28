module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.Lift

/-!
# Core-quotient adjustment for the diagram argument

If a subgroup and its overgroup have core quotients of equal order, the
subgroup surjects onto the overgroup quotient. Its projection kernel lies
in its own two-core. Consequently each element normalizing the subgroup
can be adjusted by a subgroup element so that all displacements lie in
that two-core. No ambient normality of the subgroup is required.

This is the finite-group step used below for Y₊(S ∩ L) ≤ Y₊S.
Source: Aschbacher–Smith, 15.3.24, printed p.1129 of refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction
variable {G : Type*} [Group G] [Finite G] {B H : Subgroup G}

omit [Finite G] in
private theorem restriction_core_le (hBH : B ≤ H) :
    (((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hBH)).ker) ≤ pCore 2 B := by
  have he : ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hBH)).ker =
      (pCore 2 H).comap (inclusion hBH) := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rw [he]
  exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective _ (inclusion_injective hBH)⟩

theorem core_projection_surjective (hBH : B ≤ H)
    (hc : Nat.card (B ⧸ pCore 2 B) = Nat.card (H ⧸ pCore 2 H)) :
    Function.Surjective ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hBH)) := by
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hBH)
  apply MonoidHom.range_eq_top.mp
  apply eq_top_of_le_card
  rw [← hc, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv]
  exact index_antitone (restriction_core_le hBH)

theorem core_adjustment (hBH : B ≤ H)
    (hc : Nat.card (B ⧸ pCore 2 B) = Nat.card (H ⧸ pCore 2 H))
    (s : G) (hsH : s ∈ H) (hsB : s ∈ normalizer (B : Set G)) :
    ∃ b : B, ∀ x : B,
      b⁻¹ * B.normalizerMonoidHom ⟨s, hsB⟩ x * b * x⁻¹ ∈ pCore 2 B := by
  let q := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hBH)
  obtain ⟨b, hb⟩ := core_projection_surjective hBH hc
    (QuotientGroup.mk' (pCore 2 H) ⟨s, hsH⟩)
  refine ⟨b, fun x => restriction_core_le hBH ?_⟩
  change q (b⁻¹ * B.normalizerMonoidHom ⟨s, hsB⟩ x * b * x⁻¹) = 1
  have hx : q (B.normalizerMonoidHom ⟨s, hsB⟩ x) =
      QuotientGroup.mk' (pCore 2 H) ⟨s, hsH⟩ * q x *
        (QuotientGroup.mk' (pCore 2 H) ⟨s, hsH⟩)⁻¹ := by
    change QuotientGroup.mk' (pCore 2 H)
      ((⟨s, hsH⟩ : H) * inclusion hBH x * (⟨s, hsH⟩ : H)⁻¹) = _
    simp only [map_mul, map_inv]
    rfl
  simp only [map_mul, map_inv, hx]
  change q b = _ at hb
  rw [hb]
  group

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FiveParabolics.DiagramAction
end
