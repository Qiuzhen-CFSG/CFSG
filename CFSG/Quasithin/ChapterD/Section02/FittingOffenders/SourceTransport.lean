module
public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Theory.Representation.BinaryOffender.CubicSection
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
/-!
# Minimal cubic actors on the literal generated action

Passing a starred actor to an overgroup preserves its global minimum among
that overgroup's actors. Removing a pointwise fixed complementary summand
preserves every cubic condition and action ratio, hence starred minimality.
Both statements retain the actual subgroup and restricted representation.

Source: Aschbacher–Smith D.2.14, restriction to PA on [V,P], printed p.187.
-/

public section
namespace CFSG.Quasithin.ChapterD.SourceReduction
open Subgroup Representation.BinaryOffender
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem starred_subgroupOf {A H : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hAH : A ≤ H) : A.subgroupOf H ∈ QhatStar (ρ.comp H.subtype) := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hmap : (A.subgroupOf H).map H.subtype = A := map_subgroupOf_eq_of_le hAH
  have hel : IsElementaryTwo (A.subgroupOf H) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAH⟩
    intro hb
    exact hA.1.2.1.1 (by rw [← hmap, hb, Subgroup.map_bot])
  have hr (B : Subgroup H) : actionRatio (ρ.comp H.subtype) B =
      actionRatio ρ (B.map H.subtype) := by
    rw [actionRatio, actionRatio, rank_map_injective H.subtype H.subtype_injective]
    congr 1
    unfold fixedCodim
    rw [fixedSpace_comp_map ρ H.subtype B]
  have hc : IsCubic (ρ.comp H.subtype) (A.subgroupOf H) := by
    intro a ha b hb c hc v
    exact hA.1.2.2.1 a ha b hb c hc v
  have hlo : cubicRatio ρ ≤ cubicRatio (ρ.comp H.subtype) := by
    refine le_iInf fun B => le_iInf fun hB => ?_
    let : IsElementaryAbelian 2 B := hB.1.2
    have hBn : B.map H.subtype ≠ ⊥ := by
      intro hb
      apply hB.1.1
      exact (map_injective H.subtype_injective) (by simpa only [Subgroup.map_bot] using hb)
    rw [hr]
    exact iInf_le_of_le _ (iInf_le_of_le
      ⟨⟨hBn, IsElementaryAbelian.map H.subtype⟩,
        hB.2.map_equivariant (ρ.comp H.subtype) ρ H.subtype
          (LinearEquiv.refl _ _) (fun _ _ => rfl)⟩ le_rfl)
  have he : cubicRatio (ρ.comp H.subtype) = cubicRatio ρ := by
    apply le_antisymm _ hlo
    apply (show cubicRatio (ρ.comp H.subtype) ≤ actionRatio (ρ.comp H.subtype) (A.subgroupOf H) from
      iInf_le_of_le _ (iInf_le_of_le ⟨hel, hc⟩ le_rfl)).trans
    rw [hr, hmap, hA.1.2.2.2]
  refine ⟨⟨he ▸ hA.1.1, hel, hc, ?_⟩, ?_⟩
  · rw [hr, hmap, hA.1.2.2.2, he]
  · intro B hB hBA
    apply map_injective H.subtype_injective
    rw [hmap]
    let : IsElementaryAbelian 2 B := hB.2.1.2
    apply hA.2 (B.map H.subtype) ?_ (hmap ▸ map_mono hBA)
    refine ⟨hA.1.1, ⟨?_, IsElementaryAbelian.map H.subtype⟩, ?_, ?_⟩
    · intro hb
      exact hB.2.1.1 ((map_injective H.subtype_injective) (by simpa only [Subgroup.map_bot] using hb))
    · exact hB.2.2.1.map_equivariant (ρ.comp H.subtype) ρ H.subtype
        (LinearEquiv.refl _ _) (fun _ _ => rfl)
    · rw [← hr, hB.2.2.2, he]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem cubic_fixed_complement_iff (W : Subrepresentation ρ)
    (hs : W.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤) (B : Subgroup G) :
    IsCubic W.toRepresentation B ↔ IsCubic ρ B := by
  constructor
  · intro h a ha b hb c hc v
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W.toSubmodule ⊔ fixedSpace ρ ⊤ from hs ▸ Submodule.mem_top)
    have hw0 : displacement ρ a (displacement ρ b (displacement ρ c w)) = 0 :=
      congrArg Subtype.val (h a ha b hb c hc ⟨w, hw⟩)
    have hz0 : displacement ρ c z = 0 := sub_eq_zero.mpr (hz ⟨c, mem_top c⟩)
    simp only [map_add, hw0, hz0, add_zero]
  · exact cubic_subrepresentation ρ W

omit [Finite G] in
theorem fixed_complement_starred (W : Subrepresentation ρ)
    (hs : W.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) : A ∈ QhatStar W.toRepresentation := by
  have hc (B : Subgroup G) : fixedCodim W.toRepresentation B = fixedCodim ρ B := by
    apply (fixedCodim_subrepresentation_eq_iff ρ W B).mpr
    apply top_unique
    rw [← hs]
    exact sup_le_sup_left (fixedSpace_antitone ρ le_top) _
  have hr (B : Subgroup G) : actionRatio W.toRepresentation B = actionRatio ρ B := by
    rw [actionRatio, actionRatio, hc]
  have he : cubicRatio W.toRepresentation = cubicRatio ρ := by
    unfold cubicRatio
    apply iInf_congr
    intro B
    rw [cubic_fixed_complement_iff ρ W hs B, hr]
  refine ⟨⟨he ▸ hA.1.1, hA.1.2.1,
    (cubic_fixed_complement_iff ρ W hs A).mpr hA.1.2.2.1, ?_⟩, ?_⟩
  · rw [hr, he, hA.1.2.2.2]
  · intro B hB hBA
    apply hA.2 B ?_ hBA
    exact ⟨hA.1.1, hB.2.1, (cubic_fixed_complement_iff ρ W hs B).mp hB.2.2.1,
      (hr B).symm.trans (hB.2.2.2.trans he)⟩

end CFSG.Quasithin.ChapterD.SourceReduction
