module

public import CFSG.Quasithin.ChapterJ.Section04To05.CubicLift.Quotient

/-!
# Sylow selection above the original J.4.4 complement

For the normal preimage A supplied by J.4.4(2), its containment in R₂ lets the
original S₃ quotient factor through G₂/A. The original Q₅ image has order two
and is outside R₂/A. The elementary inverted-three lift therefore selects an
actual Sylow three-subgroup X of G₂ such that Q₅ normalizes XA, with quotient S₃.

The three hypotheses on A are precisely the preceding complement construction;
the source assembly supplies them without changing the selected B₅ or maps.
Source: Aschbacher–Smith, J.4.4(5), printed p.441.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The original Q₅ has nontrivial image in G₂/R₂. -/
theorem Plane.Q₅_not_le_R₂ (B5 : Sylow 5 d.toTypeRuSetup.H) : ¬ Q₅ d B5 ≤ p.R₂ := by
  intro h
  have he : p.R₂ = (d.T : Subgroup G) := by
    simpa only [sup_eq_left.mpr h] using p.R₂_sup_Q₅ B5
  have hc := p.card_R₂
  rw [he,d.toTypeRuSetup.card_T_of_card_Z d.card_Z] at hc
  omega

/-- Literal Sylow selection modulo the complement from the preceding source lemma. -/
theorem Plane.exists_sylow_three_modulo
    (B5 : Sylow 5 d.toTypeRuSetup.H) (A : Subgroup G)
    [hn : (A.subgroupOf p.parabolic).Normal]
    (hAR : A ≤ p.R₂)
    (hB : Nat.card ((Q₅ d B5).subgroupOf p.parabolic |>.map
      (QuotientGroup.mk' (A.subgroupOf p.parabolic))) = 2) :
    ∃ X : Sylow 3 p.parabolic,
      (Q₅ d B5).subgroupOf p.parabolic ≤
        normalizer (((X : Subgroup p.parabolic) ⊔ A.subgroupOf p.parabolic : Subgroup p.parabolic) : Set p.parabolic) ∧
      Nonempty (((((Q₅ d B5).subgroupOf p.parabolic ⊔ (X : Subgroup p.parabolic)) ⊔
        A.subgroupOf p.parabolic).map (QuotientGroup.mk' (A.subgroupOf p.parabolic))) ≃*
          Equiv.Perm (Fin 3)) := by
  let q := QuotientGroup.mk' (A.subgroupOf p.parabolic)
  have hker : A.subgroupOf p.parabolic ≤ p.cubicMap.ker := by
    rw [p.cubicMap_kernel]
    exact comap_mono hAR
  let f := QuotientGroup.lift (A.subgroupOf p.parabolic) p.cubicMap hker
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨x,hx⟩ := p.cubicMap_surjective a
    exact ⟨q x,hx⟩
  have himage : (((Q₅ d B5).subgroupOf p.parabolic).map q).map f ≠ ⊥ := by
    intro he
    apply p.Q₅_not_le_R₂ B5
    intro x hx
    have hQ : Q₅ d B5 ≤ (d.T : Subgroup G) := (p.R₂_sup_Q₅ B5) ▸ le_sup_right
    have hxP : x ∈ p.parabolic := p.sylow_le_parabolic (hQ hx)
    have hm := mem_map_of_mem f (mem_map_of_mem q
      (show (⟨x,hxP⟩ : p.parabolic) ∈ (Q₅ d B5).subgroupOf p.parabolic from hx))
    rw [he,mem_bot] at hm
    have hkx : (⟨x,hxP⟩ : p.parabolic) ∈ p.cubicMap.ker := hm
    rwa [p.cubicMap_kernel] at hkx
  obtain ⟨X,hnorm,hmodel⟩ := exists_sylow_three_normalized_preimage q
    (QuotientGroup.mk'_surjective _) p.card_sylow_three f hsurj
    ((Q₅ d B5).subgroupOf p.parabolic) hB himage
  have hqker : q.ker = A.subgroupOf p.parabolic := QuotientGroup.ker_mk' _
  rw [hqker] at hnorm hmodel
  exact ⟨X,hnorm,hmodel⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
