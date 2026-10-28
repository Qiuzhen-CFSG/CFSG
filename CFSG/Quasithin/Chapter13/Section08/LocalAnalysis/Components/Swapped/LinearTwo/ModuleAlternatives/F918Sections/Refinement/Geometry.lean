module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.MarkingTransport
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Reusing the marked product for every moving element

A factor-marked product makes both factors normal in their orbit. If the
orbit is normal in the actual ambient actor and its first factor is
quasisimple, every conjugate of that factor is one of the two factors.
The component normal-subgroup dichotomy proves this without classifying
any representation. Thus one supplied product marking reconstructs a
marking for whichever moving element occurs in F.9.18(5iii).

The statements retain relative normality inside K₀ and the source right
conjugation convention. They require no order-two condition on the mover.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(5),
printed pp.325–326, and proof of 13.8.16(1), p.952 (PDF p.969).
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open PairCoordinates
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement
@[expose] public noncomputable section
variable {D : Type*} [Group D] {K K₀ : Subgroup D} {t : D}

namespace Marking
variable (p : ProductMarking K K₀ t)
include p

theorem first_image : ((⊤ : Subgroup K).prod (⊥ : Subgroup K)).map p.product.toMonoidHom =
    K.subgroupOf K₀ := by
  ext g
  constructor
  · rintro ⟨⟨a,b⟩, ⟨_, hb⟩, rfl⟩
    change b = 1 at hb
    subst b
    change (p.product (a, 1) : D) ∈ K
    rw [p.first]
    exact a.property
  · intro hg
    refine ⟨(⟨g, hg⟩, 1), ⟨mem_top _, one_mem _⟩, ?_⟩
    exact Subtype.ext (p.first ⟨g, hg⟩)

theorem first_normal : (K.subgroupOf K₀).Normal := by
  rw [← first_image p]
  exact Subgroup.Normal.map inferInstance p.product.toMonoidHom p.product.surjective

theorem normalizes_first : K₀ ≤ normalizer (K : Set D) :=
  (normal_subgroupOf_iff_le_normalizer p.le).mp (first_normal p)

theorem second_normal : ((K.conjBy t⁻¹).subgroupOf K₀).Normal := by
  rw [← p.firstProjection_ker]
  infer_instance

theorem join_eq : K ⊔ K.conjBy t⁻¹ = K₀ := by
  apply le_antisymm (sup_le p.le p.conjugate_le)
  intro g hg
  obtain ⟨⟨a,b⟩, he⟩ := p.product.surjective ⟨g,hg⟩
  have he' := congrArg Subtype.val he
  rw [p.product_coe] at he'
  change (a : D) * (t⁻¹ * b * t) = g at he'
  rw [← he']
  exact mul_mem_sup a.property ⟨b, b.property, by simp⟩

theorem disjoint : Disjoint K (K.conjBy t⁻¹) := by
  rw [disjoint_iff_inf_le]
  intro g hg
  have he : p.firstProjection ⟨g, p.le hg.1⟩ = 1 := by
    apply (show _ ∈ p.firstProjection.ker → _ from id)
    rw [p.firstProjection_ker]
    exact hg.2
  change p.firstProjection ⟨(⟨g, hg.1⟩ : K), p.le hg.1⟩ = 1 at he
  rw [p.firstProjection_inclusion] at he
  exact mem_bot.mpr (congrArg Subtype.val he)

theorem commuting : K ≤ centralizer (K.conjBy t⁻¹ : Set D) := by
  intro a ha b hb
  obtain ⟨b, hb, rfl⟩ := hb
  have he : p.product ((⟨a,ha⟩,1) * (1,⟨b,hb⟩)) =
      p.product ((1,⟨b,hb⟩) * (⟨a,ha⟩,1)) := by congr 1; simp
  have hh := congrArg Subtype.val he
  change t⁻¹ * b * (t⁻¹)⁻¹ * a = a * (t⁻¹ * b * (t⁻¹)⁻¹)
  simpa only [map_mul, Subgroup.coe_mul, p.first, p.second, inv_inv] using hh.symm

theorem component [K₀.Normal] [IsQuasisimple K] : IsComponent D K :=
  ⟨Subgroup.IsSubnormal.trans p.le (first_normal p).isSubnormal
    (inferInstance : K₀.Normal).isSubnormal, inferInstance⟩

omit p in
/-- A quasisimple component in a product of normal factors lies in a factor. -/
private theorem component_le_factor {A B L : Subgroup D}
    [A.Normal] [B.Normal] (hL : IsComponent D L) (hAB : A ⊔ B = ⊤) :
    L ≤ A ∨ L ≤ B := by
  rcases hL.normal_dichotomy A with h | ha
  · exact Or.inl h
  rcases hL.normal_dichotomy B with h | hb
  · exact Or.inr h
  have hc : L ≤ center D := by
    have h := sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
    rw [hAB] at h
    intro l hl
    exact mem_center_iff.mpr (fun g => (h (mem_top g) l hl).symm)
  have hz : ⁅L,L⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hc le_top).trans (commutator_center_left ⊤).le)
  let := hL.2
  rw [commutator_eq_self] at hz
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  have : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact ((nontrivial_iff_ne_bot L).mp inferInstance hz).elim

theorem conjugate_eq_or [K₀.Normal] [IsQuasisimple K] (s : D) :
    K.conjBy s = K ∨ K.conjBy s = K.conjBy t⁻¹ := by
  have hL := (component p).map_conj s
  have hle : K.conjBy s ≤ K₀ := by
    rintro _ ⟨k,hk,rfl⟩
    exact (inferInstance : K₀.Normal).conj_mem k (p.le hk) s
  let := first_normal p
  let := second_normal p
  have hjoin : K.subgroupOf K₀ ⊔ (K.conjBy t⁻¹).subgroupOf K₀ = ⊤ := by
    rw [← subgroupOf_sup p.le p.conjugate_le, join_eq p, subgroupOf_self]
  rcases component_le_factor (hL.subgroupOf hle) hjoin with h | h
  · left
    apply hL.eq_of_le (component p)
    intro k hk
    exact h (show (⟨k, hle hk⟩ : K₀) ∈ (K.conjBy s).subgroupOf K₀ from hk)
  · right
    apply hL.eq_of_le ((component p).map_conj t⁻¹)
    intro k hk
    exact h (show (⟨k, hle hk⟩ : K₀) ∈ (K.conjBy s).subgroupOf K₀ from hk)

theorem conjugate_eq [K₀.Normal] [IsQuasisimple K] {s : D}
    (hs : s ∉ normalizer (K : Set D)) : K.conjBy s = K.conjBy t⁻¹ := by
  rcases conjugate_eq_or p s with h | h
  · exact (hs (mem_normalizer_iff_map_conj_eq.mpr h)).elim
  · exact h

theorem remark [K₀.Normal] [IsQuasisimple K] {s : D}
    (hs : s ∉ normalizer (K : Set D)) : Nonempty (ProductMarking K K₀ s) := by
  have hsi : s⁻¹ ∉ normalizer (K : Set D) := fun h => hs (by simpa using (normalizer _).inv_mem h)
  have he := conjugate_eq p hsi
  apply productMarking_of_disjoint (by rw [normalizer_eq_top]; exact mem_top s)
  · rw [he]; exact join_eq p
  · rw [he]; exact disjoint p
  · rw [he]; exact commuting p
  · rw [he]; exact conjugate_eq p hs
end Marking
end
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.Refinement
