module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveSylowTransport
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ChapterThreeSource

/-!
# The original residual-Sylow conclusion in3.1.7

Apply the complete E.2.3 action classification to the actual reduced orbit
of the Sylow omega-center in H. The linear and single symmetric-five
branches use their proved Baumann transport. In the paired branch, the
original qrc normalizer supplies the common Sylow container, and the actual
T-invariance of O₂(M₀) lets the exchanging-factor transport aggregate the
two componentwise extensions. All maps retain the original H and O₂(M₀).

Source: Aschbacher–Smith 3.1.7, printed pp.575–576.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The original residual Sylow assertion in3.1.7, with all E.2.3 branches
discharged on the literal Sylow omega-center orbit in H. -/
theorem QrcHypotheses.residual_sylow_source
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype) :
    Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  obtain ⟨hsq,_,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  let S := T.subtype h.right_mem.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let := hU.normal
  let := hU.elementary
  rcases ChapterE.ThompsonAction.source_sylow_or_paired_five hsq S hp U hU hj with hs | hpair
  · rcases hs with hs | ⟨S₁,hs,hbs,_,hspan⟩
    · exact h.residual_sylow_of_baumann_sylow hJ hs
    · exact h.residual_sylow_of_baumann_span hJ hp S₁ hs hbs hspan
  obtain ⟨d,t,h₁,h₂,⟨c⟩⟩ := hpair
  obtain ⟨D,hn,hR⟩ := h.exists_normal_sylow_container_in_right
  let R := (M₀.pCoreIn 2).subgroupOf H
  have hRT : M₀.pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [h.core_eq_centralizer]
    exact inf_le_left
  have hRS : R ≤ S := fun x hx => hRT hx
  have hnR : M₀ ≤ normalizer (M₀.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 M₀).le_normalizer_map M₀.subtype
  have hSR : (S : Subgroup H) ≤ normalizer (R : Set H) := by
    apply le_trans _ (le_normalizer_comap H.subtype)
    intro x hx
    exact (h.sylow_le.trans hnR) hx
  have hbmap : (ChapterB.baumann (S : Subgroup H)).map H.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    have he := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (ChapterB.baumann (S : Subgroup H)).map H.subtype =
      ChapterB.baumann ((S : Subgroup H).map H.subtype) at he
    have hm : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
    exact he.trans (congrArg ChapterB.baumann hm)
  have hBR : ChapterB.baumann (S : Subgroup H) ≤ R := by
    intro x hx
    exact (h.baumann_core hJ).2 (hbmap ▸ mem_map_of_mem H.subtype hx)
  have hn' : ChapterB.minimalParabolicMax S hp ≤ normalizer (D : Set H) := by
    rw [h.intrinsic_maximal_eq_intersection hp]
    exact hn
  have hs := ChapterE.ThompsonAction.paired_symmetric_residual_sylow_of_container
    S hp U hU hj _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    d c ⟨t,h₁,h₂⟩ D R hRS hSR hBR hR hn'
  have hm := (Chapter1.IsSylowIn.map_iff H.subtype H.subtype_injective).mpr hs
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le (hRT.trans h.right_mem.1.1.2)] at hm
end CFSG.Quasithin.Chapter3
