module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ChapterThreeSylow
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceMovement

/-!
# The reduced-module branch of the genuine qrc bound

Apply the complete E.2.3 classification to any actual reduced H-module
moved by J(T). Its Baumann Sylow alternatives, including exchanged A₅
factors, put the original O₂(M₀) in Syl₂(O²(H)O₂(M₀)). For the unique
noncentral chief-factor branch, the residual commutator module supplies
this input. The genuine common-normal theorem contradicts uniqueness
of the original maximal two-local overgroup.
Source: Aschbacher--Smith 3.1.6, printed pp.573--575.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The residual Sylow argument on any actual reduced module moved by J(T). -/
theorem QrcHypotheses.residual_sylow_of_reduced_module
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (U : Subgroup H) (hU : IsPReduced 2 U)
    (hj : ¬ elementaryAbelianMaxJ
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤ centralizer (U : Set H)) :
    Chapter1.IsSylowIn 2 (M₀.pCoreIn 2)
      ((pResidual 2 H).map H.subtype ⊔ M₀.pCoreIn 2) := by
  have hsq := sqtk_of_mem_H hG h.right_mem.1.1.1
  have hp := h.intrinsic_minimalParabolic hM hu hJ
  let S := T.subtype h.right_mem.1.1.2
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



namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}
/-- The unique-factor centralizing-closure branch contradicts the original local uniqueness. -/
theorem QrcHypotheses.not_uniqueFactor_coreClosure_centralizes
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hV : V ≤ twoCoreIn H) (hu : HasUniqueNoncentralChiefFactor H V) :
    ¬ intersectionClosure M₀ H ≤ centralizer (V : Set G) := by
  intro hc
  let d := h.toQRCConfiguration (h.no_common_normal huniq)
  let I := ⁅conjugateSpan H V,(pResidual 2 H).map H.subtype⁆
  have hIH : I ≤ H := (residual_module_le_span d).trans
    ((span_le_right_core d hV).trans (twoCore_le H))
  have hJI : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (I : Set G) := by
    intro hj
    apply source_thompson_moves_residual_module d hV hu hc
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ twoCoreIn M₀ := by
      rw [show twoCoreIn M₀ = M₀.pCoreIn 2 from rfl, h.core_eq_centralizer]
      exact le_inf hJT hJ
    have he := elementaryAbelianMaxJ_eq_of_intermediate_finite
      (T : Subgroup G) (twoCoreIn M₀) hJR (left_core_le_sylow d)
    exact he ▸ hj
  have hj : ¬ elementaryAbelianMaxJ
      ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) ≤
      centralizer (I.subgroupOf H : Set H) := by
    intro hj
    apply hJI
    have hjmap : (elementaryAbelianMaxJ
        ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le h.right_mem.1.1.2
    rw [← hjmap]
    rintro g ⟨j,hjJ,rfl⟩ z hz
    exact congrArg H.subtype (hj hjJ ⟨z,hIH hz⟩ hz)
  have hRne : M₀.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact module_ne_bot hu (bot_unique (d.module_le_core.trans he.le))
  exact h.not_residual_sylow (source_common_normal_knownSimple hG T) hRne huniq
    (h.residual_sylow_of_reduced_module hG hM huniq hJ (I.subgroupOf H)
      (source_residual_module_reduced d hV hu hc) hj)
end CFSG.Quasithin.Chapter3


