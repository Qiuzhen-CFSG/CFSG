module
public import CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape.Core
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.Configurations
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.NormalityReduction
public import Theory.GroupTheory.CComponent.ContainedGeneralizedFitting

/-!
# Component placement in the ambient contained branch

The reciprocal core containment puts O₂(L) inside the selected H. The
covering equation then gives L=(L∩H)^∞. Relative normality and A.4.4's core
equality place the local component core in O₂(H), promoting the same subgroup
to an ambient C-component. The C.2.12 normalizer identity and the genuine
component orbit theorem give index two, without assuming normality in H.

Source: Aschbacher--Smith, 4.2.6--7, printed p.609, using C.2.13.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
open Chapter1.RadicalExclusions
variable {G : Type*} [Group G] [Finite G]

/-- In the ambient contained branch the intersection residual is the original L. -/
theorem residual_eq_of_fitting_contained {L H M : Subgroup G}
    [Group.IsPerfect L] (hLM : L ≤ M) (hML : M ≤ normalizer (L : Set G))
    (hH : IsMaximalTwoLocal H) (hM : IsMaximalTwoLocal M)
    (hs : IsSQTK KnownSimple.IsKnownSimple M) (hne : H ≠ M)
    (hcover : (L : Set G) =
      (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) : Set G) *
        (L.pCoreIn 2 : Set G))
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype = L := by
  have hQ := (pCoreIn_mono_of_normalizes hLM hML).trans
    (reciprocal_setup hH hM hs hne hf).2.2.1
  have hLH : L ≤ H := by
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := hcover ▸ (show x ∈ (L : Set G) from hx)
    exact H.mul_mem ((map_subtype_le _ hy).2) ((pCoreIn_le 2 H) (hQ hz))
  rw [inf_eq_left.mpr hLH,solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype]

/-- The normalized source residual is an ambient C-component in the contrary branch. -/
theorem component_of_fitting_contained {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ M) B R W)
    (hn : ((B.subgroupOf (H ⊓ M))).Normal)
    [IsQuasisimple (B ⧸ pCore 2 B)]
    (hc : H.pCoreIn 2 = (H ⊓ M).pCoreIn 2)
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    (B.subgroupOf H).IsCComponent := by
  have hBH := h.component_le.trans inf_le_left
  have hNB : H ⊓ M ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hn
  let A := B.subgroupOf H
  let N := (H ⊓ M).subgroupOf H
  let e : A ≃* B := subgroupOfEquivOfLe hBH
  have hspan : conjugateSpanBy B (H ⊓ M) = B := le_antisymm
    (conjugateSpanBy_le le_rfl hNB) (le_conjugateSpanBy _ _)
  let : Group.IsPerfect B := hspan ▸ h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsQuasisimple (A ⧸ pCore 2 A) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hNF : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ N := fun x hx => ⟨x.property,hf hx⟩
  have hQN : pCore 2 H ≤ N := by
    intro x hx
    apply hNF
    change QuotientGroup.mk' (pCore 2 H) x ∈ generalizedFitting (H ⧸ pCore 2 H)
    have he : QuotientGroup.mk' (pCore 2 H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [he]
    exact one_mem _
  have hcore : A.pCoreIn 2 ≤ pCore 2 H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hBH]
    change B.pCoreIn 2 ≤ H.pCoreIn 2
    rw [hc]
    exact pCoreIn_mono_of_normalizes h.component_le hNB
  apply isCComponent_of_contained_generalizedFitting A N (comap_mono h.component_le)
  · rw [←subgroupOf_normalizer_eq hBH]
    exact comap_mono hNB
  · exact hQN
  · exact (map_mono (f := A.subtype) (commutator_le_left (pCore 2 A) ⊤)).trans hcore
  · exact hNF

/-- C.2.13's index-two conclusion for the literal ambient contrary branch. -/
theorem index_two_of_fitting_contained {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ M) B R W)
    (hn : (B.subgroupOf (H ⊓ M)).Normal)
    [IsQuasisimple (B ⧸ pCore 2 B)] (hstrict : H ⊓ M < H)
    (hc : H.pCoreIn 2 = (H ⊓ M).pCoreIn 2)
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    (B.subgroupOf H).IsCComponent ∧
      normalizer (B.subgroupOf H : Set H) = M.subgroupOf H ∧
      (M.subgroupOf H).index = 2 := by
  have hb := component_of_fitting_contained h hn hc hf
  have hBH := h.component_le.trans inf_le_left
  have hspan := h.span_eq_of_ambient_component hstrict hb
  have he : normalizer (B.subgroupOf H : Set H) = M.subgroupOf H := by
    rw [←subgroupOf_normalizer_eq hBH]
    have hh := h.normalizer_span_eq
    rw [hspan] at hh
    ext x
    exact ⟨fun hx => (show (x : G) ∈ H ⊓ M from hh ▸ ⟨x.property,hx⟩).2,
      fun hx => (show (x : G) ∈ H ⊓ normalizer (B : Set G) from hh.symm ▸ ⟨x.property,hx⟩).2⟩
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  refine ⟨hb,he,?_⟩
  rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hb with hnorm | hi
  · let := hnorm
    have ht : M.subgroupOf H = ⊤ := he.symm.trans (normalizer_eq_top _)
    exact (hstrict.not_ge (le_inf le_rfl (subgroupOf_eq_top.mp ht))).elim
  · exact he ▸ hi
end CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
