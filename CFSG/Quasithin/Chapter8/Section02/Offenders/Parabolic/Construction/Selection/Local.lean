module
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Preparation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Quotient
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import Theory.GroupTheory.PCoreRestriction

/-!
# Restriction to the selected two-conjugate group

The genuine HStar hypothesis supplies the unique maximal overgroup; simple
QTKE supplies SQTK. Relative normalization places V in the intrinsic
local two-core. B.6.8(5), left as its universal source input, then gives
E.2.8 from the independently proved noncontainment in O₂(H).

For a selected family member, its specified Sylow and generating pair give
all of E.2.10's hypotheses, including the core inclusion under restriction.
This proves E.2.11(1) with the inverse source conjugator. The normalizer
bound is proved directly from the unique maximal overgroup.
Source: Aschbacher–Smith, pp.221–224 and Proposition 8.2.2, pp.714–715.
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open Subgroup ChapterB ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- The E.2.9 normalizer assertion in the original ambient group. -/
theorem HypothesisE28.normalizer_le {K : GroupClass} {H T M V : Subgroup G}
    (h : HypothesisE28 K H T M V) : H ⊓ normalizer (V : Set G) ≤ M := by
  let := h.elementary
  have hVH := h.le_sylow.trans h.le_ambient
  obtain ⟨S, hS, hP, hM⟩ := h.minimal
  have hn : T ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow
  have hSN : (S : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [hS, ← subgroupOf_normalizer_eq hVH]
    exact comap_mono hn
  have hproper : normalizer (V.subgroupOf H : Set H) ≠ ⊤ := by
    intro he
    let _ : (V.subgroupOf H).Normal := normalizer_eq_top_iff.mp he
    have hVm : V.subgroupOf H ≤ M.subgroupOf H := by
      rw [hM]
      exact (show V.subgroupOf H ≤ S from hS ▸ comap_mono h.le_sylow).trans
        (minimalParabolicMax_spec S hP).2
    have hc : V.subgroupOf H ≤ localCore M H := normal_le_normalCore.mpr hVm
    have hm := map_mono (f := H.subtype) hc
    rw [map_subgroupOf_eq_of_le hVH] at hm
    exact h.outside_core hm
  have hN : normalizer (V.subgroupOf H : Set H) ≤ M.subgroupOf H := by
    rw [hM]
    have hm := minimalParabolicMax_spec S hP
    exact hP.1.le_maximal ⟨hm.2, hm.1.covBy_top⟩ hSN (lt_top_iff_ne_top.mpr hproper)
  rw [← subgroupOf_normalizer_eq hVH] at hN
  intro x hx
  exact hN (show (⟨x, hx.1⟩ : H) ∈ (normalizer (V : Set G)).subgroupOf H from hx.2)

/-- E.2.11(1), with the actual restricted Sylow and the source inverse conjugator. -/
theorem Family.twoConjugate {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    (h : HypothesisE28 K H T M V) (f : Family H T M V I k)
    (S : Sylow 2 I) (hS : (S : Subgroup I) = T.subgroupOf I)
    (i : I) (hi : V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I) :
    TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹ := by
  let := h.elementary
  have hVI : V ≤ I := hi ▸ le_sup_left
  have hVH := hVI.trans f.le_ambient
  have hNI : I ⊓ normalizer (V : Set G) ≤ M :=
    (inf_le_inf_right _ f.le_ambient).trans h.normalizer_le
  have hlocal : V.subgroupOf H ≤ (M.subgroupOf H).pCoreIn 2 := by
    intro v hv
    obtain ⟨x, hx, he⟩ := h.le_local_core hv
    refine ⟨x, hx, ?_⟩
    exact Subtype.ext he
  have hVM : V ≤ M := by
    intro v hv
    exact (pCoreIn_le 2 (M.subgroupOf H)) (hlocal (show (⟨v, hVH hv⟩ : H) ∈ V.subgroupOf H from hv))
  have hcore : V.subgroupOf I ≤ (pCore 2 (M.subgroupOf I)).map (M.subgroupOf I).subtype := by
    let j : M.subgroupOf I →* M.subgroupOf H :=
      { toFun := fun x => ⟨⟨x.val.val, f.le_ambient x.val.property⟩, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro x y he
      exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.val) he))
    have hc : (pCore 2 (M.subgroupOf H)).comap j ≤ pCore 2 (M.subgroupOf I) :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective j hj⟩
    intro v hv
    refine ⟨⟨v, hVM hv⟩, hc ?_, rfl⟩
    obtain ⟨x, hx, he⟩ := hlocal (show (⟨v.val, f.le_ambient v.property⟩ : H) ∈ V.subgroupOf H from hv)
    have he' : j ⟨v, hVM hv⟩ = x := Subtype.ext he.symm
    change j ⟨v, hVM hv⟩ ∈ pCore 2 (M.subgroupOf H)
    rwa [he']
  refine ⟨IsElementaryAbelian.subgroupOf hVI, ?_, ?_, ?_, hcore, f.core_two_closed, ?_⟩
  · rw [hS]
    exact comap_mono h.le_sylow
  · have hVS : V.subgroupOf I ≤ (S : Subgroup I) := by
      rw [hS]
      exact comap_mono h.le_sylow
    apply (normal_subgroupOf_iff_le_normalizer hVS).mpr
    rw [hS, ← subgroupOf_normalizer_eq hVI]
    exact comap_mono ((normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow)
  · rw [← subgroupOf_normalizer_eq hVI]
    intro x hx
    exact hNI ⟨x.property, hx⟩
  · apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hVI, restricted_right_conjugate_image I V hVI i,
      hi, ← MonoidHom.range_eq_map, range_subtype]

/-- The local E.2.8 setup from the actual HStar member, simple QTKE,
relative normalization in H ∩ M, and the independent 8.2.2(1) input.
The remaining universal core-closedness input is B.6.8(5). -/
theorem hypothesisE28_of_HStar {K : GroupClass} (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) {H M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hVT : V ≤ T) (hn : (V.subgroupOf (T : Subgroup G)).Normal)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hout : ¬ V ≤ (pCore 2 H).map H.subtype)
    (b685 : ∀ (D : Subgroup G) (S : Sylow 2 D)
      (hP : IsMinimalParabolicOver S ⊤), IsTwoClosed (minimalParabolicMax S hP).normalCore) :
    HypothesisE28 K H T M V := by
  have hTH := hH.1.1.2
  let S := T.subtype hTH
  have hS : (S : Subgroup H) = (T : Subgroup G).subgroupOf H := rfl
  have hmap : ((T : Subgroup G).subgroupOf H).map H.subtype = T :=
    map_subgroupOf_eq_of_le hTH
  obtain ⟨B, hB, hu⟩ := Chapter3.HStar.unique_maximal_subgroup T hTM hH
  have hSB : (S : Subgroup H) ≤ B := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    simpa only [hS, hmap] using hB.2
  have hP : IsMinimalParabolicOver S ⊤ := by
    apply (isMinimalParabolicOver_top_iff S).mpr
    refine ⟨⟨B, ⟨hB.1, hSB⟩, ?_⟩, ?_⟩
    · intro Y hY
      apply hu Y
      refine ⟨hY.1, ?_⟩
      have hy := map_mono (f := H.subtype) hY.2
      simpa only [hS, hmap] using hy
    · intro hs
      have hcore : (S : Subgroup H) ≤ pCore 2 H := le_sSup ⟨hs, S.isPGroup'⟩
      have hc := map_mono (f := H.subtype) hcore
      rw [hS, hmap] at hc
      exact hout (hVT.trans hc)
  have hMB : M.subgroupOf H = B := by
    have hBM : B ≤ M.subgroupOf H := by
      have hbH : B.map H.subtype < H := by
        have hb := (map_lt_map_iff_of_injective H.subtype_injective).mpr hB.1.lt_top
        simpa only [← MonoidHom.range_eq_map, range_subtype] using hb
      have hbM := Chapter3.HStar.proper_overgroup_le T hH hB.2 hbH
      intro x hx
      exact hbM (mem_map_of_mem H.subtype hx)
    have hnM : M.subgroupOf H ≠ ⊤ := by
      intro he
      apply hH.1.2
      intro x hx
      exact (show (⟨x, hx⟩ : H) ∈ M.subgroupOf H by rw [he]; trivial)
    exact (eq_of_le_of_not_lt hBM (fun hlt => hnM (hB.1.2 _ hlt))).symm
  have hM : M.subgroupOf H = minimalParabolicMax S hP :=
    hMB.trans (minimalParabolicMax_unique S hP hB.1 hSB)
  have hVH := hVT.trans hTH
  have hVM : V ≤ (pCore 2 (M.subgroupOf H)).map
      (H.subtype.comp (M.subgroupOf H).subtype) := by
    have hVm : V.subgroupOf H ≤ M.subgroupOf H := comap_mono (hVT.trans hTM)
    have hnorm : (M.subgroupOf H) ≤ normalizer (V.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hVH]
      intro x hx
      exact hMV ⟨x.property, hx⟩
    let _ : ((V.subgroupOf H).subgroupOf (M.subgroupOf H)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hVm).mpr hnorm
    have hc : (V.subgroupOf H).subgroupOf (M.subgroupOf H) ≤ pCore 2 (M.subgroupOf H) :=
      le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup 2 V).comap_subtype.comap_subtype⟩
    have hm := map_mono (f := H.subtype.comp (M.subgroupOf H).subtype) hc
    rwa [← map_map, map_subgroupOf_eq_of_le hVm, map_subgroupOf_eq_of_le hVH] at hm
  apply hypothesisE28_of_outside_twoCore K H T M V hTH S hS hP hM
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) hVT hn hVM
  · change IsTwoClosed (M.subgroupOf H).normalCore
    rw [hM]
    exact b685 H S hP
  · exact hout

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
