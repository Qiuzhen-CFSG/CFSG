module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.QuotientActions
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Relative generation and comparison of star images

Normal generation is restricted to the actual local overgroup before using
normality. Equality in H/O₂(H) gives equality after adjoining O₂(H).
After quotienting by the central line, that supplement centralizes the seed,
so the two commutator images agree. Lifting gives the commutator bound used
in 13.8.9–11; it is proved here rather than assumed from equal star images.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.9–11,
printed pp.949–950. The core commutator bound is the earlier F.9.2 input.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G]

theorem conjugateSpan_eq_map_normalClosure (F J : Subgroup G) (hFJ : F ≤ J) :
    conjugateSpanBy F J = (normalClosure (F.subgroupOf J : Set J)).map J.subtype := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨j, hj, f, hf, rfl⟩
    exact ⟨(⟨j, hj⟩ : J) * ⟨f, hFJ hf⟩ * (⟨j, hj⟩ : J)⁻¹,
      (normalClosure_normal (s := (F.subgroupOf J : Set J))).conj_mem _
        (le_normalClosure hf) _, rfl⟩
  · apply map_le_iff_le_comap.mpr
    change normalClosure (F.subgroupOf J : Set J) ≤ (conjugateSpanBy F J).subgroupOf J
    let _ : ((conjugateSpanBy F J).subgroupOf J).Normal :=
      normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy F J)
    exact normalClosure_le_normal (fun _ hf => le_conjugateSpanBy F J hf)

theorem noncentral_of_relative_generation
    (J F E W V U : Subgroup G) (hFJ : F ≤ J) (hWJ : W ≤ J)
    (hJU : J ≤ normalizer (U : Set G))
    (hV : V = conjugateSpanBy W J)
    (hgen : J = conjugateSpanBy F J ⊔ E)
    (hEW : ⁅E, W⁆ ≤ U) (hnoncentral : ¬ ⁅J, V⁆ ≤ U) :
    ¬ ⁅F, V⁆ ≤ U := by
  have hVJ : V ≤ J := hV.le.trans (conjugateSpanBy_le_self hWJ)
  have hEJ : E ≤ J := le_sup_right.trans hgen.symm.le
  let _ : (U.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJU
  have hV' : V.subgroupOf J = normalClosure (W.subgroupOf J : Set J) := by
    apply (map_injective J.subtype_injective)
    rw [map_subgroupOf_eq_of_le hVJ, ← conjugateSpan_eq_map_normalClosure W J hWJ, hV]
  have hgen' : normalClosure (F.subgroupOf J : Set J) ⊔ E.subgroupOf J = ⊤ := by
    apply (map_injective J.subtype_injective)
    rw [Subgroup.map_sup, ← conjugateSpan_eq_map_normalClosure F J hFJ,
      map_subgroupOf_eq_of_le hEJ, ← hgen, ← MonoidHom.range_eq_map, J.range_subtype]
  intro hFV
  have hEW' : ⁅E.subgroupOf J, W.subgroupOf J⁆ ≤ U.subgroupOf J := by
    apply map_le_iff_le_comap.mp
    rwa [map_commutator, map_subgroupOf_eq_of_le hEJ, map_subgroupOf_eq_of_le hWJ]
  have hFV' : ⁅F.subgroupOf J, V.subgroupOf J⁆ ≤ U.subgroupOf J := by
    apply map_le_iff_le_comap.mp
    rwa [map_commutator, map_subgroupOf_eq_of_le hFJ, map_subgroupOf_eq_of_le hVJ]
  have hc := commutator_le_of_normal_generation (F.subgroupOf J) (E.subgroupOf J)
    (W.subgroupOf J) (V.subgroupOf J) (U.subgroupOf J) hV' hgen' hFV' hEW'
  have hm := (map_le_iff_le_comap.mpr hc)
  rw [map_commutator, ← MonoidHom.range_eq_map, J.range_subtype, map_subgroupOf_eq_of_le hVJ] at hm
  exact hnoncentral hm

theorem commutator_bound_of_quotient_images
    (F U V Z : Subgroup G) [Z.Normal]
    (h : ⁅F, V⁆.map (QuotientGroup.mk' Z) = ⁅F, U⁆.map (QuotientGroup.mk' Z)) :
    ⁅F, V⁆ ≤ ⁅F, U⁆ ⊔ Z := by
  have hc := congrArg (fun A => A.comap (QuotientGroup.mk' Z)) h
  simp only [comap_map_eq, QuotientGroup.ker_mk'] at hc
  exact le_sup_left.trans hc.le

theorem commutator_bound_of_same_core_image
    (F U V Q Z : Subgroup G) [Q.Normal] [Z.Normal]
    (hUV : U ≤ V) (hVF : V ≤ normalizer (F : Set G))
    (hFQ : ⁅F, Q⁆ ≤ Z)
    (himage : U.map (QuotientGroup.mk' Q) = V.map (QuotientGroup.mk' Q)) :
    ⁅F, V⁆ ≤ ⁅F, U⁆ ⊔ Z := by
  let q := QuotientGroup.mk' Z
  have hs : Q ⊔ U = Q ⊔ V := by
    have hc := congrArg (fun A => A.comap (QuotientGroup.mk' Q)) himage
    simpa only [comap_map_eq, QuotientGroup.ker_mk', sup_comm] using hc
  have hC : Q.map q ≤ centralizer (F.map q : Set (G ⧸ Z)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator, commutator_comm]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hFQ)
  have hN : V.map q ≤ normalizer (F.map q : Set (G ⧸ Z)) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [← map_commutator]
    exact map_mono (le_normalizer_iff_commutator_le_left.mp hVF)
  apply commutator_bound_of_quotient_images
  rw [map_commutator, map_commutator]
  have h1 := commutator_eq_of_centralizing_sup rfl hC hN
  have h2 := commutator_eq_of_centralizing_sup rfl hC ((map_mono hUV).trans hN)
  have hm := congrArg (Subgroup.map q) hs
  rw [Subgroup.map_sup, Subgroup.map_sup] at hm
  exact h1.trans (hm ▸ h2.symm)

theorem commutator_bound_of_equal_starImage
    (H F U V Z : Subgroup G)
    (hFH : F ≤ H) (hVH : V ≤ H) (hZH : Z ≤ H)
    (hZN : H ≤ normalizer (Z : Set G))
    (hUV : U ≤ V) (hVF : V ≤ normalizer (F : Set G))
    (hFQ : ⁅F, Source.QH H⁆ ≤ Z)
    (himage : Source.starImage H U = Source.starImage H V) :
    ⁅F, V⁆ ≤ ⁅F, U⁆ ⊔ Z := by
  let _ : (Z.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hZN
  have hUH := hUV.trans hVH
  have hN : V.subgroupOf H ≤ normalizer (F.subgroupOf H : Set H) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hFH, map_subgroupOf_eq_of_le hVH]
    exact le_normalizer_iff_commutator_le_left.mp hVF
  have hQ : ⁅F.subgroupOf H, pCore 2 H⁆ ≤ Z.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hFH]
    exact hFQ
  have hh := commutator_bound_of_same_core_image (F.subgroupOf H)
    (U.subgroupOf H) (V.subgroupOf H) (pCore 2 H) (Z.subgroupOf H)
    (subgroupOf_mono H hUV) hN hQ himage
  have hm := map_mono (f := H.subtype) hh
  rwa [map_commutator, Subgroup.map_sup, map_commutator,
    map_subgroupOf_eq_of_le hFH, map_subgroupOf_eq_of_le hUH,
    map_subgroupOf_eq_of_le hVH, map_subgroupOf_eq_of_le hZH] at hm

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry
end
