module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Recognized
public import Theory.Representation.NormalElementaryQuotient.SeedCore

/-!
# The actual seed stabilizer and its two-core in 15.1.28

The seed-centralizer equality identifies its centralizer in LQ1 with the
restriction of MZ. Normality of L in G1 makes its intrinsic two-core exactly
Q1. The faithful action kernel is a two-group, so this core identity descends
through the original centralizer quotient. The original C.2.7 best offender
then lies in the two-core of this same pointwise stabilizer after restriction
to the offender-generated group. The seed is fixed by the component Sylow
subgroup and is moved by the component, for both source plane sizes.

These are the source inputs to the homogeneous model eliminations. They do
not assert a parabolic identification or natural-module recognition.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original centralizer equality restricted to the actual LQ1 actor. -/
theorem exchanged_seed_centralizer_in_LQ1 (d : CaseIComponentData T M Mc V)
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    centralizer ((d.Z2 t).subgroupOf J : Set J) = d.MZ.subgroupOf J := by
  intro J
  have hJG : J ≤ d.G1 := sup_le d.L_component.1 (d.Q1_le_MZ.trans inf_le_left)
  have hZJ : d.Z2 t ≤ J := (le_conjugateSpanBy _ _).trans
    ((d.exchanged_U_le_Q1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht).trans le_sup_right)
  ext x
  constructor
  · intro hx
    apply d.exchanged_Z2_centralizer_le_MZ s.1 hM hu h t ht htS
    refine ⟨hJG x.property, ?_⟩
    intro z hz
    exact congrArg Subtype.val (hx ⟨z,hZJ hz⟩ hz)
  · intro hx z hz
    exact Subtype.ext (d.exchanged_MZ_le_centralizer_Z2 s.1 t ht hx z hz)

/-- Relative normality identifies the seed centralizer's intrinsic two-core. -/
theorem exchanged_seed_centralizer_core (d : CaseIComponentData T M Mc V)
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    (centralizer ((d.Z2 t).subgroupOf J : Set J)).pCoreIn 2 = d.Q1.subgroupOf J := by
  intro J
  let := s.1.quasisimple
  have hMQ : d.MZ ≤ normalizer (d.Q1 : Set G) :=
    d.MZ.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))
  have hMJ : d.MZ ≤ normalizer (J : Set G) :=
    (le_inf (inf_le_left.trans (d.G1_normalizes_L hG h s.cubicFacts)) hMQ).trans
      (normalizer_inf_normalizer_le_normalizer_sup d.L d.Q1)
  have hcore : (d.MZ ⊓ J).pCoreIn 2 = d.Q1 := by
    apply le_antisymm
    · exact pCoreIn_mono_of_normalizes inf_le_left
        ((le_inf d.MZ.le_normalizer hMJ).trans inf_normalizer_le_normalizer_inf)
    · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 d.MZ)
        (le_inf d.Q1_le_MZ le_sup_right) (inf_le_left.trans hMQ)
  rw [d.exchanged_seed_centralizer_in_LQ1 s hG hM hu h t ht htS]
  have he : d.MZ.subgroupOf J = (d.MZ ⊓ J).subgroupOf J := by
    ext x
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  rw [he,pCoreIn_subgroupOf 2 (d.MZ ⊓ J) J inf_le_right,hcore]

/-- The original LQ1 action kernel embeds in the known LS two-core. -/
theorem exchanged_U_quotient_kernel_isTwoGroup (d : CaseIComponentData T M Mc V)
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    IsPGroup 2 (centralizer ((d.U t).subgroupOf J : Set J)) := by
  intro J
  let D := d.L ⊔ d.S
  have hJD : J ≤ D := sup_le le_sup_left ((d.exchanged_Q1_le_S s.1 hu).trans le_sup_right)
  have hUJ : d.U t ≤ J :=
    (d.exchanged_U_le_Q1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht).trans le_sup_right
  have he := d.exchanged_U_LS_centralizer_eq_pCore s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht htS
  have hbound : centralizer ((d.U t).subgroupOf J : Set J) ≤
      (pCore 2 D).comap (inclusion hJD) := by
    intro x hx
    change (inclusion hJD x) ∈ pCore 2 D
    rw [← he]
    intro u huU
    apply Subtype.ext
    exact congrArg (fun x : J => (x : G)) (hx ⟨u,hUJ huU⟩ huU)
  exact (pCore_isPGroup.comap_of_injective (inclusion hJD) (inclusion_injective hJD)).to_le hbound

/-- The original exchanged seed as a subspace of the literal quotient module. -/
@[expose] noncomputable def exchangedSeedSpace (d : CaseIComponentData T M Mc V)
    (t : G) (J : Subgroup G) [IsElementaryAbelian 2 ((d.U t).subgroupOf J)] :
    Submodule (ZMod 2) (Additive ((d.U t).subgroupOf J)) :=
  NormalElementaryQuotient.subspace ((d.U t).subgroupOf J)
    (((d.Z2 t).subgroupOf J).subgroupOf ((d.U t).subgroupOf J))

/-- The literal seed stabilizer in the action quotient has exactly Q1's image
as its two-core. No geometric parabolic identification is assumed. -/
theorem HasExchangedLinearSource.seed_core_eq {d : CaseIComponentData T M Mc V}
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (subspaceKernel ρ (d.exchangedSeedSpace t J) ⊤).pCoreIn 2 =
      (d.Q1.subgroupOf J).map q := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ
  have hZW : (d.Z2 t).subgroupOf J ≤ W := comap_mono (le_conjugateSpanBy _ _)
  have hP : (((d.Z2 t).subgroupOf J).subgroupOf W).map W.subtype =
      (d.Z2 t).subgroupOf J := map_subgroupOf_eq_of_le hZW
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact d.exchanged_U_quotient_kernel_isTwoGroup s hG hM hu h t ht htS
  rw [exchangedSeedSpace, NormalElementaryQuotient.subspaceKernel_eq_map_centralizer,
    hP, ← map_pCoreIn_of_ker_isPGroup q hq,
    d.exchanged_seed_centralizer_core s hG hM hu h t ht htS]

/-- Every best offender supplied by the original Q1 remains a best offender
inside B and lies in the two-core of the same seed's pointwise stabilizer. -/
theorem HasExchangedLinearSource.best_offender_le_seed_core
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    ∀ A : Subgroup J, A ≤ d.Q1.subgroupOf J → IsBestOffender ρ (A.map q) →
      IsBestOffender (ρ.comp B.subtype) ((A.map q).subgroupOf B) ∧
        (A.map q).subgroupOf B ≤
          (subspaceKernel (ρ.comp B.subtype) (d.exchangedSeedSpace t J) ⊤).pCoreIn 2 := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B A hA hb
  refine ⟨hb.subgroupOf ρ (hb.le_offenderSubgroup ρ), ?_⟩
  have hZW : (d.Z2 t).subgroupOf J ≤ W := comap_mono (le_conjugateSpanBy _ _)
  have hP : (((d.Z2 t).subgroupOf J).subgroupOf W).map W.subtype =
      (d.Z2 t).subgroupOf J := map_subgroupOf_eq_of_le hZW
  have hC : centralizer ((((d.Z2 t).subgroupOf J).subgroupOf W).map W.subtype : Set J) =
      d.MZ.subgroupOf J := by
    rw [hP]
    exact d.exchanged_seed_centralizer_in_LQ1 s hG hM hu h t ht htS
  have hMQ : d.MZ ≤ normalizer (d.Q1 : Set G) :=
    d.MZ.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))
  apply (comap_mono (map_mono hA)).trans
  apply NormalElementaryQuotient.image_subgroupOf_le_seed_core W q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (((d.Z2 t).subgroupOf J).subgroupOf W) (d.Q1.subgroupOf J)
    (isPGroup_pCoreIn 2 d.MZ).comap_subtype
  · rw [hC]
    exact comap_mono d.Q1_le_MZ
  · rw [hC]
    exact (comap_mono hMQ).trans (d.Q1.le_normalizer_comap J.subtype)

/-- Recognized-component application: the offender in C.2.7 is an actual
best offender in the core just identified, on the original quotient action. -/
theorem HasExchangedLinearSource.original_seed_core_offender
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    ∃ A : Subgroup J, A ∈ elementaryAbelianMaxSubgroups (d.Q1.subgroupOf J) ∧
      IsBestOffender ρ (A.map q) ∧
      IsBestOffender (ρ.comp B.subtype) ((A.map q).subgroupOf B) ∧
      (A.map q).subgroupOf B ≤
        (subspaceKernel (ρ.comp B.subtype) (d.exchangedSeedSpace t J) ⊤).pCoreIn 2 := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B
  obtain ⟨A,hA,hb⟩ := d.exchanged_U_best_offender s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht htS
  exact ⟨A,hA,hb,s.best_offender_le_seed_core hG hM hu h t ht htS A hA.1 hb⟩

/-- The literal seed is fixed by the original component Sylow subgroup,
but is not fixed by the component. Both plane sizes are included. -/
theorem HasExchangedLinearSource.seed_fixed_and_moving
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    d.exchangedSeedSpace t J ≤ fixedSpace ρ ((d.SL.subgroupOf J).map q) ∧
      ¬ d.exchangedSeedSpace t J ≤ fixedSpace ρ ((d.L.subgroupOf J).map q) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ
  have hUJ : d.U t ≤ J :=
    (d.exchanged_U_le_Q1 s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht).trans le_sup_right
  constructor
  · intro v hv
    apply (NormalElementaryQuotient.mem_fixedSpace_image W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (d.SL.subgroupOf J) v).mpr
    intro x hx
    exact Subtype.ext (d.exchanged_Z2_le_centralizer_S s.1 t ht hv x hx.1)
  · intro hc
    apply d.exchanged_Z2_not_centralizes_L s.1 hM hu h t ht htS
    intro z hz l hl
    let zW : W := ⟨⟨z,hUJ (le_conjugateSpanBy _ _ hz)⟩,le_conjugateSpanBy _ _ hz⟩
    have hzP : Additive.ofMul zW ∈ d.exchangedSeedSpace t J := hz
    have hzC := (NormalElementaryQuotient.mem_fixedSpace_image W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (d.L.subgroupOf J) (Additive.ofMul zW)).mp (hc hzP)
    exact congrArg (fun x : J => (x : G)) (hzC ⟨l,mem_sup_left hl⟩ hl)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
