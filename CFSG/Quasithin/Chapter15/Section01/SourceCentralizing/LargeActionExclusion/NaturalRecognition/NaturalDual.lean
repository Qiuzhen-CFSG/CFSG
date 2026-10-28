module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Recognized

/-!
# Excluding the original natural-plus-dual branch

The original seed Z2 is fixed by the Sylow subgroup obtained from S ∩ LQ1.
Its component centralizer is ML, which normalizes Q1. After passing through
the literal centralizer quotient and restricting to the offender subgroup,
these facts make the Q1 image a normal two-subgroup of the actual Sylow
fixed-space centralizer. The original Q1 best offender therefore contradicts
clause (6) of B.5.1 in the natural-plus-dual case.

This proves the natural-plus-dual exclusion in 15.1.28 for both exchanged
plane sizes. The homogeneous alternatives and final natural coordinates
remain with the natural-recognition assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.1.28,
printed p.1103, and B.5.1(6), printed pp.99,103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterB.QuasisimpleSource

private theorem fixedCentralizer_core_of_seed
    {H : Type*} [Group H] [Finite H]
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (Z L Q : Subgroup H) (P : Sylow 2 H)
    (hZW : Z ≤ W) (hZP : Z ≤ centralizer (P : Set H))
    (hQP : Q ≤ P)
    (hcentral : L ⊓ centralizer (Z : Set H) ≤ normalizer (Q : Set H)) :
    let q := QuotientGroup.mk' (centralizer (W : Set H))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    B ≤ L.map q →
      ∃ R : Sylow 2 B,
        (Q.map q).subgroupOf B ≤
          (subspaceKernel (ρ.comp B.subtype)
            (fixedSpace (ρ.comp B.subtype) R) ⊤).pCoreIn 2 := by
  intro q ρ B hBL
  let : B.Normal := offenderSubgroup_normal ρ
  let Pq := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨R,hR⟩ := Pq.exists_subgroupOf_eq_of_normal B
  let σ := ρ.comp B.subtype
  let C := subspaceKernel σ (fixedSpace σ R) ⊤
  let Qb := (Q.map q).subgroupOf B
  have hQbR : Qb ≤ R := by
    rw [hR]
    exact comap_mono (map_mono hQP)
  have hQbC : Qb ≤ C := by
    intro x hx
    exact ⟨mem_top _, fun v hv => hv ⟨x,hQbR hx⟩⟩
  have hfix (z : Z) :
      Additive.ofMul (⟨z,hZW z.property⟩ : W) ∈ fixedSpace σ R := by
    have hz : Additive.ofMul (⟨z,hZW z.property⟩ : W) ∈
        fixedSpace ρ ((P : Subgroup H).map q) :=
      (NormalElementaryQuotient.mem_fixedSpace_image W q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) _ _).mpr
        (hZP z.property)
    intro r
    exact hz ⟨r.val.val, (show r.val.val ∈ (P : Subgroup H).map q from
      (show r.val ∈ (Pq : Subgroup _).subgroupOf B from hR ▸ r.property))⟩
  have hCn : C ≤ normalizer (Qb : Set B) := by
    apply le_trans _ ((Q.map q).le_normalizer_comap B.subtype)
    intro x hx
    obtain ⟨l,hl,hel⟩ := hBL x.property
    have hlZ : l ∈ centralizer (Z : Set H) := by
      intro z hz
      have he := hx.2 _ (hfix ⟨z,hz⟩)
      have he' := congrArg (fun v : Additive W => (v.toMul : H)) he
      change ((ρ (x : _) (Additive.ofMul ⟨z,hZW hz⟩)).toMul : H) = z at he'
      rw [←hel,NormalElementaryQuotient.representation_apply] at he'
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    exact Q.le_normalizer_map q ⟨l,hcentral ⟨hl,hlZ⟩,hel⟩
  exact ⟨R,le_pCoreIn_of_normalizes
    (((P.isPGroup'.to_le hQP).map q).comap_subtype) hQbC hCn⟩



open Stellmacher Theory.GroupTheory
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem exchanged_LQ1_sylow (d : CaseIComponentData T M Mc V)
    (s : d.ExchangedSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : Facts (d.L ⧸ pCore 2 d.L)) :
    ∃ P : Sylow 2 (d.L ⊔ d.Q1 : Subgroup G),
      (P : Subgroup (d.L ⊔ d.Q1 : Subgroup G)).map (d.L ⊔ d.Q1 : Subgroup G).subtype =
        d.S ⊓ (d.L ⊔ d.Q1) := by
  let := s.quasisimple
  let D := d.L ⊔ d.S
  let J := d.L ⊔ d.Q1
  have hQ1S := d.exchanged_Q1_le_S s hu
  have hJD : J ≤ D := sup_le le_sup_left (hQ1S.trans le_sup_right)
  have hSJ : d.S ≤ normalizer (J : Set G) :=
    (le_inf (d.S_le_G1.trans (d.G1_normalizes_L hG h hf))
      (d.S_le_T.trans s.sylow_normalizes_Q1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup d.L d.Q1)
  let : (J.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (le_sup_left.trans J.le_normalizer) hSJ)
  have hsD := s.centralizer_sylow.restrict (show d.S ≤ D from le_sup_right)
    (sup_le d.L_component.1 d.S_le_G1)
  exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hsD hJD
    (inferInstance : (J.subgroupOf D).Normal).isSubnormal

/-- The actual Q1 image lies in the two-core of the literal Sylow fixed-space
centralizer when the component is the whole offender-generated actor. -/
theorem exchanged_Q1_image_le_fixedCentralizer_core
    (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s hG hM hu h hi hf t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    (((d.L.subgroupOf J).map q).subgroupOf B) = ⊤ →
      ∃ R : Sylow 2 B,
        ((d.Q1.subgroupOf J).map q).subgroupOf B ≤
          (subspaceKernel (ρ.comp B.subtype)
            (fixedSpace (ρ.comp B.subtype) R) ⊤).pCoreIn 2 := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B hK
  obtain ⟨P,hP⟩ := d.exchanged_LQ1_sylow s hG hu h hf
  have hUJ : d.U t ≤ J :=
    (d.exchanged_U_le_Q1 s hG hM hu h hi hf t ht).trans le_sup_right
  have hZJ : d.Z2 t ≤ J := (le_conjugateSpanBy _ _).trans hUJ
  have hQP : d.Q1.subgroupOf J ≤ P := by
    intro x hx
    have hm : (x : G) ∈ (P : Subgroup J).map J.subtype := by
      rw [hP]
      exact ⟨d.exchanged_Q1_le_S s hu hx,x.property⟩
    obtain ⟨y,hy,he⟩ := hm
    exact (Subtype.ext he : y = x) ▸ hy
  have hZP : (d.Z2 t).subgroupOf J ≤ centralizer (P : Set J) := by
    intro z hz p hp
    have hpS : (p : G) ∈ d.S :=
      (show (p : G) ∈ d.S ⊓ J from hP ▸ mem_map_of_mem J.subtype hp).1
    exact Subtype.ext (d.exchanged_Z2_le_centralizer_S s t ht hz p hpS)
  have hnQ : d.MZ ≤ normalizer (d.Q1 : Set G) :=
    d.MZ.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))
  have hcentral : d.L.subgroupOf J ⊓ centralizer ((d.Z2 t).subgroupOf J : Set J) ≤
      normalizer (d.Q1.subgroupOf J : Set J) := by
    apply le_trans _ (d.Q1.le_normalizer_comap J.subtype)
    intro l hl
    apply hnQ
    apply d.ML_le_MZ
    rw [←d.exchanged_Z2_component_centralizer_eq_ML s hM hu h t ht htS]
    refine ⟨hl.1,?_⟩
    intro z hz
    exact congrArg Subtype.val (hl.2 ⟨z,hZJ hz⟩ hz)
  exact fixedCentralizer_core_of_seed W ((d.Z2 t).subgroupOf J)
    (d.L.subgroupOf J) (d.Q1.subgroupOf J) P
    (comap_mono (le_conjugateSpanBy _ _)) hZP hQP hcentral
    (subgroupOf_eq_top.mp hK)

/-- Original 15.1.28 excludes natural plus dual using the original Q1 best
offender, on precisely the representation classified by B.5. -/
theorem exchanged_U_not_naturalPlusDual
    (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s hG hM hu h hi hf t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      ∀ n : ℕ, n = 4 ∨ n = 5 → K = ⊤ →
        ¬ IsNaturalPlusDual (c.sectionData.space.toRepresentation.comp K.subtype) n := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c n hn hK hnat
  obtain ⟨R,hR⟩ := d.exchanged_Q1_image_le_fixedCentralizer_core
    s hG hM hu h hi hf t ht htS hK
  obtain ⟨hc⟩ := c.clause_six n hn hK hnat R
  obtain ⟨A,hAQ,hA⟩ := d.exchanged_U_best_offender s hG hM hu h hi hf t ht htS
  have hAB := hA.le_offenderSubgroup ρ
  apply hc.no_offenders ((A.map q).subgroupOf B) (hA.subgroupOf ρ hAB)
  exact (comap_mono (map_mono hAQ.1)).trans hR



/-- Literal recognized-component application of the natural-plus-dual exclusion.
All original centralizing hypotheses are retained, and both exchanged-plane
sizes are allowed. The action cases, moved section and Q1 offender use the
same quotient as `original_moved_cases`. -/
theorem HasExchangedLinearSource.original_moved_cases_not_naturalDual
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (_hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (_hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (_hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (_hne : M ≠ Mc) (_hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ∃ n : ℕ, ∃ hn : n = 4 ∨ n = 5,
      ∃ mark : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
        let hf := facts_of_small_binary_model (small_binary_model_of_marking hn mark)
        let hi := d.constrained_input hG h s.1.quasisimple s.1.core_nontrivial
          s.1.characteristic_control s.1.core_normalizer hf s.2.1
        let J := d.L ⊔ d.Q1
        let W := (d.U t).subgroupOf J
        let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h hi hf t ht
        letI := hr.normal
        letI := hr.elementary
        let q := QuotientGroup.mk' (centralizer (W : Set J))
        let ρ := NormalElementaryQuotient.representation W q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        let B := offenderSubgroup ρ
        let K := ((d.L.subgroupOf J).map q).subgroupOf B
        (d.L.subgroupOf J).map q ≤ B ∧
          ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp B.subtype) K,
            BinaryActor.ActionCase (ρ.comp B.subtype) K c.sectionData n ∧
            BinaryActor.MovedCase c.sectionData n ∧
            (K = ⊤ → ¬ IsNaturalPlusDual
              (c.sectionData.space.toRepresentation.comp K.subtype) n) ∧
            ∃ A : Subgroup J, A ∈ elementaryAbelianMaxSubgroups (d.Q1.subgroupOf J) ∧
              IsBestOffender ρ (A.map q) := by
  obtain ⟨n,hn,mark,hKB,c,hc,hm,hA⟩ := s.original_moved_cases hG hM hu h t ht htS
  refine ⟨n,hn,mark,?_⟩
  intro hf hi J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K
  exact ⟨hKB,c,hc,hm,
    d.exchanged_U_not_naturalPlusDual s.1 hG hM hu h hi hf t ht htS c n hn,hA⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
