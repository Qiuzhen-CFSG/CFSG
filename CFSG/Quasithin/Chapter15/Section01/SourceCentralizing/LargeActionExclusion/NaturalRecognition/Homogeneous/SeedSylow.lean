module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SourceCore

/-!
# A Sylow-fixed moving seed in the literal offender actor

Intersect the original Sylow subgroup with LQ1, pass through the original
centralizer quotient, and intersect with the normal offender-generated group.
The original seed is fixed by this Sylow subgroup and is still moved, since
the component image belongs to the offender-generated group.

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

private theorem seed_LQ1_sylow (d : CaseIComponentData T M Mc V)
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

/-- The actual seed is Sylow-fixed but not invariant on the offender actor.
This applies before any moved-module alternative is selected. -/
theorem HasExchangedLinearSource.seed_sylow_fixed_and_moving
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
    ∃ R : Sylow 2 B,
      d.exchangedSeedSpace t J ≤ fixedSpace (ρ.comp B.subtype) R ∧
      ¬ d.exchangedSeedSpace t J ≤ Representation.invariants (ρ.comp B.subtype) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B
  obtain ⟨P,hP⟩ := d.seed_LQ1_sylow s.1 hG hu h s.cubicFacts
  let : B.Normal := offenderSubgroup_normal ρ
  let Pq := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨R,hR⟩ := Pq.exists_subgroupOf_eq_of_normal B
  refine ⟨R, ?_, ?_⟩
  · intro z hz r
    have hrq : (r.val.val : J ⧸ centralizer (W : Set J)) ∈ (P : Subgroup J).map q := by
      change r.val ∈ (Pq : Subgroup _).subgroupOf B
      exact hR ▸ r.property
    obtain ⟨x,hx,he⟩ := hrq
    have hxS : (x : G) ∈ d.S :=
      (show (x : G) ∈ d.S ⊓ J from hP ▸ mem_map_of_mem J.subtype hx).1
    change ρ r.val.val z = z
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (d.exchanged_Z2_le_centralizer_S s.1 t ht hz x hxS)
  · obtain ⟨hKB,_⟩ := d.exchanged_U_moved_section s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht htS
    intro hm
    apply (s.seed_fixed_and_moving hG hM hu h t ht htS).2
    intro z hz k
    exact hm hz ⟨k,hKB k.property⟩

/-- Restrict the Sylow arrangement to the same component used by B.5.
Movement is retained under this restriction, including an outer actor. -/
theorem HasExchangedLinearSource.seed_component_sylow_fixed_and_moving
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
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ _c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      ∃ R : Sylow 2 K,
        d.exchangedSeedSpace t J ≤ fixedSpace ((ρ.comp B.subtype).comp K.subtype) R ∧
        ¬ d.exchangedSeedSpace t J ≤
          Representation.invariants ((ρ.comp B.subtype).comp K.subtype) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c
  obtain ⟨R₀,hfixed,_⟩ := s.seed_sylow_fixed_and_moving hG hM hu h t ht htS
  let : K.Normal := c.fitting_eq.symm ▸ inferInstance
  obtain ⟨R,hR⟩ := R₀.exists_subgroupOf_eq_of_normal K
  refine ⟨R, ?_, ?_⟩
  · intro z hz r
    have hr₀ : r.val ∈ (R₀ : Subgroup B).subgroupOf K := hR ▸ r.property
    exact hfixed hz ⟨r.val.val,hr₀⟩
  · obtain ⟨hKB,_⟩ := d.exchanged_U_moved_section s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht htS
    intro hm
    apply (s.seed_fixed_and_moving hG hM hu h t ht htS).2
    intro z hz k
    exact hm hz ⟨⟨k,hKB k.property⟩,k.property⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
