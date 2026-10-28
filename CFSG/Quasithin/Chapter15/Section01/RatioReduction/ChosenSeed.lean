module
public import Theory.Representation.BinaryOffender.ComplementSeed
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperOrbitOmega

/-!
# The literal central seed of the chosen summand

Project the original central seed through an invariant complementary
splitting of V(M). The Sylow-fixed-space identity identifies the projection
with vectors of the same central seed. The faithful-image action and its
original surjection then identify the resulting linear orbit with the
ambient conjugate span. This supplies V=<(Z∩V)^M> for the proper module
chosen in15.1.4, without replacing it by the larger original V(M).
Source: Aschbacher--Smith15.1.5(1) and15.1.9, pp.1087--1089.
-/

public section
open Subgroup Representation

open Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_complement_generated_seed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U R : Submodule (ZMod 2) (Additive V)),
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ U →
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ R → IsCompl U R →
      let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
      W ≤ M ∧ M ≤ normalizer (W : Set G) ∧ IsElementaryAbelian 2 W ∧
      W = conjugateSpanBy (centralInvolutions T ⊓ W) M := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let S := (T.subtype hM.1.2 : Subgroup M).map f
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  dsimp only
  intro U R hU hR hc
  let B : Subgroup V := Subgroup.toAddSubgroup.symm U.toAddSubgroup
  let W := B.map V.subtype
  have hWM : W ≤ M := (map_subtype_le B).trans (localModule_le T hM.1.2)
  have hnW : M ≤ normalizer (W : Set G) := by
    apply le_normalizer_iff.mpr
    rintro m hm _ ⟨v,hv,rfl⟩
    have hh := (hU (mem_top (f ⟨m,hm⟩)) (Additive.ofMul v)).mpr hv
    exact ⟨(ρ (f ⟨m,hm⟩) (Additive.ofMul v)).toMul,hh,rfl⟩
  let : IsElementaryAbelian 2 B := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun b =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) b.val)) }
  have hEW : IsElementaryAbelian 2 W := IsElementaryAbelian.map V.subtype
  refine ⟨hWM,hnW,hEW,?_⟩
  have hz : Z = fixedSpace ρ S := source_localAction_seed_eq_fixedSpace hG T hM
  have hgen : Homogeneous.orbitSpan ρ ⊤ (Z ⊓ U) = U := by
    rw [hz]
    apply complement_seed_span ρ S U R hU hR hc
    rw [←hz]
    exact (source_localAction_seed_span hG T hM).2
  let L := conjugateSpanBy (centralInvolutions T ⊓ W) M
  let C := AddSubgroup.toZModSubmodule 2 (L.subgroupOf V).toAddSubgroup
  have hseed : Z ⊓ U ≤ C := by
    intro v hv
    exact le_conjugateSpanBy _ _ ⟨hv.1,mem_map_of_mem V.subtype hv.2⟩
  have hstable : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ C := by
    apply le_subspaceStabilizer
    intro a _ v hv
    obtain ⟨m,rfl⟩ := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective a
    exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _) (m : G) m.property
      (v.toMul : G) hv
  have hUC : U ≤ C := hgen ▸ Homogeneous.orbitSpan_le ρ hseed hstable
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact hUC hv
  · exact conjugateSpanBy_le inf_le_right hnW
end CFSG.Quasithin.Chapter15.Section01

