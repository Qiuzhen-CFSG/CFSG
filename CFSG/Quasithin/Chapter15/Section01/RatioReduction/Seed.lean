module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction
public import Theory.Representation.BinaryOffender.MarkedOrbitCore
/-!
# The actual Sylow-fixed seed in the faithful local action

Pass the original central involutions through the literal conjugation-image
map. They remain fixed by the image of the chosen Sylow subgroup, and their
orbit spans V(M), since V(M) is the original conjugate span. This retains the
source hypothesis needed when restricting the action to the Fitting-moved
submodule in 15.1.2; faithfulness alone does not justify that restriction.
Source: Aschbacher--Smith Notation A.5.1 and 15.1.2, printed pp.1083--1085.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The faithful action keeps the actual Sylow-fixed seed and its whole spanning orbit. -/
theorem source_localAction_seed_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let f : M →* internalActionImage M V (le_normalizer_conjugateSpanBy _ _) :=
      (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let P := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
    let S := (T.subtype hM.1.2).mapSurjective (f := f)
      (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    P ≤ fixedSpace ρ (S : Subgroup _) ∧
      Submodule.span (ZMod 2)
        {w | ∃ (g : internalActionImage M V (le_normalizer_conjugateSpanBy _ _)) (v : Additive V),
          v ∈ P ∧ ρ g v = w} = ⊤ := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f : M →* internalActionImage M V (le_normalizer_conjugateSpanBy _ _) :=
      (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let P := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  change P ≤ fixedSpace ρ ((T.subtype hM.1.2 : Subgroup M).map f) ∧ _
  constructor
  · intro v hv a
    obtain ⟨s,hs,he⟩ := a.property
    have hc := ((mem_omegaOneCenterAmbient_iff _ _).mp hv).2.2 (s : G) hs
    have hvfix : ρ (f s) v = v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      change (s : G) * (v.toMul : G) * (s : G)⁻¹ = v.toMul
      exact (congrArg (fun x : G => x * (s : G)⁻¹) hc).trans (mul_inv_cancel_right _ _)
    exact (congrArg (fun g => ρ g v) he).symm.trans hvfix
  · let W := Submodule.span (ZMod 2)
      {w | ∃ (g : internalActionImage M V (le_normalizer_conjugateSpanBy _ _)) (v : Additive V),
        v ∈ P ∧ ρ g v = w}
    let B : Subgroup V := Subgroup.toAddSubgroup.symm W.toAddSubgroup
    have hle : V ≤ B.map V.subtype := by
      apply (closure_le _).mpr
      rintro x ⟨m,hm,z,hz,rfl⟩
      have hzV : z ∈ V := le_conjugateSpanBy _ _ hz
      have hxV : m * z * m⁻¹ ∈ V :=
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy _ _) m hm z hzV
      refine ⟨⟨m*z*m⁻¹,hxV⟩,?_,rfl⟩
      change Additive.ofMul (⟨m*z*m⁻¹,hxV⟩ : V) ∈ W
      exact Submodule.subset_span ⟨f ⟨m,hm⟩,Additive.ofMul ⟨z,hzV⟩,hz,rfl⟩
    change W = ⊤
    apply top_unique
    intro v _
    obtain ⟨b,hb,he⟩ := hle v.toMul.property
    have hv : b = v.toMul := Subtype.ext he
    change Additive.ofMul b ∈ W at hb
    have hv' : Additive.ofMul b = v := congrArg Additive.ofMul hv
    exact (congrArg (fun x : Additive V => x ∈ W) hv').mp hb
end CFSG.Quasithin.Chapter15.Section01