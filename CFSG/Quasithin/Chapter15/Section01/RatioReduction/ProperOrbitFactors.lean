module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.OrbitSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ProperOrbitFactors

/-!
# Proper orbit spans in the original selected action

The local module is contained in the Sylow two-subgroup, so its Sylow-fixed
space is exactly the original central involution seed. The proper support
orbit span therefore supplies the literal nonzero proper factor subspace
invariant under its actor and the original Sylow support stabilizer.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_seed_eq_fixedSpace
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let f : M →* internalActionImage M V (le_normalizer_conjugateSpanBy _ _) :=
      (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
    Z = fixedSpace ρ ((T.subtype hM.1.2 : Subgroup M).map f) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f : M →* internalActionImage M V (le_normalizer_conjugateSpanBy _ _) :=
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  change Z = fixedSpace ρ ((T.subtype hM.1.2 : Subgroup M).map f)
  apply le_antisymm (source_localAction_seed_span hG T hM).1
  intro v hv
  let B := V.subgroupOf M
  let := (localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩).normal
  let := (localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩).elementary
  have hVM : V ≤ M := localModule_le T hM.1.2
  have hvM : (v.toMul : G) ∈ M := hVM v.toMul.property
  have hvB : (⟨v.toMul,hvM⟩ : M) ∈ B := v.toMul.property
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  refine ⟨(IsElementaryAbelian.isPGroup 2 B).le_sylow_of_normal
    (T.subtype hM.1.2) hvB,?_,?_⟩
  · exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ v.toMul.property
  · intro t ht
    change t * (v.toMul : G) = (v.toMul : G) * t
    have hfix := hv ⟨f ⟨t,hM.1.2 ht⟩,
      mem_map_of_mem f (show (⟨t,hM.1.2 ht⟩ : M) ∈ (T.subtype hM.1.2 : Subgroup M) from ht)⟩
    have he := congrArg (fun w : Additive V => (w.toMul : G)) hfix
    change t * (v.toMul : G) * t⁻¹ = v.toMul at he
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun x : G => x * t) he
theorem source_localAction_proper_orbit_factor_reducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
    let S := (T.subtype hM.1.2 : Subgroup M).map f
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
    ∀ i, Homogeneous.orbitSpan ρ (c.orbitActor d π i) (Z ⊓ c.orbitSpace d π i) <
      c.orbitSpace d π i →
    ∃ j : d.Index, (∃ g : D, π g i = j) ∧
      ∃ B : Submodule (ZMod 2) (Additive V), B ≠ ⊥ ∧ B < (c.ambientFactor d j).space ∧
        (c.ambientFactor d j).actor ⊔
          (S ⊓ subspaceStabilizer ρ (c.ambientFactor d j).space) ≤ subspaceStabilizer ρ B := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let S := (T.subtype hM.1.2 : Subgroup M).map f
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd π hp hs i hproper
  rw [source_localAction_seed_eq_fixedSpace hG T hM] at hproper
  exact c.proper_orbit_factor_subspace d (source_localAction_twoCore hG T hM)
    hd π hp hs S ((T.subtype hM.1.2).isPGroup'.map f) i hproper

end CFSG.Quasithin.Chapter15.Section01
