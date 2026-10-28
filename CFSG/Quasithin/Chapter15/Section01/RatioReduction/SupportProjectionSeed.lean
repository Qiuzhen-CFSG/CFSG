module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperFactorSeed
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SymmetricThreeSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SupportProjectionSeed
/-!
# Projecting the original generating seed onto a factor support

In the original proper orbit branch every factor is S3, so the source rank
bound gives at most two supports. Each support stabilizer is consequently
normal and supplements the original Sylow subgroup. The original fixed seed
already spans under that stabilizer; the equivariant projection along the
actor fixed space supplies the full stabilizer span on the selected support.
Together with its proper actor span, this excludes the S3 by C2 image and
forces the literal S3 by S3 image and a unique original factor.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_support_stabilizer_seed_full
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let S := (T.subtype hM.1.2 : Subgroup M).map f
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ j : d.Index, Nonempty ((d.factor j).Carrier ≃* Equiv.Perm (Fin 3))) →
    ∀ i (P : Sylow 2 (subspaceStabilizer ρ (c.ambientFactor d i).space)),
      (P : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
        (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype =
          S ⊓ subspaceStabilizer ρ (c.ambientFactor d i).space →
      Homogeneous.orbitSpan ρ (subspaceStabilizer ρ (c.ambientFactor d i).space)
        (fixedSpace ρ ((P : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype) ⊓
          (c.ambientFactor d i).space) = (c.ambientFactor d i).space := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let Q := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  dsimp only
  intro U c d hd π hp hs he i P hP
  let := Jhat_normal ρ
  have hcount := source_localAction_symmetricThree_factor_count hG T hM U c d he
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  have hfull : Submodule.span (ZMod 2)
      {w | ∃ g v, v ∈ fixedSpace ρ ((T.subtype hM.1.2 : Subgroup M).map f) ∧ ρ g v = w} = ⊤ := by
    apply top_unique
    rw [←hspan]
    exact Submodule.span_mono (by rintro _ ⟨g,v,hv,rfl⟩; exact ⟨g,v,hfix hv,rfl⟩)
  have hh := c.support_stabilizer_fixed_seed_full d π hs hcount Q i
    (c.ambient_space_fixed_compl d (source_localAction_twoCore hG T hM) hd i)
    (c.support_stabilizer_normalizes_actor d π hp hs i) hfull
  rw [hP]
  exact hh

theorem source_localAction_proper_orbits_unique_factor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ i, Homogeneous.orbitSpan ρ (c.orbitActor d π i) (Z ⊓ c.orbitSpace d π i) <
        c.orbitSpace d π i) →
      ∃ j : d.Index, (∀ k : d.Index, k = j) ∧
        Module.finrank (ZMod 2) (d.factor j).Space = 4 ∧
        Nonempty (subspaceActionImage ρ (c.ambientFactor d j).space ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd π hp hs hproper
  have he := source_localAction_all_symmetricThree_of_proper_orbits
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs hproper
  obtain ⟨i⟩ := d.nonemptyIndex
  obtain ⟨j,_hjo,l,_h3,hdim,P,hP,hseed⟩ :=
    source_localAction_proper_orbit_cyclicThree_sylow_seed
      hG T hempty hM hmany hJ hu hne U c d hd π hp hs hproper i
  have hspan := source_localAction_support_stabilizer_seed_full
    hG T hM U c d hd π hp hs he j P hP
  refine ⟨j,?_,hdim,?_⟩
  · exact source_localAction_proper_seed_unique_factor
      hG T hM U c d π hp hs he j hdim P hseed hspan
  · exact source_localAction_proper_seed_pair_image
      hG T hM U c d π hp hs j hdim (he j).some P hseed hspan
end CFSG.Quasithin.Chapter15.Section01
