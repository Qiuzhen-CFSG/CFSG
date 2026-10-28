module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperNineExclusion
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorCarrierConjugacy
/-!
# Marked S3 factors in the original proper orbit branch

A proper orbit seed span selects a nonzero proper factor subspace invariant
under its actor and its original Sylow support stabilizer. Genuine D.2.17
reduces the factor to the marked cubic four-space or elementary-nine endpoint;
the original centralizer quotient irreducibility excludes the latter.
Conjugating the embedded actors transports the surviving S3 marking to every
factor in the orbit. Applying the proper-span hypothesis to every orbit thus
marks every original factor carrier as S3.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]
theorem source_localAction_proper_orbit_cyclicThree
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
          (S ⊓ subspaceStabilizer ρ (c.ambientFactor d j).space) ≤ subspaceStabilizer ρ B ∧
      ∃ l : CyclicSource.LocalGeneration (d.factor j).action,
        letI := BinaryGroupAction.action (d.factor j).action
        letI : Finite (d.factor j).Space := Module.finite_of_finite (ZMod 2)
        letI : IsElementaryAbelian 2 (Multiplicative (d.factor j).Space) := BinaryGroupAction.elementary
        letI := l.normal
        ChapterD.Section02.CyclicThreeEndpoint (V := Multiplicative (d.factor j).Space)
          l.kernel l.involution ∧ Module.finrank (ZMod 2) (d.factor j).Space = 4 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd π hp hs i hproper
  obtain ⟨j,hjo,B,hB0,hB,hstable⟩ := source_localAction_proper_orbit_factor_reducible
    hG T hM U c d hd π hp hs i hproper
  have hi : ¬ IsIrreducible (d.factor j).action :=
    (c.ambientFactor d j).not_irreducible_of_proper_subspace B hB0 hB
      (le_sup_left.trans hstable)
  obtain ⟨l,hl⟩ := source_localAction_reducible_factor_endpoints hG T hempty hM hmany hJ
    hu hne U c d hd j hi
  refine ⟨j,hjo,B,hB0,hB,hstable,l,?_⟩
  let := BinaryGroupAction.action (d.factor j).action
  let : Finite (d.factor j).Space := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (d.factor j).Space) := BinaryGroupAction.elementary
  let := l.normal
  rcases hl with h3 | h9
  · exact h3
  · exact (source_localAction_no_nine_proper_factor hG T hempty hM hmany hJ hu hne
      U c d hd j l h9 B hB0 hB hstable).elim

theorem source_localAction_all_symmetricThree_of_proper_orbits
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
    ∀ i : d.Index, Nonempty ((d.factor i).Carrier ≃* Equiv.Perm (Fin 3)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d hd π hp hs hproper i
  obtain ⟨j,⟨g,hg⟩,B,_hB0,_hB,_hstable,l,h3,_hdim⟩ :=
    source_localAction_proper_orbit_cyclicThree hG T hempty hM hmany hJ hu hne
      U c d hd π hp hs i (hproper i)
  let := BinaryGroupAction.action (d.factor j).action
  let : Finite (d.factor j).Space := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (d.factor j).Space) := BinaryGroupAction.elementary
  let := l.normal
  obtain ⟨ej⟩ := h3.ambient_equiv
  have he := hp g i
  rw [hg] at he
  exact ⟨(c.factorCarrierEquivOfConjugate d g he).trans ej⟩
end CFSG.Quasithin.Chapter15.Section01
