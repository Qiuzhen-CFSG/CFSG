module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ProperCyclicThree
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.ProperFactorSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SupportStabilizerSylow
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SymmetricThreeFactorCount
/-!
# The original proper orbit supplies a proper Sylow-fixed factor seed

The binary orbit trace reconstructs a fixed vector on a selected support
up to its actor fixed space. Coprime averaging on the marked odd kernel then
shows that a support omitted by the original orbit seed has a proper actor
span of its restricted Sylow-fixed vectors. In the original proper branch
all factors are S3, so the source rank bound makes every support stabilizer
normal. The restricted original Sylow subgroup is therefore a genuine Sylow
subgroup of that stabilizer, as required by the literal support-image argument.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]
theorem source_localAction_proper_orbit_cyclicThree_seed
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
      ∃ l : CyclicSource.LocalGeneration (d.factor j).action,
        letI := BinaryGroupAction.action (d.factor j).action
        letI : Finite (d.factor j).Space := Module.finite_of_finite (ZMod 2)
        letI : IsElementaryAbelian 2 (Multiplicative (d.factor j).Space) := BinaryGroupAction.elementary
        letI := l.normal
        ChapterD.Section02.CyclicThreeEndpoint (V := Multiplicative (d.factor j).Space)
          l.kernel l.involution ∧ Module.finrank (ZMod 2) (d.factor j).Space = 4 ∧
      Homogeneous.orbitSpan ρ (c.ambientFactor d j).actor
        (fixedSpace ρ (S ⊓ subspaceStabilizer ρ (c.ambientFactor d j).space) ⊓
          (c.ambientFactor d j).space) < (c.ambientFactor d j).space := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let S := (T.subtype hM.1.2 : Subgroup M).map f
  dsimp only
  intro U c d hd π hp hs i hproper
  rw [source_localAction_seed_eq_fixedSpace hG T hM] at hproper
  let := Jhat_normal ρ
  obtain ⟨j,hjo,hmissing,B,hB0,hB,hstable⟩ :=
    c.proper_orbit_factor_missing_seed d (source_localAction_twoCore hG T hM)
      hd π hp hs S ((T.subtype hM.1.2).isPGroup'.map f) i hproper
  have hi : ¬ IsIrreducible (d.factor j).action :=
    (c.ambientFactor d j).not_irreducible_of_proper_subspace B hB0 hB
      (le_sup_left.trans hstable)
  obtain ⟨l,hl⟩ := source_localAction_reducible_factor_endpoints hG T hempty hM hmany hJ
    hu hne U c d hd j hi
  have hspan := c.factor_fixed_seed_span_proper d π hs S i j hjo l hmissing
  refine ⟨j,hjo,l,?_⟩
  let := BinaryGroupAction.action (d.factor j).action
  let : Finite (d.factor j).Space := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative (d.factor j).Space) := BinaryGroupAction.elementary
  let := l.normal
  rcases hl with ⟨h3,hdim⟩ | h9
  · exact ⟨h3,hdim,hspan⟩
  · exact (source_localAction_no_nine_proper_factor hG T hempty hM hmany hJ hu hne
      U c d hd j l h9 B hB0 hB hstable).elim

theorem source_localAction_proper_orbit_cyclicThree_sylow_seed
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
    (∀ i, Homogeneous.orbitSpan ρ (c.orbitActor d π i) (Z ⊓ c.orbitSpace d π i) <
      c.orbitSpace d π i) → ∀ i,
    ∃ j : d.Index, (∃ g : D, π g i = j) ∧
      ∃ l : CyclicSource.LocalGeneration (d.factor j).action,
        letI := BinaryGroupAction.action (d.factor j).action
        letI : Finite (d.factor j).Space := Module.finite_of_finite (ZMod 2)
        letI : IsElementaryAbelian 2 (Multiplicative (d.factor j).Space) := BinaryGroupAction.elementary
        letI := l.normal
        ChapterD.Section02.CyclicThreeEndpoint (V := Multiplicative (d.factor j).Space)
          l.kernel l.involution ∧ Module.finrank (ZMod 2) (d.factor j).Space = 4 ∧
      ∃ P : Sylow 2 (subspaceStabilizer ρ (c.ambientFactor d j).space),
        (P : Subgroup (subspaceStabilizer ρ (c.ambientFactor d j).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d j).space).subtype =
            S ⊓ subspaceStabilizer ρ (c.ambientFactor d j).space ∧
        Homogeneous.orbitSpan ρ (c.ambientFactor d j).actor
          (fixedSpace ρ ((P : Subgroup (subspaceStabilizer ρ (c.ambientFactor d j).space)).map
            (subspaceStabilizer ρ (c.ambientFactor d j).space).subtype) ⊓
              (c.ambientFactor d j).space) < (c.ambientFactor d j).space := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let Q := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  dsimp only
  intro U c d hd π hp hs hproper i
  have hcount := source_localAction_symmetricThree_factor_count hG T hM U c d
    (source_localAction_all_symmetricThree_of_proper_orbits hG T hempty hM hmany hJ
      hu hne U c d hd π hp hs hproper)
  obtain ⟨j,hjo,l,h3,hdim,hseed⟩ := source_localAction_proper_orbit_cyclicThree_seed
    hG T hempty hM hmany hJ hu hne U c d hd π hp hs i (hproper i)
  obtain ⟨P,hP⟩ := c.exists_support_stabilizer_sylow_of_count d π hs hcount Q j
  refine ⟨j,hjo,l,h3,hdim,P,?_,?_⟩
  · exact hP
  · rw [hP]
    exact hseed

end CFSG.Quasithin.Chapter15.Section01
