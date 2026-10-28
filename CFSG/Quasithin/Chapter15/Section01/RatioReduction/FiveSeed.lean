module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.FiveNormalClosure
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SelectedAction
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed

/-!
# The original selected quintic actor and its seed reduction

The faithful literal image on V(M) and its original Sylow-fixed generating
seed instantiate the quintic normal-closure theorem. The embedded two-residual
is odd, supplements the supplied Sylow intersection, and lies in the Fitting
subgroup. The factor action on its moved space retains the original minimum
and starred actors and admits the fully Fitting-moved finite decomposition.
The hypothesis concerns the specified original actor only; no assertion is
made that every original starred actor moves the five-core.

Source: Aschbacher--Smith 15.1.2, printed pp.1084--1085, using D.2.13 and
D.2.23--24, printed pp.184--189.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The specified original quintic actor has a normal-closure image in
the two-core of the literal Fitting quotient. -/
theorem source_localAction_five_normalClosure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ A : Subgroup D, A ∈ QhatStar ρ → rank A = 1 → ⁅pCore 5 D,A⁆ ≠ ⊥ →
      IsPGroup 5 (pResidual 2 (normalClosure (A : Set D))) ∧
      normalClosure (A : Set D) ≤ (pCore 2 (D ⧸ fittingSubgroup D)).comap
        (QuotientGroup.mk' (fittingSubgroup D)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro A hA hr hm
  exact ⟨CyclicSource.source_five_normalClosure_residual ρ
    (imageRepresentation_injective _ _ _) hA hr hm,
    CyclicSource.source_five_normalClosure_le_twoCore_preimage ρ
      (imageRepresentation_injective _ _ _) hA hr hm⟩

/-- The actual selected seed gives the normal closure's fully moved factor
and its finite indecomposable decomposition, using the original actor. -/
theorem source_localAction_five_seed_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ A : Subgroup D, A ∈ QhatStar ρ → rank A = 1 → ⁅pCore 5 D,A⁆ ≠ ⊥ →
      let N := normalClosure (A : Set D)
      let P := (pResidual 2 N).map N.subtype
      ∃ d : RatioDecomposition.FactorData ρ N (subspaceCommutator ρ ⊤ P),
        subspaceCommutator d.representation ⊤ (fittingSubgroup N) = ⊤ ∧
        ∃ c : RatioDecomposition.Decomposition d.representation, c.FittingFull := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  dsimp only
  intro A hA hr hm
  exact CyclicSource.source_five_normalClosure_seed_factors ρ
    (imageRepresentation_injective _ _ _) hA hr hm S Z hfix hspan

end CFSG.Quasithin.Chapter15.Section01
