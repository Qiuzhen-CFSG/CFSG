module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.BeforeMoved.AllNoncyclic
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.MovedSeed
/-!
# The selected all-noncyclic branch of the original D.2 reduction

The literal M-action on V(M) is faithful, solvable, two-core-free and covered
by the original SQTK group M. When all its original starred actors are
noncyclic, their generated group K has odd normal kernel P=K∩F(D), where D
is the actual action image. The marked Sylow image gives K=P(K∩S).

The original central seed then makes the P-fixed summand K-fixed. The
existing fixed-seed theorem supplies a faithful, fully Fitting-moved action
on [V,P], preserves the original starred family, and constructs its finite
indecomposable decomposition. No full-moved premise is imposed on V(M).
Source: Aschbacher–Smith 15.1.2, first paragraph, printed p.1084.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original selected conjugation action supplies the SQTK cover and
all source hypotheses for each old noncyclic starred actor. -/
theorem source_localAction_noncyclic_normalClosure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
    ∀ A : Subgroup D, A ∈ QhatStar ρ → 1 < rank A →
      normalClosure (A : Set D) ≤ (pCore 2 (D ⧸ fittingSubgroup D)).comap
        (QuotientGroup.mk' (fittingSubgroup D)) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let D := internalActionImage M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M (localModule T M) (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  dsimp only
  intro A hA hr
  exact BeforeMoved.source_normalClosure_le_twoCore_preimage ρ
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective (imageRepresentation_injective _ _ _) hA hr
    (generalizedFitting_eq_fitting_of_solvable D) (source_localAction_twoCore hG T hM)

/-- When every original starred actor is noncyclic, Jhat has the explicit
odd normal kernel Jhat∩F(D), with the marked Sylow factorization. -/
theorem source_localAction_noncyclic_odd_factorization
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let S := (T.subtype hM.1.2).mapSurjective (f := f)
      (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    let K := Jhat ρ
    let P := K ⊓ fittingSubgroup D
    (∀ A ∈ QhatStar ρ, 1 < rank A) →
      P.Normal ∧ Odd (Nat.card P) ∧ K = P ⊔ (K ⊓ (S : Subgroup D)) ∧
        P.subgroupOf K ≤ fittingSubgroup K := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let S := (T.subtype hM.1.2).mapSurjective (f := f)
    (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
  let := source_localAction_isSolvable hG T hempty hM
  dsimp only
  intro hnoncyclic
  exact BeforeMoved.source_Jhat_odd_factorization ρ
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    (imageRepresentation_injective _ _ _) (generalizedFitting_eq_fitting_of_solvable D)
    (source_localAction_twoCore hG T hM) hnoncyclic S

/-- The actual all-noncyclic source branch supplies the literal, faithful,
fully Fitting-moved factor datum and the finite D.2.16 decomposition. -/
theorem source_centralizing_noncyclic_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let K := Jhat ρ
    let P := K ⊓ fittingSubgroup D
    (∀ A ∈ QhatStar ρ, 1 < rank A) →
      ∃ d : RatioDecomposition.FactorData ρ K (subspaceCommutator ρ ⊤ P),
        subspaceCommutator d.representation ⊤ (fittingSubgroup K) = ⊤ ∧
        ∃ c : RatioDecomposition.Decomposition d.representation, c.FittingFull := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let K := Jhat ρ
  let P := K ⊓ fittingSubgroup D
  dsimp only
  intro hnoncyclic
  obtain ⟨hP,hodd,hgen,hPF⟩ :=
    source_localAction_noncyclic_odd_factorization hG T hempty hM hnoncyclic
  exact source_centralizing_odd_factorData hG T hempty hM hmany hJ K P
    (Jhat_normal ρ) hP hodd hgen rfl hPF
end CFSG.Quasithin.Chapter15.Section01
