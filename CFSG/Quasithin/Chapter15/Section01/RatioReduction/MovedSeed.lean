module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Assembly
/-!
# The selected fixed-seed reduction and literal D.2 decomposition

For normal odd P and the normal starred-generated actor K in M/C_M(V),
the factorization K=P(K∩T̄) and the original central seed show that the odd
fixed summand is fixed by K. Restriction to [V,P] is therefore faithful and
retains the original cubic minimum and starred subgroups. If P lies in the
Fitting subgroup of K, its action is fully Fitting-moved, so the finite
D.2.16 theorem produces indecomposable factors with literal maps and supports.

The group-theoretic odd-kernel factorization remains explicit. Its source
producer is separate; the full-moved hypothesis is not assumed of V(M).
Source: Aschbacher--Smith 15.1.2, printed pp.1084--1085, using D.2.16--17.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
/-- The fixed-seed argument on the original local conjugation image. -/
theorem source_localAction_odd_moved_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let S := (T.subtype hM.1.2).mapSurjective (f := f)
      (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    ∀ K P : Subgroup D, K.Normal → P.Normal → Odd (Nat.card P) →
      K = P ⊔ (K ⊓ (S : Subgroup D)) →
      subspaceCommutator ρ ⊤ K = subspaceCommutator ρ ⊤ P ∧
      fixedSpace ρ P = fixedSpace ρ K ∧
      IsCompl (subspaceCommutator ρ ⊤ P) (fixedSpace ρ K) ∧
      subspaceCommutator ρ (subspaceCommutator ρ ⊤ P) K = subspaceCommutator ρ ⊤ P := by
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
  intro K P hK hP hodd hKP
  let := hK
  let := hP
  exact ⟨NormalOddSeed.moved_eq ρ K P (S : Subgroup D) hKP Z hfix hspan,
    NormalOddSeed.fixed_eq ρ K P (S : Subgroup D) hodd hKP Z hfix hspan,
    NormalOddSeed.isCompl_moved_fixed ρ K P (S : Subgroup D) hodd hKP Z hfix hspan,
    NormalOddSeed.moved_self ρ K P (S : Subgroup D) hodd hKP Z hfix hspan⟩
/-- The original selected action supplies the complete literal input to the
finite D.2.16 splitting once the odd-kernel factorization is established. -/
theorem source_centralizing_odd_factorData
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
    let f : M →* D := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let S := (T.subtype hM.1.2).mapSurjective (f := f)
      (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective
    ∀ K P : Subgroup D, K.Normal → P.Normal → Odd (Nat.card P) →
      K = P ⊔ (K ⊓ (S : Subgroup D)) → K = Jhat ρ →
      P.subgroupOf K ≤ fittingSubgroup K →
      ∃ d : RatioDecomposition.FactorData ρ K (subspaceCommutator ρ ⊤ P),
        subspaceCommutator d.representation ⊤ (fittingSubgroup K) = ⊤ ∧
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
  obtain ⟨A,hA,_⟩ := source_centralizing_minimumActor hG T hempty hM hmany hJ
  dsimp only
  intro K P hK hP hodd hKP hKJ hPF
  let := hK
  let := hP
  let d := RatioDecomposition.normalOddFactorData ρ (imageRepresentation_injective _ _ _)
    K P (S : Subgroup D) hodd hKP Z hfix hspan hKJ ⟨A,hA⟩
  have he : d.representation = RatioDecomposition.oddMovedAction ρ K P :=
    RatioDecomposition.FactorData.representation_eq_side ρ d
      (RatioDecomposition.oddMoved_stable ρ K P)
  have hd : subspaceCommutator d.representation ⊤ (fittingSubgroup K) = ⊤ := by
    rw [he]
    exact RatioDecomposition.oddMovedAction_full_of_le ρ K P
      (hKP.symm ▸ (le_sup_left : P ≤ P ⊔ (K ⊓ (S : Subgroup D)))) hodd
      (fittingSubgroup K) hPF
  exact ⟨d,hd,RatioDecomposition.source_fitting_decomposition d.representation
    d.faithful d.generated hd (d.ratio.trans_le
      (source_centralizing_cubicRatio_le_two hG T hempty hM hmany hJ))⟩

end CFSG.Quasithin.Chapter15.Section01