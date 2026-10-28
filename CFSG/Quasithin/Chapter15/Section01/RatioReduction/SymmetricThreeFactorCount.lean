module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SymmetricThreeSeparation
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SymmetricThreeFactorCount

/-!
# The selected local action has at most two symmetric-three factors

The actual conjugation image of M on V(M) is covered by M. Quasithinness
bounds its cover's three-rank by two, so a decomposition into marked S₃
factors has at most two factors. Combined with the normal-S₃ splitting,
an S₃² image on one support forces that support to be the unique factor.
The proper-orbit classification supplies the factor markings and the
literal support permutation; neither rank nor factor count is assumed.

Source: Aschbacher--Smith 15.1.2, printed pp.1084--1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_symmetricThree_factor_count
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation),
      (∀ i : d.Index, Nonempty ((d.factor i).Carrier ≃* Equiv.Perm (Fin 3))) →
      Nat.card d.Index ≤ 2 := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := actionHom M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d he
  exact c.symmetricThree_factor_count d he f.rangeRestrict f.rangeRestrict_surjective
    ((hG.twoLocal_sqtk hM.1.1.1).stronglyQuasithin 3 (by decide) (by decide))

theorem source_localAction_symmetricThree_pair_image_singleton
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation) (π : D →* Equiv.Perm d.Index),
      (∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g i)).actor) →
      (∀ g i, (c.ambientFactor d i).space.map (ρ g) =
        (c.ambientFactor d (π g i)).space) →
      (∀ j : d.Index, Nonempty ((d.factor j).Carrier ≃* Equiv.Perm (Fin 3))) →
      ∀ i : d.Index,
      (subspaceActionImage ρ (c.ambientFactor d i).space ≃*
        Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) →
      ∀ j : d.Index, j = i := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d π hp hs he i ei
  exact source_localAction_pair_image_unique_factor hG T hM U c d π hp hs
    (source_localAction_symmetricThree_factor_count hG T hM U c d he) he i ei
end CFSG.Quasithin.Chapter15.Section01
