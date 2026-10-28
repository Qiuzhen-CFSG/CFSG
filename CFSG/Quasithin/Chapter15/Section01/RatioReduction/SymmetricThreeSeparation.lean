module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SymmetricThreeSeparation

/-!
# Excluding a second symmetric-three factor in the selected local action

The action is the literal conjugation image of the ordering-maximal M on
V(M). Its original M cover has three-rank at most two by quasithinness.
Thus an S₃² action image on one support cannot kill a second normal S₃
factor. The factor-count and marking hypotheses remain the precise inputs
supplied by the preceding proper-orbit classification.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_pair_image_excludes_other_symmetricThree_factor
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
      Nat.card d.Index ≤ 2 → ∀ i j : d.Index, i ≠ j →
      ((c.ambientFactor d j).Carrier ≃* Equiv.Perm (Fin 3)) →
      (subspaceActionImage ρ (c.ambientFactor d i).space ≃*
        Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) → False := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := actionHom M V (le_normalizer_conjugateSpanBy _ _)
  dsimp only
  intro U c d π hp hs hcount i j hij ej ei
  exact c.not_pair_image_with_other_symmetricThree_factor d π hp hs hcount hij ej ei
    f.rangeRestrict f.rangeRestrict_surjective
    ((hG.twoLocal_sqtk hM.1.1.1).stronglyQuasithin 3 (by decide) (by decide))

theorem source_localAction_pair_image_unique_factor
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
      Nat.card d.Index ≤ 2 →
      (∀ j : d.Index, Nonempty ((c.ambientFactor d j).Carrier ≃* Equiv.Perm (Fin 3))) →
      ∀ i : d.Index,
      (subspaceActionImage ρ (c.ambientFactor d i).space ≃*
        Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) →
      ∀ j : d.Index, j = i := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d π hp hs hcount he i ei j
  by_contra hji
  obtain ⟨ej⟩ := he j
  exact source_localAction_pair_image_excludes_other_symmetricThree_factor
    hG T hM U c d π hp hs hcount i j (Ne.symm hji) ej ei

end CFSG.Quasithin.Chapter15.Section01
