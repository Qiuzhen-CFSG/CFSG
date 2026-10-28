module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.SymmetricThreeFactorCount
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SymmetricThreeSeed

/-!
# The proper Sylow-fixed seed in the selected local action

For the original conjugation action on V(M), the support permutation
normalizes the marked factor actor. A proper Sylow-fixed seed on a
four-dimensional S₃ factor yields the two literal support images. If all
factors are S₃, the S₃² image forces a unique factor by the original
quasithin rank bound on M. No four-divisibility or factor-count premise is
retained at this source consumer.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_symmetricThree_proper_seed_image_cases
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
      ∀ i : d.Index,
      Module.finrank (ZMod 2) (d.factor i).Space = 4 →
      ((d.factor i).Carrier ≃* Equiv.Perm (Fin 3)) →
      ∀ S : Sylow 2 (subspaceStabilizer ρ (c.ambientFactor d i).space),
      Homogeneous.orbitSpan ρ (c.ambientFactor d i).actor
        (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype) ⊓
          (c.ambientFactor d i).space) < (c.ambientFactor d i).space →
      Nonempty (subspaceActionImage ρ (c.ambientFactor d i).space ≃*
        (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) ∨
      Nonempty (subspaceActionImage ρ (c.ambientFactor d i).space ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d π hp hs i hdim e S hproper
  exact (c.ambientFactor d i).symmetricThree_proper_sylow_seed_cases hdim e
    (c.support_stabilizer_normalizes_actor d π hp hs i) S hproper

theorem source_localAction_proper_seed_small_image_or_unique_factor
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
      Module.finrank (ZMod 2) (d.factor i).Space = 4 →
      ∀ S : Sylow 2 (subspaceStabilizer ρ (c.ambientFactor d i).space),
      Homogeneous.orbitSpan ρ (c.ambientFactor d i).actor
        (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype) ⊓
          (c.ambientFactor d i).space) < (c.ambientFactor d i).space →
      Nonempty (subspaceActionImage ρ (c.ambientFactor d i).space ≃*
        (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) ∨
      ∀ j : d.Index, j = i := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d π hp hs he i hdim S hproper
  rcases source_localAction_symmetricThree_proper_seed_image_cases hG T hM
    U c d π hp hs i hdim (he i).some S hproper with hsmall | hpair
  · exact Or.inl hsmall
  · exact Or.inr (source_localAction_symmetricThree_pair_image_singleton hG T hM
      U c d π hp hs he i hpair.some)
theorem source_localAction_proper_seed_pair_image
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
      ∀ i : d.Index,
      Module.finrank (ZMod 2) (d.factor i).Space = 4 →
      ((d.factor i).Carrier ≃* Equiv.Perm (Fin 3)) →
      ∀ S : Sylow 2 (subspaceStabilizer ρ (c.ambientFactor d i).space),
      Homogeneous.orbitSpan ρ (c.ambientFactor d i).actor
        (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype) ⊓
          (c.ambientFactor d i).space) < (c.ambientFactor d i).space →
      Homogeneous.orbitSpan ρ (subspaceStabilizer ρ (c.ambientFactor d i).space)
        (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype) ⊓
          (c.ambientFactor d i).space) = (c.ambientFactor d i).space →
      Nonempty (subspaceActionImage ρ (c.ambientFactor d i).space ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d π hp hs i hdim e S hproper hspan
  rcases source_localAction_symmetricThree_proper_seed_image_cases hG T hM
    U c d π hp hs i hdim e S hproper with hsmall | hpair
  · have he := (c.ambientFactor d i).symmetricThree_small_image_sylow_seed_eq e
      (c.support_stabilizer_normalizes_actor d π hp hs i) hsmall.some S
    exact (hproper.ne (he.symm.trans hspan)).elim
  · exact hpair

theorem source_localAction_proper_seed_unique_factor
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
      Module.finrank (ZMod 2) (d.factor i).Space = 4 →
      ∀ S : Sylow 2 (subspaceStabilizer ρ (c.ambientFactor d i).space),
      Homogeneous.orbitSpan ρ (c.ambientFactor d i).actor
        (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype) ⊓
          (c.ambientFactor d i).space) < (c.ambientFactor d i).space →
      Homogeneous.orbitSpan ρ (subspaceStabilizer ρ (c.ambientFactor d i).space)
        (fixedSpace ρ ((S : Subgroup (subspaceStabilizer ρ (c.ambientFactor d i).space)).map
          (subspaceStabilizer ρ (c.ambientFactor d i).space).subtype) ⊓
          (c.ambientFactor d i).space) = (c.ambientFactor d i).space →
      ∀ j : d.Index, j = i := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  dsimp only
  intro U c d π hp hs he i hdim S hproper hspan
  obtain ⟨e⟩ := source_localAction_proper_seed_pair_image hG T hM
    U c d π hp hs i hdim (he i).some S hproper hspan
  exact source_localAction_symmetricThree_pair_image_singleton hG T hM
    U c d π hp hs he i e
end CFSG.Quasithin.Chapter15.Section01
