module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed
public import Theory.Representation.BinaryOffender.ProjectedSeed

/-!
# Projected seeds in the actual selected local action

The source Sylow-fixed central seed spans V(M) under the original faithful
local image. Any surjective equivariant projection retains this property and
therefore has faithful image with trivial two-core. In particular the actual
residual action on C_V(Y), for a normal odd Y, has trivial two-core through
the coprime fixed/moved projection.

These are applications of `source_localAction_seed_span` with its literal
conjugation image, prescribed Sylow image, and original central seed. They
supply the residual two-core input in the first paragraph of original 15.1.2;
neither solvability nor full Fitting movement is added to the source premises.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 15.1.2,
printed pp.1084–1085 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterD ChapterD.UniqueFactor ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_projected_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
      (σ : Representation (ZMod 2) D W) (e : Additive V →ₗ[ZMod 2] W),
      (∀ g v, e (ρ g v) = σ g (e v)) → Function.Surjective e →
      pCore 2 (Representation.BinaryOffender.actionImage σ) = ⊥ := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro V D ρ W _ _ σ e hact he
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  exact projected_actionImage_twoCore σ e hact he _ _ hfix hspan

theorem source_localAction_oddFixed_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (Y : Subgroup D) [Y.Normal], Odd (Nat.card Y) →
      pCore 2 (subspaceActionImage ρ (fixedSpace ρ Y)) = ⊥ := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  intro V D ρ Y _ hodd
  obtain ⟨hfix,hspan⟩ := source_localAction_seed_span hG T hM
  exact normalOddFixedImage_twoCore ρ Y hodd _ _ hfix hspan

end CFSG.Quasithin.Chapter15.Section01
