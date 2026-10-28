module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2JoinFullActor
public import Theory.Representation.G2BinaryOffenderPairGeneration

/-!
# Generation from the literal moved offender image

An actual subgroup of LT whose full actor image offends on the intrinsic
natural quotient generates L modulo O₂(LT) with one L-conjugate. The
model conjugator belongs to the derived group, so it lifts through the
original block actor. No preimage of an arbitrarily marked root eight or
assumption of full actor surjectivity is used.

This discharges the generation premise in the core-product step of
Aschbacher–Smith 3.3.28, p.601. Source offender status and the sharp index
on all of O₂(LT) remain the independent ambient inputs.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.G2BlockAction
variable {G : Type*} [Group G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual offender image supplies the literal ambient generation
premise for the source core-product theorem. -/
theorem joinFullActor_generation_of_offender
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (m : BlockModuleModel L g2TwoNaturalAction)
    (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G))
    (hoff : IsOffender (Atlas.G2.NaturalOffenders.binaryNatural (F := ZMod 2))
      ((A.subgroupOf (L ⊔ (T : Subgroup G))).map (joinFullActor hTL m))) :
    ∃ g ∈ L, L ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊔
      (A ⊔ A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨g, hg, hgen⟩ :=
    Atlas.G2.Natural.BinaryPointGeneration.offender_exists_derived_conjugate_generating
      _ hoff
  obtain ⟨k, hk⟩ := joinFullActor_two_conjugate_generation hTL m
    (A.subgroupOf (L ⊔ (T : Subgroup G))) ⟨g, hg⟩ (by rw [hgen]; exact le_top)
  rw [map_subgroupOf_eq_of_le hA] at hk
  exact ⟨k, k.property, hk⟩

end CFSG.Quasithin.ChapterC.G2BlockAction
