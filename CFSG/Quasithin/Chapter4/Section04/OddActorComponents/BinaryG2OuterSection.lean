module
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.ActionSection
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddG2
public import Theory.SpecificGroups.G2.PositiveLocalCubicRank

/-!
# Binary G₂ outer sections in the selected component

The selected unitary residual is the derived binary G₂ group.  The public
block realization contains an injective copy of SL₃(2), so any outer section
onto the residual pulls back to an outer SL₃(2) section.  Chapter 7's complete
Theorem-B obstruction therefore supplies the exact model-specific input needed
by the original component action, without assuming solvability of every outer
automorphism group.

Source: Aschbacher--Smith 4.4.3 and 4.4.10, printed pp.619,621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04

open ChapterE
open Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization
open CFSG.Quasithin.Chapter7.NormalizedSource

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private lemma binary_block_injective {F : Type*} [Field F] :
    Function.Injective (blockHom (K := F)) := by
  intro x y h
  apply Subtype.ext
  simpa only [peirceMatrix_blockHom] using congrArg
    Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.peirceMatrix h

private def binary_block_map (F : Type*) [Field F] [CharP F 2] :
    SL(3, ZMod 2) →* Atlas.G2.Model F :=
  blockHom.comp (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F))

private lemma binary_block_map_injective (F : Type*) [Field F] [CharP F 2] :
    Function.Injective (binary_block_map F) := by
  apply binary_block_injective.comp
  intro x y h
  apply Subtype.ext
  ext i j
  exact (ZMod.castHom (dvd_refl 2) F).injective
    (congrArg (fun A : SL(3,F) => A.val i j) h)

private lemma binary_block_map_range_le (F : Type*) [Field F] [CharP F 2] :
    (binary_block_map F).range ≤ commutator (Atlas.G2.Model F) := by
  let : Group.IsPerfect SL(3, ZMod 2) := Atlas.sl_perfect 3 (by decide)
  have hc : (commutator SL(3, ZMod 2)).map (binary_block_map F) ≤
      commutator (Atlas.G2.Model F) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  simpa only [Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map] using hc

private def binary_block_derived (F : Type*) [Field F] [CharP F 2] :
    SL(3, ZMod 2) →* commutator (Atlas.G2.Model F) :=
  (binary_block_map F).codRestrict _
    (fun x => binary_block_map_range_le F ⟨x, rfl⟩)

private lemma binary_block_derived_injective (F : Type*) [Field F] [CharP F 2] :
    Function.Injective (binary_block_derived F) := by
  intro x y h
  exact binary_block_map_injective F (congrArg Subtype.val h)

private theorem no_binary_derived_outer_section
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hmodel : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    ¬ ∃ U : Subgroup (MulAut.Outer K),
      ∃ f : U →* commutator (Atlas.G2.Model (ZMod 2)), Function.Surjective f := by
  intro ho
  obtain ⟨U,f,hf⟩ := ho
  let j := binary_block_derived (ZMod 2)
  have hj : Function.Injective j := binary_block_derived_injective (ZMod 2)
  let e : SL(3, ZMod 2) ≃* j.range := MonoidHom.ofInjective hj
  let P := j.range.comap f
  let q : P →* SL(3, ZMod 2) :=
    e.symm.toMonoidHom.comp (f.subgroupComap j.range)
  have hq : Function.Surjective q := e.symm.surjective.comp
    (f.subgroupComap_surjective_of_surjective j.range hf)
  let a : P ≃* P.map U.subtype := P.equivMapOfInjective U.subtype U.subtype_injective
  let q' : P.map U.subtype →* SL(3, ZMod 2) := q.comp a.symm.toMonoidHom
  have hq' : Function.Surjective q' := hq.comp a.symm.surjective
  exact (DoubledBinaryOddG2.no_theoremB_outer_section hmodel)
    ⟨P.map U.subtype,q',hq'⟩

/-- The actual binary-G₂ residual acts inner on every selected Theorem-B
component.  The central covering kernel and the original normalizer carrier
remain in the conclusion of the general action theorem. -/
theorem chosen_oddNormalizer_inner_of_binary_derived_outer_section
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (e : inducedAutomizer V L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hmodel : ChapterA.Section02.IsTheoremBModel (K ⧸ center K)) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) := by
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    change Group.IsPerfect Atlas.G2.LieAutomorphismExtensions.BinaryDerived
    rw [Atlas.G2.LieAutomorphismExtensions.binaryDerived_eq]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsQuasisimple K := hK.2
  apply chosen_oddNormalizer_inner_of_no_action_outer_section h D hfaith e
    A hAN hcomm hodd hAV K hK
  intro U f hf
  exact no_binary_derived_outer_section hmodel ⟨U,f,hf⟩

end CFSG.Quasithin.Chapter4.Section04
