module
public import Theory.SpecificGroups.Alternating.PositiveLocalCubicRank
public import Theory.SpecificGroups.PSL3.LinearThreeBinaryLocals
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockRealization.Algebra
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Positive local cubic rank in binary G₂ and its derived subgroup

The binary point local identifies an actual S₄ subgroup of SL₃(2). Its
normal Klein four-group supplies positive local three-rank. The Peirce block
action embeds SL₃(2) in the split-octonion automorphism group over every
characteristic-two field. Perfectness of SL₃(2) puts that whole image in
the genuine commutator subgroup, including at the smallest field.

These are the G₂ local witnesses in Aschbacher–Smith A.3.8, printed pp.45–46.
The concrete octonion block map and binary local identifications retain the
source attributions of their imported constructions.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Theory.SpecificGroups.G2.PositiveLocalCubicRank
open Matrix.PSL3.LinearThree
open Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization

private def binarySymmetric : Equiv.Perm (Fin 4) →* SL(3,ZMod 2) :=
  (pointLocalSL (ZMod 2)).subtype.comp (((binaryPointLocalEquivS4 (ZMod 2) (by simp)).symm.trans
    (pointLocalProjectEquiv (ZMod 2)).symm).toMonoidHom)

private lemma binarySymmetric_injective : Function.Injective binarySymmetric :=
  (pointLocalSL (ZMod 2)).subtype_injective.comp
    (((binaryPointLocalEquivS4 (ZMod 2) (by simp)).symm.trans
      (pointLocalProjectEquiv (ZMod 2)).symm).injective)

private theorem binary_sl_local : 1 ≤ twoLocalPrimeRank 3 SL(3,ZMod 2) :=
  Theory.Quasithin.one_le_twoLocalPrimeRank_of_a4_embedding
    (binarySymmetric.comp (alternatingGroup (Fin 4)).subtype)
    (binarySymmetric_injective.comp Subtype.val_injective)

private lemma block_injective {F : Type*} [Field F] :
    Function.Injective (blockHom (K:=F)) := by
  intro x y h
  apply Subtype.ext
  simpa only [peirceMatrix_blockHom] using congrArg
    Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.peirceMatrix h

private def binaryMap (F : Type*) [Field F] [CharP F 2] : SL(3,ZMod 2) →* Atlas.G2.Model F :=
  blockHom.comp (SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F))

private lemma binaryMap_injective (F : Type*) [Field F] [CharP F 2] :
    Function.Injective (binaryMap F) := by
  apply block_injective.comp
  intro x y h
  apply Subtype.ext
  ext i j
  exact (ZMod.castHom (dvd_refl 2) F).injective
    (congrArg (fun A : SL(3,F) => A.val i j) h)

private lemma binaryMap_range_le (F : Type*) [Field F] [CharP F 2] :
    (binaryMap F).range ≤ commutator (Atlas.G2.Model F) := by
  let : Group.IsPerfect SL(3,ZMod 2) := Atlas.sl_perfect 3 (by decide)
  have hc : (commutator SL(3,ZMod 2)).map (binaryMap F) ≤ commutator (Atlas.G2.Model F) := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  simpa only [Group.IsPerfect.commutator_eq_top,←MonoidHom.range_eq_map] using hc

private def binaryDerived (F : Type*) [Field F] [CharP F 2] :
    SL(3,ZMod 2) →* commutator (Atlas.G2.Model F) :=
  (binaryMap F).codRestrict _ (fun x => binaryMap_range_le F ⟨x,rfl⟩)

private lemma binaryDerived_injective (F : Type*) [Field F] [CharP F 2] :
    Function.Injective (binaryDerived F) := by
  intro x y h
  exact binaryMap_injective F (congrArg Subtype.val h)

/-- A perfect binary SL₃ subgroup places the A₄ witness in the actual derived G₂ carrier. -/
theorem derived {F : Type*} [Field F] [Finite F] [CharP F 2] :
    1 ≤ twoLocalPrimeRank 3 (commutator (Atlas.G2.Model F)) :=
  binary_sl_local.trans (twoLocalPrimeRank_le_of_injective 3
    (binaryDerived F) (binaryDerived_injective F))

/-- The same genuine local witness in the full split-octonion automorphism group. -/
theorem model {F : Type*} [Field F] [Finite F] [CharP F 2] :
    1 ≤ twoLocalPrimeRank 3 (Atlas.G2.Model F) :=
  (derived (F:=F)).trans (twoLocalPrimeRank_le_of_injective 3
    (commutator (Atlas.G2.Model F)).subtype Subtype.val_injective)
end Theory.SpecificGroups.G2.PositiveLocalCubicRank
