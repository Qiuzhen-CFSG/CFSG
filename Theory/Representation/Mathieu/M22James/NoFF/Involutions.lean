module
public import Theory.Representation.Mathieu.M22James.NoFF.GroupBounds
public import Theory.Representation.Mathieu.M22James.Unitary.Action
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.Matrix.Rank
/-!
# Involution displacement on the genuine triple Mathieu module

The native involution has displacement of rank two in the checked six-dimensional
F4 coordinates. A factorization and a two by two minor certify that rank.
Restriction of scalars doubles displacement ranks; native involution fusion
therefore gives binary displacement four for every involution in the cover.
Source: Aschbacher--Smith H.12.1(7), printed pp.393--395.
-/
public section
noncomputable section
open Sporadic.Mathieu Theory.GroupTheory
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
namespace Sporadic.Mathieu.M22TripleCover.NoFF
open Representation.SL2FourNatural Representation Representation.BinaryOffender
open Sporadic.Mathieu.M22TripleCover.Unitary
lemma binary_finrank_range (M : Matrix (Fin 6) (Fin 6) F) :
    Module.finrank (ZMod 2) (LinearMap.range (M.mulVecLin.restrictScalars (ZMod 2))) = 2 * M.rank := by
  rw [LinearMap.range_restrictScalars]
  rw [← Module.finrank_mul_finrank (ZMod 2) F]
  rw [QuadraticAlgebra.finrank_eq_two, (Submodule.restrictScalarsEquiv (ZMod 2) F _ _).finrank_eq]
  rfl
open scoped Matrix
private def bImage : Matrix (Fin 6) (Fin 2) F :=
  (!![0,2; 0,2; 3,0; 0,3; 0,1; 2,0] : Matrix _ _ ℕ).map fieldEntry
private def bFactor : Matrix (Fin 2) (Fin 6) F :=
  (!![1,1,0,3,2,0; 0,0,1,0,0,2] : Matrix _ _ ℕ).map fieldEntry
private def bLeft : Matrix (Fin 2) (Fin 6) F :=
  (!![0,0,0,0,0,3; 0,0,0,0,1,0] : Matrix _ _ ℕ).map fieldEntry
private def bRight : Matrix (Fin 6) (Fin 2) F :=
  (!![1,0; 0,0; 0,1; 0,0; 0,0; 0,0] : Matrix _ _ ℕ).map fieldEntry
lemma generatorB_rank : (generatorB - 1).rank = 2 := by
  have hf : generatorB - 1 = bImage * bFactor := by decide +kernel
  have hm : bLeft * (generatorB - 1) * bRight = 1 := by decide +kernel
  apply le_antisymm
  · calc
      (generatorB - 1).rank = (bImage * bFactor).rank := congrArg Matrix.rank hf
      _ ≤ bImage.rank := Matrix.rank_mul_le_left _ _
      _ ≤ 2 := Matrix.rank_le_width _
  · have h := (Matrix.rank_mul_le_left (bLeft * (generatorB - 1)) bRight).trans
      (Matrix.rank_mul_le_right bLeft (generatorB - 1))
    simpa only [hm, Matrix.rank_one, Fintype.card_fin] using h
lemma coreGeneratorB_order : orderOf coreGeneratorB = 2 := by
  apply orderOf_eq_prime
  · exact Subtype.ext coreB_pow_two
  · intro h
    have hmat := congrArg (fun g => (matrixAction g : Matrix (Fin 6) (Fin 6) F)) h
    rw [matrixAction_generatorB, map_one, Matrix.GeneralLinearGroup.coe_one] at hmat
    have hh := generatorB_rank
    rw [hmat, sub_self, Matrix.rank_zero] at hh
    omega
lemma binaryCodim_eq_twice_matrixRank (g : M22TripleCover) :
    fixedCodim binaryRepresentation (Subgroup.zpowers g) =
      2 * ((matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1).rank := by
  let M := (matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1
  have he : M.mulVecLin.restrictScalars (ZMod 2) =
      (binaryCoordinates.toLinearMap.comp (binaryRepresentation g - LinearMap.id)).comp
        binaryCoordinates.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := binaryCoordinates.surjective v
    change M *ᵥ binaryCoordinates w = binaryCoordinates
      (binaryRepresentation g (binaryCoordinates.symm (binaryCoordinates w)) -
        binaryCoordinates.symm (binaryCoordinates w))
    rw [binaryCoordinates.symm_apply_apply, map_sub]
    change ((matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1) *ᵥ coordinates w = _
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, matrixAction_intertwines]
    rfl
  have hr := binary_finrank_range M
  rw [he, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr binaryCoordinates.symm.surjective),
    LinearMap.range_comp, binaryCoordinates.finrank_map_eq] at hr
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hr
lemma binaryCodim_involution (g : M22TripleCover) (hg : orderOf g = 2) :
    fixedCodim binaryRepresentation (Subgroup.zpowers g) = 4 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (involutions_isConj coreGeneratorB g coreGeneratorB_order hg)
  rw [← hc, fixedCodim_zpowers_conj, binaryCodim_eq_twice_matrixRank,
    matrixAction_generatorB, generatorB_rank]
lemma matrixRank_involution (g : M22TripleCover) (hg : orderOf g = 2) :
    ((matrixAction g : Matrix (Fin 6) (Fin 6) F) - 1).rank = 2 := by
  have h := binaryCodim_involution g hg
  rw [binaryCodim_eq_twice_matrixRank] at h
  omega
end Sporadic.Mathieu.M22TripleCover.NoFF
