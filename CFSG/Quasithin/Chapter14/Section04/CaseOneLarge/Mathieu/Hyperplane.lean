module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit

/-!
# The native Mathieu Sylow hyperplane

Eleven columns of the six certified Sylow displacement operators have an
explicit decoder. Its product is the identity minus the projection defined
by the polar functional at the marked point. Thus these displacements span
the perpendicular hyperplane. A binary linear-functional argument shows that
this is the unique proper subspace containing all those displacements.

This identifies the original plane centralizer in the Mathieu branch from
Sylow normalization alone, without an additional invariant-form marking.
Source: Aschbacher--Smith, H.12.1(9) and 14.4.12, pp.393--394,1011--1012.
The imported native ATLAS matrices retain their attribution; the small
column and decoder certificates below are verified by the Lean kernel.
-/

public noncomputable section
open Matrix Subgroup Representation.BinaryOffender
open Sporadic.Mathieu M22TripleCover M22TripleCover.Unitary
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open LargerDimension.Mathieu.ModuleGeometry.Native
open SylowCertificates

private def movedColumns : Matrix12 :=
  fromRows ![984,1388,1701,779,368,1986,621,115,552,1277,1039,627]
private def movedDecoder : Matrix12 :=
  fromRows ![108,1000,1062,2072,1942,408,1290,1772,788,2176,3002,2045]
private def pointRow : Matrix (Fin 1) (Fin 12) (ZMod 2) :=
  fun _ j => if (2045 : ℕ).testBit j.val then 1 else 0
private def pointFunctional : BinarySpace →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj 0).comp pointRow.mulVecLin
private def pointProjection : Matrix12 := fun i j => if i = 0 then pointRow 0 j else 0
private def chosenActor : Fin 11 → Fin 6 := ![0,0,0,0,0,0,1,1,2,3,5]
private def chosenColumn : Fin 11 → Fin 12 := ![0,1,2,3,4,7,0,1,0,4,0]

private theorem movedColumns_eq : ∀ (i : Fin 12) (j : Fin 11),
    movedColumns i j.castSucc =
      (generatorMatrix (chosenActor j) - 1) i (chosenColumn j) := by decide +kernel
private theorem movedColumns_last : ∀ i, movedColumns i 11 = 0 := by decide +kernel
private theorem moved_decode : movedColumns * movedDecoder = 1 - pointProjection := by decide +kernel

private theorem marked_functional : quadraticForm.polarBilin markedVector = pointFunctional := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply]
  change ((hermitianForm (markedVector + Pi.single i 1) (markedVector + Pi.single i 1)).re -
    (hermitianForm markedVector markedVector).re -
    (hermitianForm (Pi.single i 1) (Pi.single i 1)).re) = _
  change ((hermitianBinary (markedVector + Pi.single i 1) (markedVector + Pi.single i 1)).re -
    (hermitianBinary markedVector markedVector).re -
    (hermitianBinary (Pi.single i 1) (Pi.single i 1)).re) = _
  revert i
  decide +kernel

/-- Eleven native Sylow displacements span the literal perpendicular hyperplane. -/
theorem mathieu_markedPerp_le_sylow_moved :
    markedPerp ≤ subspaceCommutator representation ⊤ markedSylow := by
  intro v hv
  let M := subspaceCommutator representation ⊤ (markedSylow : Subgroup Group)
  have hcol (j : Fin 12) : (fun i => movedColumns i j) ∈ M := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · have hz : (fun i => movedColumns i (Fin.last 11)) = 0 := funext movedColumns_last
      rw [hz]
      exact M.zero_mem
    · have hg : generator (chosenActor j) ∈ (markedSylow : Subgroup Group) := by
        rw [markedSylow_coe]
        exact subset_closure ⟨_,rfl⟩
      have hm : representation (generator (chosenActor j)) (Pi.single (chosenColumn j) 1) -
          Pi.single (chosenColumn j) 1 ∈ M :=
        Submodule.subset_span ⟨_,hg,_,Submodule.mem_top,rfl⟩
      have he : representation (generator (chosenActor j)) (Pi.single (chosenColumn j) 1) -
          Pi.single (chosenColumn j) 1 = (fun i => movedColumns i j.castSucc) := by
        change ((generator (chosenActor j) : Matrix12ˣ) : Matrix12) *ᵥ
          Pi.single (chosenColumn j) 1 - Pi.single (chosenColumn j) 1 = _
        rw [generator_matrix]
        ext i
        rw [movedColumns_eq]
        simp [Pi.single_apply,Matrix.one_apply]
      exact he ▸ hm
  have hmul : movedColumns *ᵥ (movedDecoder *ᵥ v) ∈ M := by
    have hh := M.sum_mem (t:=Finset.univ) (f:=fun j => (movedDecoder *ᵥ v) j •
      (fun i => movedColumns i j)) (fun j _ => M.smul_mem _ (hcol j))
    convert hh using 1
    ext i
    simp only [mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  have hz : pointFunctional v = 0 := by
    change quadraticForm.polarBilin markedVector v = 0 at hv
    rwa [marked_functional] at hv
  have hp : pointProjection *ᵥ v = 0 := by
    ext i
    by_cases hi : i = 0
    · subst i
      exact hz
    · simp [pointProjection,mulVec,dotProduct,hi]
  rw [mulVec_mulVec,moved_decode,Matrix.sub_mulVec,one_mulVec,hp,sub_zero] at hmul
  exact hmul

/-- The native perpendicular hyperplane is maximal among proper subspaces. -/
theorem mathieu_markedPerp_eq_of_le (P : Submodule (ZMod 2) BinarySpace)
    (hle : markedPerp ≤ P) (hne : P ≠ ⊤) : P = markedPerp := by
  apply le_antisymm ?_ hle
  intro v hv
  change quadraticForm.polarBilin markedVector v = 0
  rw [marked_functional]
  by_contra hzero
  have hone : pointFunctional v = 1 :=
    ((show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) _).resolve_left hzero
  apply hne
  apply top_unique
  intro w _
  have hw : w - pointFunctional w • v ∈ markedPerp := by
    change quadraticForm.polarBilin markedVector (w - pointFunctional w • v) = 0
    rw [marked_functional,map_sub,map_smul,hone,smul_eq_mul,mul_one,sub_self]
  have hh := P.add_mem (hle hw) (P.smul_mem (pointFunctional w) hv)
  simpa only [sub_add_cancel] using hh

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
