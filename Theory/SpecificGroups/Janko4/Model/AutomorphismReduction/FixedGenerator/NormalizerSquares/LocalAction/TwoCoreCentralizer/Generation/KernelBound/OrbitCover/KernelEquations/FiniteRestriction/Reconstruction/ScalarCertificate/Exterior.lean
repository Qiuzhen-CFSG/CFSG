module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.ExteriorTransport
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.ScalarCertificate.ExteriorChecks

/-! The packed exterior functional annihilates each of the 1221 actual
exterior basis forms. Kernel-checked parity evaluations extend to the entire
restricted exterior space by linearity. Source: ScalarCertificate/source/README.md. -/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
open ExteriorIndex

private theorem annihilator_check (k : Fin 1221) :
    bit (foldParity 13 (annihilatorBits &&& exteriorFormRows.get k)) 0 = 0 := by
  have hm : exteriorFormRows.get k ∈ exteriorFormRows.toList :=
    Vector.mem_toList_iff.mpr (Vector.getElem_mem k.isLt)
  have h := List.all_eq_true.mp annihilator_list _ hm
  have hf : (forcedParity 13 (annihilatorBits &&& exteriorFormRows.get k)).testBit 0 = false := by
    cases hb : (forcedParity 13 (annihilatorBits &&& exteriorFormRows.get k)).testBit 0 with
    | false => rfl
    | true => simp [hb] at h
  rw [← forcedParity_eq]
  simp only [bit, hf, Bool.false_eq_true, if_false]

set_option exponentiation.threshold 6216 in
theorem exterior_annihilated (k : Fin 1221) :
    le (restrictionForm (exteriorBasisForm k)) = 0 := by
  change pairing (decode functionalEBits) (restrictionForm (exteriorBasisForm k)) = 0
  rw [pairing_restriction, ← phi_decode]
  unfold exteriorBasisForm
  rw [pairing_upper]
  simp_rw [phi_upper_check]
  have hb : annihilatorBits &&& exteriorFormRows.get k < 2 ^ 6216 :=
    (Nat.and_le_left).trans_lt annihilator_bound
  have hbit (i : Fin 6216) : bit annihilatorBits i.val * bit (exteriorFormRows.get k) i.val =
      bit (annihilatorBits &&& exteriorFormRows.get k) i.val := by
    simp only [bit, Nat.testBit_and]
    cases annihilatorBits.testBit i.val <;>
      cases (exteriorFormRows.get k).testBit i.val <;> decide
  simp_rw [hbit]
  rw [← parity_sum _ hb (show 6216 ≤ 2 ^ 13 by decide)]
  exact annihilator_check k

/-- The checked exterior functional vanishes on the full restricted exterior space. -/
theorem le_of_mem_restrictionExteriorSpace {R : RestrictionMatrix}
    (hR : R ∈ restrictionExteriorSpace) : le R = 0 := by
  change R ∈ Submodule.span (ZMod 2)
    (Set.range (fun i : Fin 1221 => restrictionForm (exteriorBasisForm i))) at hR
  induction hR using Submodule.span_induction with
  | mem R hR => obtain ⟨i, rfl⟩ := hR; exact exterior_annihilated i
  | zero => exact map_zero le
  | add R S _ _ hR hS => rw [map_add, hR, hS, add_zero]
  | smul c R _ hR => rw [map_smul, hR, smul_zero]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.ScalarCertificate
