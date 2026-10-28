module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftEvaluation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairKernel

/-!
# Corrected native lifts of the two unprimed rows

The actual max1 words, with their left kernel corrections, are commuting
involutions in each selected row. The quotient marking and its entire fibre
are retained. These equations are the lift input to the elementary centralizer
construction, not an assertion about an arbitrary ambient centralizer.
Source: Kleidman--Wilson (1988), Figures 1/2 and Propositions 2.3.4--2.3.5.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality KernelCount KernelCount.Relations QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits Janko4.GeneratorCertificates
open SylowCore SylowCore.Transport LiftMatrices
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "ρ" => representation matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

theorem nativeMask_xor (m n : ℕ) :
    nativeMask (m ^^^ n) = nativeMask m * nativeMask n :=
  congrArg Subtype.val (maskValue_xor matrixA_mul_self matrixB_pow_four m n)

theorem nativeMask_zero : nativeMask 0 = 1 :=
  congrArg Subtype.val (maskValue_zero matrixA_mul_self matrixB_pow_four)

theorem nativeMask_square (m : ℕ) : nativeMask m * nativeMask m = 1 := by
  rw [← nativeMask_xor, Nat.xor_self, nativeMask_zero]

theorem nativeMask_commute (m n : ℕ) : Commute (nativeMask m) (nativeMask n) := by
  change nativeMask m * nativeMask n = nativeMask n * nativeMask m
  rw [← nativeMask_xor, ← nativeMask_xor, Nat.xor_comm]

theorem nativeMask_eq_maskEquiv (m : Fin 2048) : nativeMask m.val = (e m : L) := rfl

theorem nativeMask_projection (m : ℕ) : π (nativeMask m) = 1 := by
  apply MonoidHom.mem_ker.mp
  rw [starProjection_ker]
  exact (maskValue matrixA_mul_self matrixB_pow_four m).property

theorem correctedLift_projection (i : Fin 6) : π (correctedLift i) = starElement i := by
  rw [correctedLift, map_mul, nativeMask_projection, permutationLift_projection, one_mul]

theorem correctedLift_square (i : Fin 6) : correctedLift i * correctedLift i = 1 := by
  apply representation_injective matrixA_mul_self matrixB_pow_four
  rw [map_mul, map_one, representation_correctedLift]
  fin_cases i
  · exact (decoded_product square_0).trans decode_packedOne
  · exact (decoded_product square_1).trans decode_packedOne
  · exact (decoded_product square_2).trans decode_packedOne
  · exact (decoded_product square_3).trans decode_packedOne
  · exact (decoded_product square_4).trans decode_packedOne
  · exact (decoded_product square_5).trans decode_packedOne

/-- Four generators per whole row, including the Figure 1 pair permutation. -/
def correctedIndex : Fin 2 → Fin 4 → Fin 6 := ![![0,1,2,5], ![0,3,4,5]]

def correctedGenerator (r : Fin 2) (j : Fin 4) : L := correctedLift (correctedIndex r j)

private theorem decoded_commute (a b : Vector ℕ 112)
    (h : packedMul a b = packedMul b a) :
    decodeRows a * decodeRows b = decodeRows b * decodeRows a :=
  (decode_packedMul a b).symm.trans ((congrArg decodeRows h).trans (decode_packedMul b a))

private theorem corrected_commute_of_rows (i j : Fin 6)
    (h : packedMul (correctedRows i) (correctedRows j) =
      packedMul (correctedRows j) (correctedRows i)) : Commute (correctedLift i) (correctedLift j) := by
  apply representation_injective matrixA_mul_self matrixB_pow_four
  simp only [map_mul, representation_correctedLift]
  exact decoded_commute _ _ h

theorem correctedGenerator_commute (r : Fin 2) (i j : Fin 4) :
    Commute (correctedGenerator r i) (correctedGenerator r j) := by
  have h01 := corrected_commute_of_rows 0 1 commute_0_1
  have h02 := corrected_commute_of_rows 0 2 commute_0_2
  have h05 := corrected_commute_of_rows 0 5 commute_0_5
  have h12 := corrected_commute_of_rows 1 2 commute_1_2
  have h15 := corrected_commute_of_rows 1 5 commute_1_5
  have h25 := corrected_commute_of_rows 2 5 commute_2_5
  have h03 := corrected_commute_of_rows 0 3 commute_0_3
  have h04 := corrected_commute_of_rows 0 4 commute_0_4
  have h34 := corrected_commute_of_rows 3 4 commute_3_4
  have h35 := corrected_commute_of_rows 3 5 commute_3_5
  have h45 := corrected_commute_of_rows 4 5 commute_4_5
  fin_cases r <;> fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact h01
  · exact h02
  · exact h05
  · exact h01.symm
  · exact Commute.refl _
  · exact h12
  · exact h15
  · exact h02.symm
  · exact h12.symm
  · exact Commute.refl _
  · exact h25
  · exact h05.symm
  · exact h15.symm
  · exact h25.symm
  · exact Commute.refl _
  · exact Commute.refl _
  · exact h03
  · exact h04
  · exact h05
  · exact h03.symm
  · exact Commute.refl _
  · exact h34
  · exact h35
  · exact h04.symm
  · exact h34.symm
  · exact Commute.refl _
  · exact h45
  · exact h05.symm
  · exact h35.symm
  · exact h45.symm
  · exact Commute.refl _

theorem correctedGenerator_square (r : Fin 2) (j : Fin 4) :
    correctedGenerator r j * correctedGenerator r j = 1 :=
  correctedLift_square _

theorem correctedGenerator_projection (r : Fin 2) (j : Fin 4) :
    π (correctedGenerator r j) = pairRowGenerator (r.castLE (by decide)) j := by
  rw [correctedGenerator, correctedLift_projection]
  fin_cases r <;> fin_cases j <;> rfl

/-- Every lift of the marked permutation has a unique bounded left kernel coordinate. -/
theorem correctedLift_fibre (i : Fin 6) (x : L) :
    π x = starElement i ↔ ∃! m : Fin 2048, x = nativeMask m.val * correctedLift i := by
  constructor
  · intro hx
    have hk : x * (correctedLift i)⁻¹ ∈ E := by
      rw [← starProjection_ker, MonoidHom.mem_ker, map_mul, map_inv,
        correctedLift_projection, hx, mul_inv_cancel]
    obtain ⟨m,hm⟩ := (e).surjective ⟨x * (correctedLift i)⁻¹,hk⟩
    have hv : nativeMask m.val = x * (correctedLift i)⁻¹ := congrArg Subtype.val hm
    refine ⟨m, ?_, ?_⟩
    · change x = nativeMask m.val * correctedLift i
      rw [hv, inv_mul_cancel_right]
    · intro n hn
      apply (e).injective
      apply Subtype.ext
      change nativeMask n.val = nativeMask m.val
      apply mul_right_cancel (b := correctedLift i)
      rw [← hn, hv, inv_mul_cancel_right]
  · rintro ⟨m,hm,_⟩
    rw [hm, map_mul, correctedLift_projection, nativeMask_projection, one_mul]

/-- The literal left-conjugation action on every bounded kernel coordinate. -/
theorem correctedLift_mask_mul (i : Fin 6) (m : Fin 2048) :
    correctedLift i * nativeMask m.val =
      nativeMask (starMask (starElement i) m.val) * correctedLift i := by
  have h := congrArg (fun z : E => (z : L))
    (maskEquiv_starMask matrixA_mul_self matrixB_pow_four (correctedLift i) m)
  change nativeMask (starMask (π (correctedLift i)) m.val) =
    correctedLift i * nativeMask m.val * (correctedLift i)⁻¹ at h
  rw [correctedLift_projection] at h
  rw [h, inv_mul_cancel_right]

end Janko4.LocalStructure.ElementaryEightGeometry
