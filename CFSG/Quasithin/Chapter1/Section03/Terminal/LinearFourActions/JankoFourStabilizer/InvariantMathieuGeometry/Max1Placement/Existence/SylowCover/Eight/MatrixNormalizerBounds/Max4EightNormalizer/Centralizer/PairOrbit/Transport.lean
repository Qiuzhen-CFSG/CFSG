module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.Arithmetic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

/-!
# Transporting the thirteen kernel factors to the original max2 subgroup

Undoing the literal conjugating word identifies each local basis element with
the corresponding original `LowerBound.kernelFactor`. The proof checks only
the thirteen word expressions using homomorphism laws and group identities.
Transport then supplies exact squares, centrality, commutators and the two
generator actions in the original source subgroup. In particular the final
two theorems apply these actions to every increasing-bit source product.

This is the group-theoretic input to the independent mask-arithmetic soundness
proof. No new 112-by-112 matrix multiplication is needed.
Source: the ATLAS J4G1-max2W1 words and the certified relations retained in
TwoCoreCentralizer/NormalClosureControl/Certificates; Kleidman–Wilson (1988),
pp.484–510; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
open Janko4 Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open NormalClosureControl LowerBound

set_option linter.unusedSimpArgs false in
theorem unconjugate_basis (i : Fin 13) :
    unconjugate (basis i) = (kernelFactor i : Model) := by
  fin_cases i
  · exact unconjugate_involution.trans coe_sourceSeed_sq.symm
  · change unconjugate localSeed = ((1 : Model))⁻¹ * xyxyy ^ 11 * ((1 : Model))
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupY⁻¹ * localSeed * subgroupY) = (w14)⁻¹ * xyxyy ^ 11 * (w14)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) = (w14 * w14)⁻¹ * xyxyy ^ 11 * (w14 * w14)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) = (w14 * w14 * w10)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) = (w14 * w14 * w10 * w14)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) = (w14 * w14 * w10 * w14 * w10)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14 * w10)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) = (w14 * w14 * w10 * w14 * w14)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14 * w14)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) = (w14 * w14 * w10 * w14 * w10 * w14)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14 * w10 * w14)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) * subgroupX) = (w14 * w14 * w10 * w14 * w14 * w10)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14 * w14 * w10)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) * subgroupX) = (w14 * w14 * w10 * w14 * w10 * w14 * w10)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14 * w10 * w14 * w10)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) * subgroupY) = (w14 * w14 * w10 * w14 * w10 * w14 * w14)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14 * w10 * w14 * w14)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]
  · change unconjugate (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) * subgroupX) * subgroupY) = (w14 * w14 * w10 * w14 * w14 * w10 * w14)⁻¹ * xyxyy ^ 11 * (w14 * w14 * w10 * w14 * w14 * w10 * w14)
    simp only [map_mul, map_inv, unconjugate_seed, unconjugate_x, unconjugate_y,
      mul_inv_rev, mul_assoc, inv_one, one_mul, mul_one]

attribute [local irreducible] localSeed subgroupX subgroupY subgroupInvolution
  sourceSeed sourceX sourceY w10 w14 xyxyy

theorem unconjugate_product (m : ℕ) :
    unconjugate (maskProduct basis m) = (maskProduct kernelFactor m : sourceSubgroup) := by
  change unconjugate (maskProduct basis m) = sourceSubgroup.subtype (maskProduct kernelFactor m)
  rw [map_maskProduct, map_maskProduct]
  exact congrArg (fun e : Fin 13 → Model => maskProduct e m) (funext unconjugate_basis)

theorem source_factor_action_x (i : Fin 13) :
    sourceX⁻¹ * kernelFactor i * sourceX = maskProduct kernelFactor (Certificates.xMasks i) := by
  apply Subtype.ext
  simpa only [map_mul, map_inv, unconjugate_x, unconjugate_basis, unconjugate_product,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_sourceX] using
    congrArg unconjugate (basis_action_x i)

theorem source_factor_action_y (i : Fin 13) :
    sourceY⁻¹ * kernelFactor i * sourceY = maskProduct kernelFactor (Certificates.yMasks i) := by
  apply Subtype.ext
  simpa only [map_mul, map_inv, unconjugate_y, unconjugate_basis, unconjugate_product,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_sourceY] using
    congrArg unconjugate (basis_action_y i)

theorem commutatorForm_symm (i j : Fin 13) :
    IntrinsicCenter.commutatorForm i j = IntrinsicCenter.commutatorForm j i := by
  revert i j
  decide +kernel

theorem source_factor_commutator (i j : Fin 13) :
    kernelFactor i * kernelFactor j = kernelFactor j * kernelFactor i *
      IntrinsicCenter.bit (kernelFactor 0) (IntrinsicCenter.commutatorForm i j) := by
  apply Subtype.ext
  have hz : unconjugate subgroupInvolution = (kernelFactor 0 : Model) := unconjugate_basis 0
  simpa only [map_mul, unconjugate_basis, IntrinsicCenter.bit, apply_ite,
    hz, map_one, commutatorForm_symm j i, Subgroup.coe_mul, Subgroup.coe_one] using
    congrArg unconjugate (IntrinsicCenter.basis_twist j i)

private theorem local_succ_square (i : Fin 12) :
    basis i.succ ^ 2 = subgroupInvolution := by
  have step (g z : localSubgroup) (hz : z ^ 2 = subgroupInvolution) :
      (g⁻¹ * z * g) ^ 2 = subgroupInvolution := by
    calc
      (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by simp only [pow_two]; group
      _ = subgroupInvolution := by
        rw [hz, mul_assoc, ← (Subgroup.mem_center_iff.mp involution_mem_center) g,
          inv_mul_cancel_left]
  fin_cases i
  · change localSeed ^ 2 = subgroupInvolution
    exact localSeed_sq
  · change (subgroupY⁻¹ * localSeed * subgroupY) ^ 2 = subgroupInvolution
    exact (step subgroupY localSeed localSeed_sq)
  · change (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) ^ 2 = subgroupInvolution
    exact (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq))
  · change (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) ^ 2 = subgroupInvolution
    exact (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq)))
  · change (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) ^ 2 = subgroupInvolution
    exact (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq))))
  · change (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) ^ 2 = subgroupInvolution
    exact (step subgroupX (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq)))))
  · change (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) ^ 2 = subgroupInvolution
    exact (step subgroupY (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq)))))
  · change (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) ^ 2 = subgroupInvolution
    exact (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq))))))
  · change (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) * subgroupX) ^ 2 = subgroupInvolution
    exact (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq))))))
  · change (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) * subgroupX) ^ 2 = subgroupInvolution
    exact (step subgroupX (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq)))))))
  · change (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) * subgroupY) ^ 2 = subgroupInvolution
    exact (step subgroupY (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq)))))))
  · change (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) * subgroupX) * subgroupY) ^ 2 = subgroupInvolution
    exact (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) * subgroupY) (step subgroupY (subgroupX⁻¹ * (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) * subgroupX) (step subgroupX (subgroupY⁻¹ * (subgroupY⁻¹ * localSeed * subgroupY) * subgroupY) (step subgroupY (subgroupY⁻¹ * localSeed * subgroupY) (step subgroupY localSeed localSeed_sq)))))))

theorem source_factor_zero_square : kernelFactor 0 ^ 2 = 1 := by
  apply Subtype.ext
  have hz : unconjugate subgroupInvolution = (kernelFactor 0 : Model) := unconjugate_basis 0
  simpa only [map_pow, hz, map_one, Subgroup.coe_pow, Subgroup.coe_one] using
    congrArg unconjugate involution_pow_two

theorem source_factor_succ_square (i : Fin 12) :
    kernelFactor i.succ ^ 2 = kernelFactor 0 := by
  apply Subtype.ext
  have hz : unconjugate subgroupInvolution = (kernelFactor 0 : Model) := unconjugate_basis 0
  simpa only [map_pow, unconjugate_basis, hz, Subgroup.coe_pow] using
    congrArg unconjugate (local_succ_square i)
theorem source_product_action (g : sourceSubgroup) (f : Fin 13 → ℕ)
    (hf : ∀ i, g⁻¹ * kernelFactor i * g = maskProduct kernelFactor (f i)) (m : ℕ) :
    g⁻¹ * maskProduct kernelFactor m * g =
      maskProduct (fun i => maskProduct kernelFactor (f i)) m := by
  have hm := map_maskProduct (MulAut.conj g⁻¹).toMonoidHom kernelFactor m
  have he : (fun i => (MulAut.conj g⁻¹).toMonoidHom (kernelFactor i)) =
      (fun i => maskProduct kernelFactor (f i)) := by
    funext i
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hf i
  rw [he] at hm
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hm
theorem unconjugate_source_equiv (g : sourceSubgroup) :
    unconjugate (sourceSubgroupEquivLocal g) = (g : Model) := by
  change h * centralizerToModel (sourceSubgroupEquivLocal g) * h⁻¹ = (g : Model)
  rw [sourceSubgroupEquivLocal_apply]
  group

/-- The source's factor zero is central in the entire original max2 subgroup. -/
theorem source_factor_zero_central : kernelFactor 0 ∈ Subgroup.center sourceSubgroup := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have hz : unconjugate subgroupInvolution = (kernelFactor 0 : Model) := unconjugate_basis 0
  simpa only [map_mul, hz, unconjugate_source_equiv, Subgroup.coe_mul] using
    congrArg unconjugate
      ((Subgroup.mem_center_iff.mp involution_mem_center) (sourceSubgroupEquivLocal g))

theorem source_product_action_x (m : ℕ) :
    sourceX⁻¹ * maskProduct kernelFactor m * sourceX =
      maskProduct (fun i => maskProduct kernelFactor (Certificates.xMasks i)) m :=
  source_product_action sourceX Certificates.xMasks source_factor_action_x m

theorem source_product_action_y (m : ℕ) :
    sourceY⁻¹ * maskProduct kernelFactor m * sourceY =
      maskProduct (fun i => maskProduct kernelFactor (Certificates.yMasks i)) m :=
  source_product_action sourceY Certificates.yMasks source_factor_action_y m


end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
