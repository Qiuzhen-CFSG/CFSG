/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayConstruction
public import Theory.AtlasPort.OtherSporadic.Codes.BinaryWeight

/-!
The binary Golay code is self-dual and doubly even.
Pairwise dot products of the lift and twist give self-orthogonality; dimension
and the binary overlap identity complete the arguments.

Source: `Atlas/Codes/GolayDuality.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators

theorem jWord_dot (h k : HexWord) : binaryDot (jWord h) (jWord k) = wordPolar h k := by
  rw [binaryDot_apply, Fintype.sum_prod_type, wordPolar_apply]
  exact Finset.sum_congr rfl (fun i _ => j_dot (h i) (k i))

theorem jWord_rho_dot (h : HexWord) (r : Fin 6 → Bit) : binaryDot (jWord h) (rho r) = 0 := by
  rw [binaryDot_apply, Fintype.sum_prod_type]
  change (∑ i : HexIndex, ∑ k : Fin 4, j (h i) k * r (hexIndexEquiv i)) = 0
  simp only [← Finset.sum_mul, j_sum, zero_mul, Finset.sum_const_zero]

theorem rho_dot (r s : Fin 6 → Bit) : binaryDot (rho r) (rho s) = 0 := by
  simp [binaryDot_apply, Fintype.sum_prod_type, rho, nsmul_eq_mul]

theorem eta_jWord_dot (h : HexWord) : binaryDot eta (jWord h) = 0 := by
  rw [binaryDot_apply, Fintype.sum_prod_type]
  change (∑ i : HexIndex, binaryDot (fun k => eta (i,k)) (j (h i))) = 0
  simp

theorem eta_rho_dot (r : P6) : binaryDot eta (rho r.val) = 0 := by
  rw [binaryDot_apply, Fintype.sum_prod_type]
  change (∑ i : HexIndex, ∑ k : Fin 4, eta (i,k) * r.val (hexIndexEquiv i)) = 0
  simp only [← Finset.sum_mul, eta_block_sum, one_mul]
  rw [Equiv.sum_comp hexIndexEquiv]
  exact (parityCode_mem 5 r.val).mp r.prop

theorem eta_dot_eta : binaryDot eta eta = 0 := by decide

theorem c0Encoder_dot (h k : hexacode) (r s : P6) :
    binaryDot (c0Encoder (h,r)) (c0Encoder (k,s)) = 0 := by
  have hk : wordPolar h.val k.val = 0 := by
    have hh : k.val ∈ dual hexacode := hexacode_selfDual ▸ k.prop
    exact hh h.val h.prop
  have hr : binaryDot (rho r.val) (jWord k.val) = 0 := by
    rw [binaryDot_symmetric, jWord_rho_dot]
  simp [c0Encoder, map_add, LinearMap.add_apply, jWord_dot, jWord_rho_dot, rho_dot, hk, hr]

theorem eta_c0Encoder_dot (h : hexacode) (r : P6) : binaryDot eta (c0Encoder (h,r)) = 0 := by
  simp [c0Encoder, eta_jWord_dot, eta_rho_dot]

theorem golay_selfOrthogonal : golay ≤ binaryDot.orthogonal golay := by
  rintro _ ⟨⟨h,r,ε⟩,rfl⟩ _ ⟨⟨k,s,δ⟩,rfl⟩
  have hη : binaryDot (c0Encoder (k,s)) eta = 0 := by
    rw [binaryDot_symmetric, eta_c0Encoder_dot]
  simp [golayEncoder, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    c0Encoder_dot, eta_c0Encoder_dot, eta_dot_eta, hη]

theorem golay_selfDual : golay = binaryDot.orthogonal golay := by
  apply selfDual_of_half_dimension binaryDot binaryDot_nondegenerate golay golay_selfOrthogonal
  rw [golay_finrank]
  simp [Omega, HexIndex]

theorem c0Encoder_doublyEven (h : hexacode) (r : P6) : 4 ∣ hammingNorm (c0Encoder (h,r)) := by
  change 4 ∣ hammingNorm (jWord h.val + rho r.val)
  apply doublyEven_add
  · rw [jWord_weight]
    obtain ⟨k,hk⟩ := hexacode_even h.val h.prop
    omega
  · rw [rho_weight]
    exact dvd_mul_right _ _
  · exact jWord_rho_dot _ _

theorem golay_doublyEven (w : BinaryWord) (hw : w ∈ golay) : 4 ∣ hammingNorm w := by
  obtain ⟨⟨h,r,ε⟩,rfl⟩ := hw
  rcases bit_cases ε with he | he
  · simpa [golayEncoder, he] using c0Encoder_doublyEven h r
  · simp only [golayEncoder, he, LinearMap.coe_mk, AddHom.coe_mk, one_smul]
    apply doublyEven_add _ _ (c0Encoder_doublyEven h r)
    · rw [eta_weight]; decide
    · rw [binaryDot_symmetric, eta_c0Encoder_dot]

end Atlas.Codes
