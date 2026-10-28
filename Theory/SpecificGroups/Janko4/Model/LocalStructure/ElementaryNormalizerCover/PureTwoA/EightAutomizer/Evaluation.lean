module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks12
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Words
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Coordinates
/-!
# Checked action of the three literal native automizer words

Every packed product is transported through the faithful native representation.
The final conjugation equations use exactly the finite automizer's bit masks,
so words in those three finite actions lift to words in the actual F-normalizer.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/
public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open GeneratorCertificates Cardinality.KernelCount Cardinality.KernelCount.Relations
open ElementaryEightGeometry
attribute [local irreducible] modelGroup matrixA matrixB
private theorem eval_x : toMatrix sourceX = decodeRows xRows := representation_x _ _
private theorem eval_y : toMatrix sourceY = decodeRows yRows := representation_y _ _
private theorem eval_n0 : toMatrix LinearFive.NativeNormalizer.n0 =
    decodeRows LinearFive.NativeNormalizer.n0Rows := LinearFive.NativeNormalizer.eval_n0
private theorem eval_n1 : toMatrix LinearFive.NativeNormalizer.n1 =
    decodeRows LinearFive.NativeNormalizer.n1Rows := LinearFive.NativeNormalizer.eval_n1
private theorem eval_a : toMatrix Janko4.a = decodeRows Janko4.aRows := by
  simpa only [matrixA] using toMatrix_a
private theorem eval_mask1 : toMatrix (Loewy.maskElement 1) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) := by
  rw [show (1 : Mask) = bitBasis 0 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 0
private theorem eval_mask2 : toMatrix (Loewy.maskElement 2) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) := by
  rw [show (2 : Mask) = bitBasis 1 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 1
private theorem eval_mask4 : toMatrix (Loewy.maskElement 4) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) := by
  rw [show (4 : Mask) = bitBasis 2 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 2
private theorem eval_mask8 : toMatrix (Loewy.maskElement 8) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) := by
  rw [show (8 : Mask) = bitBasis 3 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 3
private theorem eval_mask16 : toMatrix (Loewy.maskElement 16) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) := by
  rw [show (16 : Mask) = bitBasis 4 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 4
private theorem eval_mask32 : toMatrix (Loewy.maskElement 32) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) := by
  rw [show (32 : Mask) = bitBasis 5 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 5
private theorem eval_mask64 : toMatrix (Loewy.maskElement 64) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) := by
  rw [show (64 : Mask) = bitBasis 6 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 6
private theorem eval_mask128 : toMatrix (Loewy.maskElement 128) = decodeRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) := by
  rw [show (128 : Mask) = bitBasis 7 from rfl, maskElement_basis]
  exact Loewy.toMatrix_nativeGenerator 7
theorem eval_xy : toMatrix xy = decodeRows xyRows :=
  eval_mul toMatrix eval_x eval_y (decoded_product check_xy)
theorem eval_xyy : toMatrix xyy = decodeRows xyyRows :=
  eval_mul toMatrix eval_xy eval_y (decoded_product check_xyy)
theorem eval_p2 : toMatrix p2 = decodeRows p2Rows :=
  eval_mul toMatrix eval_xyy eval_xyy (decoded_product check_p2)
theorem eval_p4 : toMatrix p4 = decodeRows p4Rows :=
  eval_mul toMatrix eval_p2 eval_p2 (decoded_product check_p4)
theorem eval_cx : toMatrix cx = decodeRows cxRows :=
  eval_mul toMatrix eval_p4 eval_x (decoded_product check_cx)
theorem eval_cxy : toMatrix cxy = decodeRows cxyRows :=
  eval_mul toMatrix eval_cx eval_y (decoded_product check_cxy)
theorem eval_cxyx : toMatrix cxyx = decodeRows cxyxRows :=
  eval_mul toMatrix eval_cxy eval_x (decoded_product check_cxyx)
theorem eval_c : toMatrix c = decodeRows cRows :=
  eval_mul toMatrix eval_cxyx (Loewy.toMatrix_nativeGenerator 0) (decoded_product check_c)
theorem eval_ci : toMatrix ci = decodeRows ciRows :=
  eval_inv toMatrix eval_c (by rw [decoded_product check_inverse_ci, decode_packedOne])
theorem eval_n0i : toMatrix n0i = decodeRows n0iRows :=
  eval_inv toMatrix eval_n0 (by rw [decoded_product check_inverse_n0i, decode_packedOne])
theorem eval_n1i : toMatrix n1i = decodeRows n1iRows :=
  eval_inv toMatrix eval_n1 (by rw [decoded_product check_inverse_n1i, decode_packedOne])
theorem eval_cu0 : toMatrix cu0 = decodeRows cu0Rows :=
  eval_mul toMatrix eval_c eval_n0 (decoded_product check_cu0)
theorem eval_actor0 : toMatrix actor0 = decodeRows actor0Rows :=
  eval_mul toMatrix eval_cu0 eval_ci (decoded_product check_actor0)
theorem eval_u1_0 : toMatrix u1_0 = decodeRows u1_0Rows :=
  eval_mul toMatrix eval_n1i eval_n1i (decoded_product check_u1_0)
theorem eval_u1_1 : toMatrix u1_1 = decodeRows u1_1Rows :=
  eval_mul toMatrix eval_u1_0 eval_n1i (decoded_product check_u1_1)
theorem eval_u1_2 : toMatrix u1_2 = decodeRows u1_2Rows :=
  eval_mul toMatrix eval_u1_1 eval_n0 (decoded_product check_u1_2)
theorem eval_u1_3 : toMatrix u1_3 = decodeRows u1_3Rows :=
  eval_mul toMatrix eval_u1_2 eval_n1 (decoded_product check_u1_3)
theorem eval_u1_4 : toMatrix u1_4 = decodeRows u1_4Rows :=
  eval_mul toMatrix eval_u1_3 eval_n1 (decoded_product check_u1_4)
theorem eval_u1_5 : toMatrix u1_5 = decodeRows u1_5Rows :=
  eval_mul toMatrix eval_u1_4 eval_n1 (decoded_product check_u1_5)
theorem eval_cu1 : toMatrix cu1 = decodeRows cu1Rows :=
  eval_mul toMatrix eval_c eval_u1_5 (decoded_product check_cu1)
theorem eval_actor1 : toMatrix actor1 = decodeRows actor1Rows :=
  eval_mul toMatrix eval_cu1 eval_ci (decoded_product check_actor1)
theorem eval_u2_0 : toMatrix u2_0 = decodeRows u2_0Rows :=
  eval_mul toMatrix eval_n1i eval_n0i (decoded_product check_u2_0)
theorem eval_u2_1 : toMatrix u2_1 = decodeRows u2_1Rows :=
  eval_mul toMatrix eval_u2_0 eval_n1i (decoded_product check_u2_1)
theorem eval_u2_2 : toMatrix u2_2 = decodeRows u2_2Rows :=
  eval_mul toMatrix eval_u2_1 eval_n0i (decoded_product check_u2_2)
theorem eval_u2_3 : toMatrix u2_3 = decodeRows u2_3Rows :=
  eval_mul toMatrix eval_u2_2 eval_n1 (decoded_product check_u2_3)
theorem eval_u2_4 : toMatrix u2_4 = decodeRows u2_4Rows :=
  eval_mul toMatrix eval_u2_3 eval_n0 (decoded_product check_u2_4)
theorem eval_u2_5 : toMatrix u2_5 = decodeRows u2_5Rows :=
  eval_mul toMatrix eval_u2_4 eval_n1 (decoded_product check_u2_5)
theorem eval_u2_6 : toMatrix u2_6 = decodeRows u2_6Rows :=
  eval_mul toMatrix eval_u2_5 eval_n0 (decoded_product check_u2_6)
theorem eval_u2_7 : toMatrix u2_7 = decodeRows u2_7Rows :=
  eval_mul toMatrix eval_u2_6 eval_n1 (decoded_product check_u2_7)
theorem eval_cu2 : toMatrix cu2 = decodeRows cu2Rows :=
  eval_mul toMatrix eval_c eval_u2_7 (decoded_product check_cu2)
theorem eval_actor2 : toMatrix actor2 = decodeRows actor2Rows :=
  eval_mul toMatrix eval_cu2 eval_ci (decoded_product check_actor2)
private theorem eval_mask20 : toMatrix (Loewy.maskElement 20) = decodeRows m20Rows := by
  rw [show Loewy.maskElement 20 = Loewy.maskElement 4 * Loewy.maskElement 16 from maskElement_xor 4 16]
  exact eval_mul toMatrix eval_mask4 eval_mask16 (decoded_product check_m20)
private theorem eval_mask52 : toMatrix (Loewy.maskElement 52) = decodeRows m52Rows := by
  rw [show Loewy.maskElement 52 = Loewy.maskElement 20 * Loewy.maskElement 32 from maskElement_xor 20 32]
  exact eval_mul toMatrix eval_mask20 eval_mask32 (decoded_product check_m52)
private theorem eval_mask17 : toMatrix (Loewy.maskElement 17) = decodeRows m17Rows := by
  rw [show Loewy.maskElement 17 = Loewy.maskElement 1 * Loewy.maskElement 16 from maskElement_xor 1 16]
  exact eval_mul toMatrix eval_mask1 eval_mask16 (decoded_product check_m17)
private theorem eval_mask49 : toMatrix (Loewy.maskElement 49) = decodeRows m49Rows := by
  rw [show Loewy.maskElement 49 = Loewy.maskElement 17 * Loewy.maskElement 32 from maskElement_xor 17 32]
  exact eval_mul toMatrix eval_mask17 eval_mask32 (decoded_product check_m49)
private theorem eval_mask177 : toMatrix (Loewy.maskElement 177) = decodeRows m177Rows := by
  rw [show Loewy.maskElement 177 = Loewy.maskElement 49 * Loewy.maskElement 128 from maskElement_xor 49 128]
  exact eval_mul toMatrix eval_mask49 eval_mask128 (decoded_product check_m177)
private theorem eval_mask3 : toMatrix (Loewy.maskElement 3) = decodeRows m3Rows := by
  rw [show Loewy.maskElement 3 = Loewy.maskElement 1 * Loewy.maskElement 2 from maskElement_xor 1 2]
  exact eval_mul toMatrix eval_mask1 eval_mask2 (decoded_product check_m3)
private theorem eval_mask7 : toMatrix (Loewy.maskElement 7) = decodeRows m7Rows := by
  rw [show Loewy.maskElement 7 = Loewy.maskElement 3 * Loewy.maskElement 4 from maskElement_xor 3 4]
  exact eval_mul toMatrix eval_mask3 eval_mask4 (decoded_product check_m7)
private theorem eval_mask23 : toMatrix (Loewy.maskElement 23) = decodeRows m23Rows := by
  rw [show Loewy.maskElement 23 = Loewy.maskElement 7 * Loewy.maskElement 16 from maskElement_xor 7 16]
  exact eval_mul toMatrix eval_mask7 eval_mask16 (decoded_product check_m23)
private theorem eval_mask55 : toMatrix (Loewy.maskElement 55) = decodeRows m55Rows := by
  rw [show Loewy.maskElement 55 = Loewy.maskElement 23 * Loewy.maskElement 32 from maskElement_xor 23 32]
  exact eval_mul toMatrix eval_mask23 eval_mask32 (decoded_product check_m55)
private theorem eval_mask183 : toMatrix (Loewy.maskElement 183) = decodeRows m183Rows := by
  rw [show Loewy.maskElement 183 = Loewy.maskElement 55 * Loewy.maskElement 128 from maskElement_xor 55 128]
  exact eval_mul toMatrix eval_mask55 eval_mask128 (decoded_product check_m183)
private theorem eval_mask11 : toMatrix (Loewy.maskElement 11) = decodeRows m11Rows := by
  rw [show Loewy.maskElement 11 = Loewy.maskElement 3 * Loewy.maskElement 8 from maskElement_xor 3 8]
  exact eval_mul toMatrix eval_mask3 eval_mask8 (decoded_product check_m11)
private theorem eval_mask27 : toMatrix (Loewy.maskElement 27) = decodeRows m27Rows := by
  rw [show Loewy.maskElement 27 = Loewy.maskElement 11 * Loewy.maskElement 16 from maskElement_xor 11 16]
  exact eval_mul toMatrix eval_mask11 eval_mask16 (decoded_product check_m27)
private theorem eval_mask59 : toMatrix (Loewy.maskElement 59) = decodeRows m59Rows := by
  rw [show Loewy.maskElement 59 = Loewy.maskElement 27 * Loewy.maskElement 32 from maskElement_xor 27 32]
  exact eval_mul toMatrix eval_mask27 eval_mask32 (decoded_product check_m59)
private theorem eval_mask187 : toMatrix (Loewy.maskElement 187) = decodeRows m187Rows := by
  rw [show Loewy.maskElement 187 = Loewy.maskElement 59 * Loewy.maskElement 128 from maskElement_xor 59 128]
  exact eval_mul toMatrix eval_mask59 eval_mask128 (decoded_product check_m187)
private theorem eval_mask5 : toMatrix (Loewy.maskElement 5) = decodeRows m5Rows := by
  rw [show Loewy.maskElement 5 = Loewy.maskElement 1 * Loewy.maskElement 4 from maskElement_xor 1 4]
  exact eval_mul toMatrix eval_mask1 eval_mask4 (decoded_product check_m5)
private theorem eval_mask37 : toMatrix (Loewy.maskElement 37) = decodeRows m37Rows := by
  rw [show Loewy.maskElement 37 = Loewy.maskElement 5 * Loewy.maskElement 32 from maskElement_xor 5 32]
  exact eval_mul toMatrix eval_mask5 eval_mask32 (decoded_product check_m37)
private theorem eval_mask19 : toMatrix (Loewy.maskElement 19) = decodeRows m19Rows := by
  rw [show Loewy.maskElement 19 = Loewy.maskElement 3 * Loewy.maskElement 16 from maskElement_xor 3 16]
  exact eval_mul toMatrix eval_mask3 eval_mask16 (decoded_product check_m19)
private theorem eval_mask147 : toMatrix (Loewy.maskElement 147) = decodeRows m147Rows := by
  rw [show Loewy.maskElement 147 = Loewy.maskElement 19 * Loewy.maskElement 128 from maskElement_xor 19 128]
  exact eval_mul toMatrix eval_mask19 eval_mask128 (decoded_product check_m147)
private theorem eval_mask51 : toMatrix (Loewy.maskElement 51) = decodeRows m51Rows := by
  rw [show Loewy.maskElement 51 = Loewy.maskElement 19 * Loewy.maskElement 32 from maskElement_xor 19 32]
  exact eval_mul toMatrix eval_mask19 eval_mask32 (decoded_product check_m51)
private theorem eval_mask115 : toMatrix (Loewy.maskElement 115) = decodeRows m115Rows := by
  rw [show Loewy.maskElement 115 = Loewy.maskElement 51 * Loewy.maskElement 64 from maskElement_xor 51 64]
  exact eval_mul toMatrix eval_mask51 eval_mask64 (decoded_product check_m115)
private theorem eval_mask243 : toMatrix (Loewy.maskElement 243) = decodeRows m243Rows := by
  rw [show Loewy.maskElement 243 = Loewy.maskElement 115 * Loewy.maskElement 128 from maskElement_xor 115 128]
  exact eval_mul toMatrix eval_mask115 eval_mask128 (decoded_product check_m243)
private theorem eval_mask12 : toMatrix (Loewy.maskElement 12) = decodeRows m12Rows := by
  rw [show Loewy.maskElement 12 = Loewy.maskElement 4 * Loewy.maskElement 8 from maskElement_xor 4 8]
  exact eval_mul toMatrix eval_mask4 eval_mask8 (decoded_product check_m12)
private theorem eval_mask28 : toMatrix (Loewy.maskElement 28) = decodeRows m28Rows := by
  rw [show Loewy.maskElement 28 = Loewy.maskElement 12 * Loewy.maskElement 16 from maskElement_xor 12 16]
  exact eval_mul toMatrix eval_mask12 eval_mask16 (decoded_product check_m28)
private theorem eval_mask60 : toMatrix (Loewy.maskElement 60) = decodeRows m60Rows := by
  rw [show Loewy.maskElement 60 = Loewy.maskElement 28 * Loewy.maskElement 32 from maskElement_xor 28 32]
  exact eval_mul toMatrix eval_mask28 eval_mask32 (decoded_product check_m60)
private theorem eval_mask188 : toMatrix (Loewy.maskElement 188) = decodeRows m188Rows := by
  rw [show Loewy.maskElement 188 = Loewy.maskElement 60 * Loewy.maskElement 128 from maskElement_xor 60 128]
  exact eval_mul toMatrix eval_mask60 eval_mask128 (decoded_product check_m188)
private theorem eval_mask10 : toMatrix (Loewy.maskElement 10) = decodeRows m10Rows := by
  rw [show Loewy.maskElement 10 = Loewy.maskElement 2 * Loewy.maskElement 8 from maskElement_xor 2 8]
  exact eval_mul toMatrix eval_mask2 eval_mask8 (decoded_product check_m10)
private theorem eval_mask26 : toMatrix (Loewy.maskElement 26) = decodeRows m26Rows := by
  rw [show Loewy.maskElement 26 = Loewy.maskElement 10 * Loewy.maskElement 16 from maskElement_xor 10 16]
  exact eval_mul toMatrix eval_mask10 eval_mask16 (decoded_product check_m26)
private theorem eval_mask58 : toMatrix (Loewy.maskElement 58) = decodeRows m58Rows := by
  rw [show Loewy.maskElement 58 = Loewy.maskElement 26 * Loewy.maskElement 32 from maskElement_xor 26 32]
  exact eval_mul toMatrix eval_mask26 eval_mask32 (decoded_product check_m58)
private theorem eval_mask186 : toMatrix (Loewy.maskElement 186) = decodeRows m186Rows := by
  rw [show Loewy.maskElement 186 = Loewy.maskElement 58 * Loewy.maskElement 128 from maskElement_xor 58 128]
  exact eval_mul toMatrix eval_mask58 eval_mask128 (decoded_product check_m186)
private theorem eval_mask48 : toMatrix (Loewy.maskElement 48) = decodeRows m48Rows := by
  rw [show Loewy.maskElement 48 = Loewy.maskElement 16 * Loewy.maskElement 32 from maskElement_xor 16 32]
  exact eval_mul toMatrix eval_mask16 eval_mask32 (decoded_product check_m48)
private theorem eval_mask176 : toMatrix (Loewy.maskElement 176) = decodeRows m176Rows := by
  rw [show Loewy.maskElement 176 = Loewy.maskElement 48 * Loewy.maskElement 128 from maskElement_xor 48 128]
  exact eval_mul toMatrix eval_mask48 eval_mask128 (decoded_product check_m176)
private theorem eval_mask6 : toMatrix (Loewy.maskElement 6) = decodeRows m6Rows := by
  rw [show Loewy.maskElement 6 = Loewy.maskElement 2 * Loewy.maskElement 4 from maskElement_xor 2 4]
  exact eval_mul toMatrix eval_mask2 eval_mask4 (decoded_product check_m6)
private theorem eval_mask22 : toMatrix (Loewy.maskElement 22) = decodeRows m22Rows := by
  rw [show Loewy.maskElement 22 = Loewy.maskElement 6 * Loewy.maskElement 16 from maskElement_xor 6 16]
  exact eval_mul toMatrix eval_mask6 eval_mask16 (decoded_product check_m22)
private theorem eval_mask13 : toMatrix (Loewy.maskElement 13) = decodeRows m13Rows := by
  rw [show Loewy.maskElement 13 = Loewy.maskElement 5 * Loewy.maskElement 8 from maskElement_xor 5 8]
  exact eval_mul toMatrix eval_mask5 eval_mask8 (decoded_product check_m13)
private theorem eval_mask29 : toMatrix (Loewy.maskElement 29) = decodeRows m29Rows := by
  rw [show Loewy.maskElement 29 = Loewy.maskElement 13 * Loewy.maskElement 16 from maskElement_xor 13 16]
  exact eval_mul toMatrix eval_mask13 eval_mask16 (decoded_product check_m29)
private theorem eval_mask36 : toMatrix (Loewy.maskElement 36) = decodeRows m36Rows := by
  rw [show Loewy.maskElement 36 = Loewy.maskElement 4 * Loewy.maskElement 32 from maskElement_xor 4 32]
  exact eval_mul toMatrix eval_mask4 eval_mask32 (decoded_product check_m36)
private theorem eval_mask100 : toMatrix (Loewy.maskElement 100) = decodeRows m100Rows := by
  rw [show Loewy.maskElement 100 = Loewy.maskElement 36 * Loewy.maskElement 64 from maskElement_xor 36 64]
  exact eval_mul toMatrix eval_mask36 eval_mask64 (decoded_product check_m100)
private theorem eval_mask228 : toMatrix (Loewy.maskElement 228) = decodeRows m228Rows := by
  rw [show Loewy.maskElement 228 = Loewy.maskElement 100 * Loewy.maskElement 128 from maskElement_xor 100 128]
  exact eval_mul toMatrix eval_mask100 eval_mask128 (decoded_product check_m228)
private theorem eval_mask61 : toMatrix (Loewy.maskElement 61) = decodeRows m61Rows := by
  rw [show Loewy.maskElement 61 = Loewy.maskElement 29 * Loewy.maskElement 32 from maskElement_xor 29 32]
  exact eval_mul toMatrix eval_mask29 eval_mask32 (decoded_product check_m61)
private theorem eval_mask189 : toMatrix (Loewy.maskElement 189) = decodeRows m189Rows := by
  rw [show Loewy.maskElement 189 = Loewy.maskElement 61 * Loewy.maskElement 128 from maskElement_xor 61 128]
  exact eval_mul toMatrix eval_mask61 eval_mask128 (decoded_product check_m189)
private theorem eval_mask101 : toMatrix (Loewy.maskElement 101) = decodeRows m101Rows := by
  rw [show Loewy.maskElement 101 = Loewy.maskElement 37 * Loewy.maskElement 64 from maskElement_xor 37 64]
  exact eval_mul toMatrix eval_mask37 eval_mask64 (decoded_product check_m101)
private theorem eval_mask74 : toMatrix (Loewy.maskElement 74) = decodeRows m74Rows := by
  rw [show Loewy.maskElement 74 = Loewy.maskElement 10 * Loewy.maskElement 64 from maskElement_xor 10 64]
  exact eval_mul toMatrix eval_mask10 eval_mask64 (decoded_product check_m74)
theorem eval_ag : toMatrix ag = decodeRows agRows :=
  eval_mul toMatrix eval_a (Loewy.toMatrix_nativeGenerator 6) (decoded_product check_ag)
theorem eval_ag2 : toMatrix ag2 = decodeRows ag2Rows :=
  eval_mul toMatrix eval_ag eval_ag (decoded_product check_ag2)
theorem eval_ag4 : toMatrix ag4 = decodeRows ag4Rows :=
  eval_mul toMatrix eval_ag2 eval_ag2 (decoded_product check_ag4)
theorem eval_ag8 : toMatrix ag8 = decodeRows ag8Rows :=
  eval_mul toMatrix eval_ag4 eval_ag4 (decoded_product check_ag8)
theorem eval_ag10 : toMatrix ag10 = decodeRows ag10Rows :=
  eval_mul toMatrix eval_ag8 eval_ag2 (decoded_product check_ag10)

private theorem conjugate_of_matrix {g x y : Model} {rg rx ry : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rg) (hx : toMatrix x = decodeRows rx)
    (hy : toMatrix y = decodeRows ry) (hc : packedMul rg rx = packedMul ry rg) :
    g * x * g⁻¹ = y := by
  have h : toMatrix g * toMatrix x = toMatrix y * toMatrix g := by
    rw [hg,hx,hy,← decode_packedMul,← decode_packedMul,hc]
  apply toMatrix_injective
  rw [map_mul,map_mul,h,mul_assoc,← map_mul,mul_inv_cancel,map_one,mul_one]

theorem actor_conjugates (i : Fin 3) (j : Fin 8) :
    actor i * Loewy.nativeGenerator j * (actor i)⁻¹ =
      Loewy.maskElement (generatorColumns i j) := by
  fin_cases i <;> fin_cases j
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 0) eval_mask52 conjugates_0_0
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 1) eval_mask177 conjugates_0_1
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 2) eval_mask183 conjugates_0_2
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 3) eval_mask187 conjugates_0_3
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 4) eval_mask37 conjugates_0_4
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 5) eval_mask147 conjugates_0_5
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 6) eval_mask243 conjugates_0_6
  · exact conjugate_of_matrix eval_actor0 (Loewy.toMatrix_nativeGenerator 7) eval_mask128 conjugates_0_7
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 0) eval_mask60 conjugates_1_0
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 1) eval_mask188 conjugates_1_1
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 2) eval_mask186 conjugates_1_2
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 3) eval_mask176 conjugates_1_3
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 4) eval_mask22 conjugates_1_4
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 5) eval_mask29 conjugates_1_5
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 6) eval_mask228 conjugates_1_6
  · exact conjugate_of_matrix eval_actor1 (Loewy.toMatrix_nativeGenerator 7) eval_mask3 conjugates_1_7
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 0) eval_mask2 conjugates_2_0
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 1) eval_mask1 conjugates_2_1
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 2) eval_mask13 conjugates_2_2
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 3) eval_mask8 conjugates_2_3
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 4) eval_mask189 conjugates_2_4
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 5) eval_mask101 conjugates_2_5
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 6) eval_mask74 conjugates_2_6
  · exact conjugate_of_matrix eval_actor2 (Loewy.toMatrix_nativeGenerator 7) eval_mask128 conjugates_2_7

/-- The odd product fuses the first-class vector outside the invariant sixteen
with the literal first involution, without appealing to numerical matrix rank. -/
theorem outside_first_product : (Janko4.a * Loewy.nativeGenerator 6) ^ 11 = 1 := by
  have h2 : toMatrix ag2 = toMatrix ag ^ 2 := by rw [ag2,map_mul,pow_two]
  have h4 : toMatrix ag4 = toMatrix ag ^ 4 := by
    rw [ag4,map_mul,h2,← pow_add]
  have h8 : toMatrix ag8 = toMatrix ag ^ 8 := by
    rw [ag8,map_mul,h4,← pow_add]
  have h10 : toMatrix ag10 = toMatrix ag ^ 10 := by
    rw [ag10,map_mul,h8,h2,← pow_add]
  apply toMatrix_injective
  change toMatrix (ag ^ 11) = toMatrix (1 : Model)
  rw [map_pow,map_one,show (11 : ℕ) = 10+1 from rfl,pow_succ,← h10,
    eval_ag10,eval_ag,← decode_packedMul,check_eleven,decode_packedOne]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
