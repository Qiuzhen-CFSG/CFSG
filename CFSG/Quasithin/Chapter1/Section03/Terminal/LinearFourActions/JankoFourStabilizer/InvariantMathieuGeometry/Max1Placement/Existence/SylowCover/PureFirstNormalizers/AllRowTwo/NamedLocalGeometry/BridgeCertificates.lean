module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.BridgeMatrices
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.IntersectionCertificates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Mask

/-!
# Checked native bridge into the linear-five elementary subgroup

The actual word c = (kernelProduct 1 * fValue 6)^2 conjugates seven
independent max2 kernel words into the native F. The products are checked
on all 112 rows and transferred through the faithful native representation.
Python only proposes the certificates; every equality is kernel checked.
The original ATLAS max1/max2 words and their attribution remain in the
imported source modules. Source context: KW (1988), Section 2.1.
-/

@[expose] public section
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.BridgeCertificates
open Janko4.GeneratorCertificates
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound NormalClosureControl
open LowerBound.KernelSeparation
open Janko4.LocalStructure.LinearFive
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB toMatrix kernelFactor generators
theorem eval_k1 : toMatrix (kernelProduct 1 : Model) = decodeRows k1 := IntersectionCertificates.eval_1
theorem eval_k2 : toMatrix (kernelProduct 2 : Model) = decodeRows k2 := by
  have hw : kernelProduct 2 = kernelFactor 1 := by
    change (1 * ((kernelFactor 1) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = kernelFactor 1
    simp only [one_mul,mul_one]
  rw [hw]
  exact eval_factor 1
theorem eval_k4 : toMatrix (kernelProduct 4 : Model) = decodeRows k4 := by
  have hw : kernelProduct 4 = kernelFactor 2 := by
    change (1 * (1 * ((kernelFactor 2) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = kernelFactor 2
    simp only [one_mul,mul_one]
  rw [hw]
  exact eval_factor 2
theorem eval_k6 : toMatrix (kernelProduct 6 : Model) = decodeRows k6 := IntersectionCertificates.eval_6
theorem eval_k8 : toMatrix (kernelProduct 8 : Model) = decodeRows k8 := by
  have hw : kernelProduct 8 = kernelFactor 3 := by
    change (1 * (1 * (1 * ((kernelFactor 3) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = kernelFactor 3
    simp only [one_mul,mul_one]
  rw [hw]
  exact eval_factor 3
theorem eval_k14 : toMatrix (kernelProduct 14 : Model) = decodeRows k14 := by
  have hw : kernelProduct 14 = kernelProduct 6 * kernelFactor 3 := by
    change (1 * ((kernelFactor 1) * ((kernelFactor 2) * ((kernelFactor 3) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = (1 * ((kernelFactor 1) * ((kernelFactor 2) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 3
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 14 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 6 : Model) * (kernelFactor 3 : Model)) = _
  rw [map_mul,eval_k6,eval_factor,← decode_packedMul,kprod14]
theorem eval_k20 : toMatrix (kernelProduct 20 : Model) = decodeRows k20 := by
  have hw : kernelProduct 20 = kernelProduct 4 * kernelFactor 4 := by
    change (1 * (1 * ((kernelFactor 2) * (1 * ((kernelFactor 4) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = (1 * (1 * ((kernelFactor 2) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 4
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 20 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 4 : Model) * (kernelFactor 4 : Model)) = _
  rw [map_mul,eval_k4,eval_factor,← decode_packedMul,kprod20]
theorem eval_k24 : toMatrix (kernelProduct 24 : Model) = decodeRows k24 := by
  have hw : kernelProduct 24 = kernelProduct 8 * kernelFactor 4 := by
    change (1 * (1 * (1 * ((kernelFactor 3) * ((kernelFactor 4) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = (1 * (1 * (1 * ((kernelFactor 3) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 4
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 24 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 8 : Model) * (kernelFactor 4 : Model)) = _
  rw [map_mul,eval_k8,eval_factor,← decode_packedMul,kprod24]
theorem eval_k32 : toMatrix (kernelProduct 32 : Model) = decodeRows k32 := by
  have hw : kernelProduct 32 = kernelFactor 5 := by
    change (1 * (1 * (1 * (1 * (1 * ((kernelFactor 5) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = kernelFactor 5
    simp only [one_mul,mul_one]
  rw [hw]
  exact eval_factor 5
theorem eval_k68 : toMatrix (kernelProduct 68 : Model) = decodeRows k68 := by
  have hw : kernelProduct 68 = kernelProduct 4 * kernelFactor 6 := by
    change (1 * (1 * ((kernelFactor 2) * (1 * (1 * (1 * ((kernelFactor 6) * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = (1 * (1 * ((kernelFactor 2) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 6
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 68 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 4 : Model) * (kernelFactor 6 : Model)) = _
  rw [map_mul,eval_k4,eval_factor,← decode_packedMul,kprod68]
theorem eval_k160 : toMatrix (kernelProduct 160 : Model) = decodeRows k160 := by
  have hw : kernelProduct 160 = kernelProduct 32 * kernelFactor 7 := by
    change (1 * (1 * (1 * (1 * (1 * ((kernelFactor 5) * (1 * ((kernelFactor 7) * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) = (1 * (1 * (1 * (1 * (1 * ((kernelFactor 5) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 7
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 160 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 32 : Model) * (kernelFactor 7 : Model)) = _
  rw [map_mul,eval_k32,eval_factor,← decode_packedMul,kprod160]
theorem eval_k270 : toMatrix (kernelProduct 270 : Model) = decodeRows k270 := by
  have hw : kernelProduct 270 = kernelProduct 14 * kernelFactor 8 := by
    change (1 * ((kernelFactor 1) * ((kernelFactor 2) * ((kernelFactor 3) * (1 * (1 * (1 * (1 * ((kernelFactor 8) * (1 * (1 * (1 * (1 * 1))))))))))))) = (1 * ((kernelFactor 1) * ((kernelFactor 2) * ((kernelFactor 3) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 8
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 270 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 14 : Model) * (kernelFactor 8 : Model)) = _
  rw [map_mul,eval_k14,eval_factor,← decode_packedMul,kprod270]
theorem eval_k532 : toMatrix (kernelProduct 532 : Model) = decodeRows k532 := by
  have hw : kernelProduct 532 = kernelProduct 20 * kernelFactor 9 := by
    change (1 * (1 * ((kernelFactor 2) * (1 * ((kernelFactor 4) * (1 * (1 * (1 * (1 * ((kernelFactor 9) * (1 * (1 * (1 * 1))))))))))))) = (1 * (1 * ((kernelFactor 2) * (1 * ((kernelFactor 4) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 9
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 532 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 20 : Model) * (kernelFactor 9 : Model)) = _
  rw [map_mul,eval_k20,eval_factor,← decode_packedMul,kprod532]
theorem eval_k1048 : toMatrix (kernelProduct 1048 : Model) = decodeRows k1048 := IntersectionCertificates.eval_1048
theorem eval_k2208 : toMatrix (kernelProduct 2208 : Model) = decodeRows k2208 := by
  have hw : kernelProduct 2208 = kernelProduct 160 * kernelFactor 11 := by
    change (1 * (1 * (1 * (1 * (1 * ((kernelFactor 5) * (1 * ((kernelFactor 7) * (1 * (1 * (1 * ((kernelFactor 11) * (1 * 1))))))))))))) = (1 * (1 * (1 * (1 * (1 * ((kernelFactor 5) * (1 * ((kernelFactor 7) * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 11
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 2208 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 160 : Model) * (kernelFactor 11 : Model)) = _
  rw [map_mul,eval_k160,eval_factor,← decode_packedMul,kprod2208]
theorem eval_k4100 : toMatrix (kernelProduct 4100 : Model) = decodeRows k4100 := by
  have hw : kernelProduct 4100 = kernelProduct 4 * kernelFactor 12 := by
    change (1 * (1 * ((kernelFactor 2) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * ((kernelFactor 12) * 1))))))))))))) = (1 * (1 * ((kernelFactor 2) * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * (1 * 1))))))))))))) * kernelFactor 12
    simp only [one_mul,mul_one,mul_assoc]
  change toMatrix ((kernelProduct 4100 : sourceSubgroup) : Model) = _
  rw [hw]
  change toMatrix ((kernelProduct 4 : Model) * (kernelFactor 12 : Model)) = _
  rw [map_mul,eval_k4,eval_factor,← decode_packedMul,kprod4100]
theorem eval_f1 : toMatrix (fValue 1) = decodeRows f1 := by
  change toMatrix (fValue (2^(0 : Fin 10).val)) = _
  rw [fValue_basis]
  exact representation_generators 0
theorem eval_f2 : toMatrix (fValue 2) = decodeRows f2 := by
  change toMatrix (fValue (2^(1 : Fin 10).val)) = _
  rw [fValue_basis]
  exact representation_generators 1
theorem eval_f3 : toMatrix (fValue 3) = decodeRows f3 := by
  rw [show 3 = Nat.xor 1 2 from rfl,fValue_xor,map_mul,eval_f1,
    (show fValue 2 = (generators 1 : Model) from fValue_basis 1)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 1) = _
  rw [representation_generators,← decode_packedMul,fprod3]
theorem eval_f4 : toMatrix (fValue 4) = decodeRows f4 := by
  change toMatrix (fValue (2^(2 : Fin 10).val)) = _
  rw [fValue_basis]
  exact representation_generators 2
theorem eval_f5 : toMatrix (fValue 5) = decodeRows f5 := by
  rw [show 5 = Nat.xor 1 4 from rfl,fValue_xor,map_mul,eval_f1,
    (show fValue 4 = (generators 2 : Model) from fValue_basis 2)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 2) = _
  rw [representation_generators,← decode_packedMul,fprod5]
theorem eval_f6 : toMatrix (fValue 6) = decodeRows f6 := by
  rw [show 6 = Nat.xor 2 4 from rfl,fValue_xor,map_mul,eval_f2,
    (show fValue 4 = (generators 2 : Model) from fValue_basis 2)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 2) = _
  rw [representation_generators,← decode_packedMul,fprod6]
theorem eval_f7 : toMatrix (fValue 7) = decodeRows f7 := by
  rw [show 7 = Nat.xor 3 4 from rfl,fValue_xor,map_mul,eval_f3,
    (show fValue 4 = (generators 2 : Model) from fValue_basis 2)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 2) = _
  rw [representation_generators,← decode_packedMul,fprod7]
theorem eval_f9 : toMatrix (fValue 9) = decodeRows f9 := by
  rw [show 9 = Nat.xor 1 8 from rfl,fValue_xor,map_mul,eval_f1,
    (show fValue 8 = (generators 3 : Model) from fValue_basis 3)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 3) = _
  rw [representation_generators,← decode_packedMul,fprod9]
theorem eval_f13 : toMatrix (fValue 13) = decodeRows f13 := by
  rw [show 13 = Nat.xor 5 8 from rfl,fValue_xor,map_mul,eval_f5,
    (show fValue 8 = (generators 3 : Model) from fValue_basis 3)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 3) = _
  rw [representation_generators,← decode_packedMul,fprod13]
theorem eval_f14 : toMatrix (fValue 14) = decodeRows f14 := by
  rw [show 14 = Nat.xor 6 8 from rfl,fValue_xor,map_mul,eval_f6,
    (show fValue 8 = (generators 3 : Model) from fValue_basis 3)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 3) = _
  rw [representation_generators,← decode_packedMul,fprod14]
theorem eval_f15 : toMatrix (fValue 15) = decodeRows f15 := by
  rw [show 15 = Nat.xor 7 8 from rfl,fValue_xor,map_mul,eval_f7,
    (show fValue 8 = (generators 3 : Model) from fValue_basis 3)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 3) = _
  rw [representation_generators,← decode_packedMul,fprod15]
theorem eval_f20 : toMatrix (fValue 20) = decodeRows f20 := by
  rw [show 20 = Nat.xor 4 16 from rfl,fValue_xor,map_mul,eval_f4,
    (show fValue 16 = (generators 4 : Model) from fValue_basis 4)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 4) = _
  rw [representation_generators,← decode_packedMul,fprod20]
theorem eval_f22 : toMatrix (fValue 22) = decodeRows f22 := by
  rw [show 22 = Nat.xor 6 16 from rfl,fValue_xor,map_mul,eval_f6,
    (show fValue 16 = (generators 4 : Model) from fValue_basis 4)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 4) = _
  rw [representation_generators,← decode_packedMul,fprod22]
theorem eval_f25 : toMatrix (fValue 25) = decodeRows f25 := by
  rw [show 25 = Nat.xor 9 16 from rfl,fValue_xor,map_mul,eval_f9,
    (show fValue 16 = (generators 4 : Model) from fValue_basis 4)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 4) = _
  rw [representation_generators,← decode_packedMul,fprod25]
theorem eval_f45 : toMatrix (fValue 45) = decodeRows f45 := by
  rw [show 45 = Nat.xor 13 32 from rfl,fValue_xor,map_mul,eval_f13,
    (show fValue 32 = (generators 5 : Model) from fValue_basis 5)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 5) = _
  rw [representation_generators,← decode_packedMul,fprod45]
theorem eval_f47 : toMatrix (fValue 47) = decodeRows f47 := by
  rw [show 47 = Nat.xor 15 32 from rfl,fValue_xor,map_mul,eval_f15,
    (show fValue 32 = (generators 5 : Model) from fValue_basis 5)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 5) = _
  rw [representation_generators,← decode_packedMul,fprod47]
theorem eval_f52 : toMatrix (fValue 52) = decodeRows f52 := by
  rw [show 52 = Nat.xor 20 32 from rfl,fValue_xor,map_mul,eval_f20,
    (show fValue 32 = (generators 5 : Model) from fValue_basis 5)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 5) = _
  rw [representation_generators,← decode_packedMul,fprod52]
theorem eval_f54 : toMatrix (fValue 54) = decodeRows f54 := by
  rw [show 54 = Nat.xor 22 32 from rfl,fValue_xor,map_mul,eval_f22,
    (show fValue 32 = (generators 5 : Model) from fValue_basis 5)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 5) = _
  rw [representation_generators,← decode_packedMul,fprod54]
theorem eval_f57 : toMatrix (fValue 57) = decodeRows f57 := by
  rw [show 57 = Nat.xor 25 32 from rfl,fValue_xor,map_mul,eval_f25,
    (show fValue 32 = (generators 5 : Model) from fValue_basis 5)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 5) = _
  rw [representation_generators,← decode_packedMul,fprod57]
theorem eval_f78 : toMatrix (fValue 78) = decodeRows f78 := by
  rw [show 78 = Nat.xor 14 64 from rfl,fValue_xor,map_mul,eval_f14,
    (show fValue 64 = (generators 6 : Model) from fValue_basis 6)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 6) = _
  rw [representation_generators,← decode_packedMul,fprod78]
theorem eval_f109 : toMatrix (fValue 109) = decodeRows f109 := by
  rw [show 109 = Nat.xor 45 64 from rfl,fValue_xor,map_mul,eval_f45,
    (show fValue 64 = (generators 6 : Model) from fValue_basis 6)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 6) = _
  rw [representation_generators,← decode_packedMul,fprod109]
theorem eval_f121 : toMatrix (fValue 121) = decodeRows f121 := by
  rw [show 121 = Nat.xor 57 64 from rfl,fValue_xor,map_mul,eval_f57,
    (show fValue 64 = (generators 6 : Model) from fValue_basis 6)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 6) = _
  rw [representation_generators,← decode_packedMul,fprod121]
theorem eval_f590 : toMatrix (fValue 590) = decodeRows f590 := by
  rw [show 590 = Nat.xor 78 512 from rfl,fValue_xor,map_mul,eval_f78,
    (show fValue 512 = (generators 9 : Model) from fValue_basis 9)]
  change _ * Cardinality.KernelCount.representation matrixA_mul_self matrixB_pow_four (generators 9) = _
  rw [representation_generators,← decode_packedMul,fprod590]
def bridge : Model := ((kernelProduct 1 : Model) * fValue 6)^2

theorem eval_bridge : toMatrix bridge = decodeRows bridgeRows := by
  rw [bridge,pow_two,map_mul,map_mul,eval_k1,eval_f6,← decode_packedMul,bridge_first,
    ← decode_packedMul,bridge_square]
theorem bridge_conjugates_0 :
    (MulAut.conj bridge) (kernelProduct 1 : Model) = fValue 6 := by
  have he : bridge * (kernelProduct 1 : Model) = fValue 6 * bridge := by
    apply toMatrix_injective
    rw [map_mul,map_mul,eval_bridge,eval_k1,eval_f6,← decode_packedMul,← decode_packedMul]
    exact congrArg decodeRows (left0.trans right0.symm)
  simp only [MulAut.conj_apply,he,mul_assoc,mul_inv_cancel,mul_one]
theorem bridge_conjugates_1 :
    (MulAut.conj bridge) (kernelProduct 68 : Model) = fValue 590 := by
  have he : bridge * (kernelProduct 68 : Model) = fValue 590 * bridge := by
    apply toMatrix_injective
    rw [map_mul,map_mul,eval_bridge,eval_k68,eval_f590,← decode_packedMul,← decode_packedMul]
    exact congrArg decodeRows (left1.trans right1.symm)
  simp only [MulAut.conj_apply,he,mul_assoc,mul_inv_cancel,mul_one]
theorem bridge_conjugates_2 :
    (MulAut.conj bridge) (kernelProduct 270 : Model) = fValue 54 := by
  have he : bridge * (kernelProduct 270 : Model) = fValue 54 * bridge := by
    apply toMatrix_injective
    rw [map_mul,map_mul,eval_bridge,eval_k270,eval_f54,← decode_packedMul,← decode_packedMul]
    exact congrArg decodeRows (left2.trans right2.symm)
  simp only [MulAut.conj_apply,he,mul_assoc,mul_inv_cancel,mul_one]
theorem bridge_conjugates_3 :
    (MulAut.conj bridge) (kernelProduct 532 : Model) = fValue 47 := by
  have he : bridge * (kernelProduct 532 : Model) = fValue 47 * bridge := by
    apply toMatrix_injective
    rw [map_mul,map_mul,eval_bridge,eval_k532,eval_f47,← decode_packedMul,← decode_packedMul]
    exact congrArg decodeRows (left3.trans right3.symm)
  simp only [MulAut.conj_apply,he,mul_assoc,mul_inv_cancel,mul_one]
theorem bridge_conjugates_4 :
    (MulAut.conj bridge) (kernelProduct 1048 : Model) = fValue 121 := by
  have he : bridge * (kernelProduct 1048 : Model) = fValue 121 * bridge := by
    apply toMatrix_injective
    rw [map_mul,map_mul,eval_bridge,eval_k1048,eval_f121,← decode_packedMul,← decode_packedMul]
    exact congrArg decodeRows (left4.trans right4.symm)
  simp only [MulAut.conj_apply,he,mul_assoc,mul_inv_cancel,mul_one]
theorem bridge_conjugates_5 :
    (MulAut.conj bridge) (kernelProduct 2208 : Model) = fValue 109 := by
  have he : bridge * (kernelProduct 2208 : Model) = fValue 109 * bridge := by
    apply toMatrix_injective
    rw [map_mul,map_mul,eval_bridge,eval_k2208,eval_f109,← decode_packedMul,← decode_packedMul]
    exact congrArg decodeRows (left5.trans right5.symm)
  simp only [MulAut.conj_apply,he,mul_assoc,mul_inv_cancel,mul_one]
theorem bridge_conjugates_6 :
    (MulAut.conj bridge) (kernelProduct 4100 : Model) = fValue 52 := by
  have he : bridge * (kernelProduct 4100 : Model) = fValue 52 * bridge := by
    apply toMatrix_injective
    rw [map_mul,map_mul,eval_bridge,eval_k4100,eval_f52,← decode_packedMul,← decode_packedMul]
    exact congrArg decodeRows (left6.trans right6.symm)
  simp only [MulAut.conj_apply,he,mul_assoc,mul_inv_cancel,mul_one]
end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.NamedLocalGeometry.BridgeCertificates
