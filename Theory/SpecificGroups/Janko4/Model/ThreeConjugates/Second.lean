module

public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Second.Evaluations
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Second.Generation
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Reduction

/-!
# Three conjugates of the second J₄ involution generate the literal model

Let `r = (ababb)^5`. The explicit conjugators are the original model elements
`a` and `b`. Two words in `r`, `ara⁻¹`, `brb⁻¹` are simultaneously conjugate
in the ambient general linear group to the standard generators. The checked
change of basis therefore embeds the whole finite model into the subgroup
of the triple, which forces that subgroup to be the entire model.

Every matrix product is certified in `Second.Products00`–`Second.Products12`.
No assertion about the order or simplicity of the model is needed. In
particular, membership of the change-of-basis matrix in the model is not
assumed: only the triple's two conjugators need, and have, that membership.

This proves the upper bound of three for the second involution in
Revin–Zavarnitsine, https://arxiv.org/abs/2505.05173v2, Theorem 1.
`Second/source/README.md` records the witnesses, ATLAS attribution and
reproduction instructions. The final application discharges `hsecond` in
`automorphisms_of_representatives`, leaving the first triple explicit.
-/

public section
namespace Janko4.ThreeConjugates
open Subgroup Theory.GroupTheory GeneratorCertificates SecondCertificate
attribute [local irreducible] modelGroup matrixA matrixB

private def changeOfBasis : BinaryMatrixˣ where
  val := decodeRows tRows
  inv := decodeRows tiRows
  val_inv := by rw [← decode_packedMul, product_t_ti, decode_packedOne]
  inv_val := by rw [← decode_packedMul, product_ti_t, decode_packedOne]

private theorem intertwine_a :
    changeOfBasis * toAmbient standardA = toAmbient a * changeOfBasis := by
  apply Units.ext
  change decodeRows tRows * toMatrix standardA = matrixA * decodeRows tRows
  rw [eval_standardA]
  rw [matrixA, ← decode_packedMul, ← decode_packedMul, product_t_standardA, product_a_t]

private theorem intertwine_b :
    changeOfBasis * toAmbient standardB = toAmbient b * changeOfBasis := by
  apply Units.ext
  change decodeRows tRows * toMatrix standardB = matrixB * decodeRows tRows
  rw [eval_standardB]
  rw [matrixB, ← decode_packedMul, ← decode_packedMul, product_t_standardB, product_b_t]

/-- The literal conjugators `a` and `b` give a generating triple for `r`. -/
theorem second_conjugators_generate :
    zpowers ((a * b * a * b * b) ^ 5) ⊔
      zpowers (a * ((a * b * a * b * b) ^ 5) * a⁻¹) ⊔
      zpowers (b * ((a * b * a * b * b) ^ 5) * b⁻¹) = (⊤ : Subgroup Model) := by
  change triple = ⊤
  apply eq_top_of_ambient_conjugate_pair toAmbient toAmbient_injective a b closure_a_b
    triple changeOfBasis standardA standardB mem_standardA mem_standardB
  · have h := congrArg (changeOfBasis⁻¹ * ·) intertwine_a
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h.symm
  · have h := congrArg (changeOfBasis⁻¹ * ·) intertwine_b
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h.symm

/-- Three conjugates of the second involution generate the actual matrix model. -/
theorem second_three_conjugates_generate :
    ThreeConjugatesGenerate ((a * b * a * b * b) ^ 5) :=
  ⟨a, b, second_conjugators_generate⟩

/-- Discharge the second representative in the automorphism-generation reduction. -/
theorem automorphisms_of_first_representative
    [IsSimpleGroup Model] [Group.IsPerfect Model]
    (hfirst : ThreeConjugatesGenerate a) : ThreeConjugateAutomorphisms Model :=
  automorphisms_of_representatives hfirst second_three_conjugates_generate

end Janko4.ThreeConjugates
