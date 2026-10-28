module

public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Tensor
public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Transport

/-!
# The native trio core as a tensor conjugation module

The actual intrinsic core is identified with the tensor product of the natural
binary three-space and the natural S3 two-space. In translation coordinates,
conjugation by an affine element sends the vector at octad i to its common
linear image at the permuted octad. This is exactly the tensor action.

The final identity uses the existing quotient by the intrinsic two-core and
its established PSL3(2) × S3 identification. The ambient version uses the
literal inclusion into M24. The translation model has been characterized and
constructed from the native Golay code, rather than assumed.

Source: Aschbacher–Smith H.14.1(3), printed pp.396–397; Aschbacher,
*Sporadic Groups*, Lemma 20.2.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped BigOperators TensorProduct MatrixGroups
namespace Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
noncomputable section

lemma tensorCoordinates_action (q : QuotientModel) (z : NaturalTensor) (i : Fin 3) :
    tensorCoordinates (quotientTensorRepresentation q z) (q.1 i) =
      Matrix.SpecialLinearGroup.toLin' q.2 (tensorCoordinates z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
      change tensorCoordinates (Matrix.SpecialLinearGroup.toLin' q.2 a ⊗ₜ[ZMod 2]
        BinaryPermutation.coreRepresentation (Fin 3) q.1 n) (q.1 i) = _
      simp only [tensorCoordinates_tmul, BinaryPermutation.coreRepresentation_apply,
        BinaryPermutation.representation_apply, Equiv.symm_apply_apply, map_smul]
  | add z w hz hw =>
      simp only [map_add, Pi.add_apply, hz, hw]

/-- The additive tensor space is the actual intrinsic trio core. -/
def tensorEquiv : Multiplicative NaturalTensor ≃* Kernel :=
  tensorTranslationEquiv.toAddEquiv.toMultiplicative.trans translationEquiv

lemma tensorEquiv_point (z : NaturalTensor) (i : Fin 3) (v : Vector) :
    (tensorEquiv (Multiplicative.ofAdd z)).val.val.val (point (i,v)) =
      point (i,v + tensorCoordinates z i) :=
  translation_point _ _ _

lemma tensorEquiv_conjugation (g : Stabilizer) (z : NaturalTensor) :
    g * (tensorEquiv (Multiplicative.ofAdd z)).val * g⁻¹ =
      (tensorEquiv (Multiplicative.ofAdd (standardTensorRepresentation g z))).val := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  obtain ⟨t, ht⟩ := affineQuotient_spec affineCoverage g
  change HasAffineForm g (standardAffineHom g) t at ht
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,v⟩, rfl⟩ := point.surjective x
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [tensorEquiv_point, ht, ht, tensorEquiv_point]
  change point ((standardAffineHom g).1 i,
    Matrix.SpecialLinearGroup.toLin' (standardAffineHom g).2 (v + tensorCoordinates z i) + t i) =
      point ((standardAffineHom g).1 i,
        Matrix.SpecialLinearGroup.toLin' (standardAffineHom g).2 v + t i +
          tensorCoordinates (quotientTensorRepresentation (standardAffineHom g) z)
            ((standardAffineHom g).1 i))
  rw [tensorCoordinates_action, map_add, add_right_comm]

/-- The source ordering of the two natural-module factors. -/
def sourceModelEquiv : QuotientModel ≃* (PSL(3, ZMod 2) × Equiv.Perm (Fin 3)) :=
  (MulEquiv.prodComm).trans
    (MulEquiv.prodCongr Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two (MulEquiv.refl _))

/-- Natural three-space tensor natural two-space, with the projective source factor. -/
def sourceTensorRepresentation :
    Representation (ZMod 2) (PSL(3, ZMod 2) × Equiv.Perm (Fin 3)) NaturalTensor :=
  quotientTensorRepresentation.comp sourceModelEquiv.symm.toMonoidHom

lemma sourceTensorRepresentation_tmul
    (q : PSL(3, ZMod 2) × Equiv.Perm (Fin 3))
    (a : Vector) (n : BinaryPermutation.core (Fin 3)) :
    sourceTensorRepresentation q (a ⊗ₜ[ZMod 2] n) =
      Matrix.SpecialLinearGroup.toLin'
        (Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two.symm q.1) a ⊗ₜ[ZMod 2]
          BinaryPermutation.coreRepresentation (Fin 3) q.2 n := rfl

lemma sourceTensorRepresentation_mk (g : Stabilizer) :
    sourceTensorRepresentation (standardSourceQuotientEquiv (QuotientGroup.mk g)) =
      standardTensorRepresentation g := by
  change quotientTensorRepresentation
    (sourceModelEquiv.symm (sourceModelEquiv (standardQuotientEquiv (QuotientGroup.mk g)))) = _
  rw [sourceModelEquiv.symm_apply_apply, standardQuotientEquiv_mk]
  rfl

/-- H.14.1(3), using the literal quotient by the intrinsic two-core. -/
lemma tensorEquiv_source_conjugation (g : Stabilizer) (z : NaturalTensor) :
    g * (tensorEquiv (Multiplicative.ofAdd z)).val * g⁻¹ =
      (tensorEquiv (Multiplicative.ofAdd
        (sourceTensorRepresentation
          (standardSourceQuotientEquiv (QuotientGroup.mk g)) z))).val := by
  rw [sourceTensorRepresentation_mk]
  exact tensorEquiv_conjugation g z

/-- The tensor identification with the core mapped into the literal ambient M24. -/
def ambientTensorEquiv : Multiplicative NaturalTensor ≃* core :=
  tensorEquiv.trans (Kernel.equivMapOfInjective Stabilizer.subtype Stabilizer.subtype_injective)

lemma ambientTensorEquiv_conjugation (g : Stabilizer) (z : NaturalTensor) :
    g.val * (ambientTensorEquiv (Multiplicative.ofAdd z)).val * g.val⁻¹ =
      (ambientTensorEquiv (Multiplicative.ofAdd
        (sourceTensorRepresentation
          (standardSourceQuotientEquiv (QuotientGroup.mk g)) z))).val :=
  congrArg Subtype.val (tensorEquiv_source_conjugation g z)

lemma mem_twoCore_iff_sum_zero (g : Stabilizer) :
    g ∈ Kernel ↔ ∃ t : Fin 3 → Vector, (∑ i, t i) = 0 ∧
      ∀ i v, g.val.val (point (i,v)) = point (i,v + t i) := by
  rw [mem_standardTwoCore_iff]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, translation_sum_zero g t ht, ht⟩,
    fun ⟨t, _, ht⟩ => ⟨t, ht⟩⟩

end
end Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
