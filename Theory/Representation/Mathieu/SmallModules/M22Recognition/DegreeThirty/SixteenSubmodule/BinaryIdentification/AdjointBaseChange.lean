module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.Representation.SL3.BinaryFieldDescent.BaseChange

/-!
# Scalar extension of the concrete SL₃ adjoint representation

Extend endomorphisms and conjugate by the canonical identification of the
extended natural three-space. Preservation of trace restricts this map to
the trace-zero subspace. It is injective, and the two trace-zero spaces have
dimension eight, so it is an equivalence. Compatibility with composition
proves that this equivalence intertwines the actual conjugation actions.

This is the model comparison needed for finite-field descent in GLS III,
Remark 2.8.8 and Example 2.8.10(c). It applies to any extension of fields.
-/

open scoped TensorProduct MatrixGroups
open Representation Representation.SL3.BinaryDefiningFactors
public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.SL3.BinaryDefiningFactors
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

private def naturalBaseChange :
    (extendScalars K (natural (RingHom.id F))).Equiv
      (natural (algebraMap F K)) :=
  .mk (TensorProduct.piScalarRight F K K (Fin 3)) (by
    intro g
    ext v i
    change (TensorProduct.piScalarRight F K K (Fin 3))
      ((1 : K) ⊗ₜ[F] (natural (RingHom.id F) g (Pi.single v 1))) i =
      natural (algebraMap F K) g
        ((TensorProduct.piScalarRight F K K (Fin 3)) ((1 : K) ⊗ₜ[F] (Pi.single v 1))) i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Algebra.smul_def, mul_one]
    change (algebraMap F K) ((g.val.mulVec (Pi.single v 1)) i) =
      ((g.val.map (algebraMap F K)).mulVec
        (fun j => (algebraMap F K) ((Pi.single v 1 : Fin 3 → F) j))) i
    simp [Matrix.mulVec, dotProduct])

private def endBaseChange :
    (K ⊗[F] Module.End F (Fin 3 → F)) ≃ₗ[K] Module.End K (Fin 3 → K) :=
  (LinearMap.baseChangeLinearMapEquiv F K (Fin 3 → F) (Fin 3 → F)).trans
    (naturalBaseChange (F := F) (K := K)).toLinearEquiv.conj

private theorem endBaseChange_tmul (a : K) (f : Module.End F (Fin 3 → F)) :
    endBaseChange (a ⊗ₜ[F] f) =
      a • (naturalBaseChange (F := F) (K := K)).toLinearEquiv.conj (f.baseChange K) := by
  simp [endBaseChange, LinearMap.baseChangeLinearMapEquiv_tmul]

set_option maxRecDepth 2000 in
private def adjointBaseChangeMap : (K ⊗[F] AdjointSpace F) →ₗ[K] AdjointSpace K :=
  LinearMap.codRestrict _
    (endBaseChange.toLinearMap.comp
      ((LinearMap.trace F (Fin 3 → F)).ker.subtype.baseChange K)) (by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      change LinearMap.trace K _ (endBaseChange (a ⊗ₜ[F] f.val)) = 0
      rw [endBaseChange_tmul, map_smul, LinearMap.trace_conj', LinearMap.trace_baseChange,
        f.property, map_zero, smul_zero]
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy)

set_option maxRecDepth 2000 in
private theorem adjointBaseChangeMap_injective :
    Function.Injective (adjointBaseChangeMap (F := F) (K := K)) := by
  intro x y h
  have h' := congrArg Subtype.val h
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (LinearMap.trace F (Fin 3 → F)).ker.subtype Subtype.val_injective
  exact endBaseChange.injective h'

private def adjointBaseChangeLinearEquiv : (K ⊗[F] AdjointSpace F) ≃ₗ[K] AdjointSpace K := by
  letI : Module.Free F (AdjointSpace F) := Module.Free.of_divisionRing F (AdjointSpace F)
  exact LinearMap.linearEquivOfInjective
    (K := K) (V := K ⊗[F] AdjointSpace F) (V₂ := AdjointSpace K)
    (adjointBaseChangeMap (F := F) (K := K))
    (adjointBaseChangeMap_injective (F := F) (K := K)) (by
      rw [Module.finrank_baseChange, finrank_adjointSpace, finrank_adjointSpace])

set_option maxRecDepth 2000 in
/-- Scalar extension of the concrete trace-zero conjugation action, through the
canonical coefficient embedding on the natural three-space. -/
def adjointBaseChange :
    (extendScalars K (factorRep (RingHom.id F) .adjoint)).Equiv
      (factorRep (algebraMap F K) .adjoint) :=
  .mk (adjointBaseChangeLinearEquiv (F := F) (K := K)) (by
    intro g
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      apply Subtype.ext
      change endBaseChange (a ⊗ₜ[F]
          (natural (RingHom.id F) g ∘ₗ f.val ∘ₗ natural (RingHom.id F) g⁻¹)) =
        natural (algebraMap F K) g ∘ₗ endBaseChange (a ⊗ₜ[F] f.val) ∘ₗ
          natural (algebraMap F K) g⁻¹
      simp only [endBaseChange_tmul, LinearMap.baseChange_comp,
        LinearEquiv.conj_comp, LinearMap.smul_comp, LinearMap.comp_smul]
      rw [show (natural (RingHom.id F) g).baseChange K =
          extendScalars K (natural (RingHom.id F)) g from rfl,
        show (natural (RingHom.id F) g⁻¹).baseChange K =
          extendScalars K (natural (RingHom.id F)) g⁻¹ from rfl]
      rw [Representation.Equiv.conj_apply_self, Representation.Equiv.conj_apply_self]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy)

end Representation.SL3.BinaryDefiningFactors
