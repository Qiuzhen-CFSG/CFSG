module

public import Theory.Representation.BinaryAlternatingSixModels.Geometry
public import Theory.Representation.ExtendScalars
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Scalar extension of the binary `A₆` tensor

This file is the concrete scalar-extension layer for the tensor action from
`BinaryAlternatingSixModels`.  The coefficient field is the existing literal
quadratic field `F₂[a]`, with `a² = a + 1`; it is retained here rather than
using an abstract field of cardinality four.  The actual eigenspace and
exchange certificates are added below the representation interface.
-/

@[expose] public section

open scoped TensorProduct
open Representation
namespace BinaryAlternatingSix

open Theory.SpecificGroups.SymmetricSix

namespace TensorSplitting

abbrev F4 := Representation.SL2FourNatural.F

instance : Fintype F4 := Representation.SL2FourNatural.fieldFintype
instance : CharP F4 2 := Representation.SL2FourNatural.fieldCharP

theorem card_F4 : Fintype.card F4 = 4 :=
  Representation.SL2FourNatural.card_field

noncomputable abbrev scalarTensor : Representation F4 A6
    (F4 ⊗[ZMod 2] TensorModule) :=
  Representation.extendScalars F4 alternatingTensor

theorem scalarTensor_finrank : Module.finrank F4 scalarTensor.asModule = 16 := by
  change Module.finrank F4 (F4 ⊗[ZMod 2] TensorModule) = 16
  rw [Module.finrank_baseChange]
  simp

theorem finrank_F4_binary : Module.finrank (ZMod 2) F4 = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F4)
  rw [Nat.card_eq_fintype_card, card_F4, Nat.card_eq_fintype_card, ZMod.card] at h
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) h).symm

theorem scalarTensor_binary_finrank :
    Module.finrank (ZMod 2) (F4 ⊗[ZMod 2] TensorModule) = 32 := by
  rw [Module.finrank_tensorProduct, finrank_F4_binary]
  simp

/-! The following basis is the literal polar basis used by the published
tensor action.  Naming it here keeps subsequent finite certificates tied to
the actual `polarTable`, rather than to an abstract four-dimensional model. -/

def naturalBasisVector : Fin 4 → NaturalModule :=
  ![(polarVector (13 : Duad)).val, (polarVector (1 : Duad)).val,
    (polarVector (14 : Duad)).val, (polarVector (0 : Duad)).val]

theorem naturalBasisVector_linearIndependent :
    LinearIndependent (ZMod 2) naturalBasisVector := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h0 := congrFun hf (Sum.inl (0 : Fin 2))
  have h1 := congrFun hf (Sum.inl (1 : Fin 2))
  have h2 := congrFun hf (Sum.inr (0 : Fin 2))
  have h3 := congrFun hf (Sum.inr (1 : Fin 2))
  fin_cases i <;>
    simp [naturalBasisVector, polarVector, polarTable, vec,
      Fin.sum_univ_four] at h0 h1 h2 h3 ⊢ <;> assumption

theorem naturalBasisVector_span :
    Submodule.span (ZMod 2) (Set.range naturalBasisVector) = ⊤ := by
  apply naturalBasisVector_linearIndependent.span_eq_top_of_card_eq_finrank
  simp

noncomputable def naturalBasis : Module.Basis (Fin 4) (ZMod 2) NaturalModule :=
  Module.Basis.mk naturalBasisVector_linearIndependent naturalBasisVector_span.ge

@[simp] theorem naturalBasis_apply (i : Fin 4) :
    naturalBasis i = naturalBasisVector i :=
  Module.Basis.mk_apply _ _ _

noncomputable abbrev tensorBasis :
    Module.Basis (Fin 4 × Fin 4) (ZMod 2) TensorModule :=
  naturalBasis.tensorProduct naturalBasis

@[simp] theorem tensorBasis_apply (i j : Fin 4) :
    tensorBasis (i, j) = naturalBasis i ⊗ₜ[ZMod 2] naturalBasis j := by
  exact Module.Basis.tensorProduct_apply _ _ _ _

/-! The two formulas below are the concrete interface for later finite
certificates.  They retain both published factors, including the exceptional
twist in the second one, and avoid replacing the tensor by an abstract
sixteen-dimensional representation. -/

theorem alternatingTensor_tensorBasis_apply (g : A6) (i j : Fin 4) :
    alternatingTensor g (tensorBasis (i, j)) =
      (firstAlternating g (naturalBasis i)) ⊗ₜ[ZMod 2]
        (secondAlternating g (naturalBasis j)) := by
  simp [alternatingTensor, tensorAction]

theorem scalarTensor_tmul_apply (g : A6) (a : F4) (v : TensorModule) :
    scalarTensor g (a ⊗ₜ[ZMod 2] v) =
      a ⊗ₜ[ZMod 2] alternatingTensor g v := by
  simp [scalarTensor, Representation.extendScalars_apply]

theorem scalarTensor_tensorBasis_apply (g : A6) (a : F4) (i j : Fin 4) :
    scalarTensor g (a ⊗ₜ[ZMod 2] tensorBasis (i, j)) =
      a ⊗ₜ[ZMod 2]
        ((firstAlternating g (naturalBasis i)) ⊗ₜ[ZMod 2]
          (secondAlternating g (naturalBasis j))) := by
  rw [scalarTensor_tmul_apply, alternatingTensor_tensorBasis_apply]

end TensorSplitting

end BinaryAlternatingSix
