module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.Models
public import Theory.Representation.BinaryPermutation.ThreeTensor
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# The three concrete SL₃(2) × S₃ tensor modules

The first factors are the faithful natural, contragredient natural, and
trace-zero adjoint models, of dimensions three, three, and eight. The second
factor is the actual augmentation core of S₃ from `ExternalModules.Models`.
The general tensor calculation therefore gives rank one and these exact fixed
codimensions for every elementary quadratic actor with nontrivial S₃ projection.

For the Steinberg tensor, the earlier strict bound on a single Steinberg
module also excludes actors in the component. Equivariant transport retains
the full actor, its rank, and the specified direct-product identification.

Source: Aschbacher–Smith 13.8.21(1), printed p.957, using B.4 and H.6
(combined manuscript of 1 March 2004). The earlier single-Steinberg bound
remains an explicit input, separate from the tensor calculation proved here.
-/

@[expose] public section

open Representation Representation.BinaryOffender TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors

/-- The underlying space of the dual natural tensor. -/
noncomputable abbrev DualTensorSpace :=
  (Module.Dual (ZMod 2) BinaryLinearThree.Vector) ⊗[ZMod 2] S3Natural

/-- The external tensor product of the dual natural action with the S₃ natural action. -/
noncomputable abbrev dualNaturalTensor :
    Representation (ZMod 2) TensorGroup
      ((Module.Dual (ZMod 2) BinaryLinearThree.Vector) ⊗[ZMod 2] S3Natural) :=
  BinaryPermutation.ThreeTensor.action BinaryLinearThree.W.dual
/-- The external tensor product of the concrete Steinberg action with the S₃ natural action. -/
noncomputable abbrev steinbergTensor :
    Representation (ZMod 2) TensorGroup (BinaryLinearThree.Steinberg ⊗[ZMod 2] S3Natural) :=
  BinaryPermutation.ThreeTensor.action BinaryLinearThree.S

/-- An outer actor on the natural tensor has rank one and fixed codimension three. -/
theorem natural_tensor_outer_parameters (A : Subgroup TensorGroup) (hA : IsElementaryTwo A)
    (hq : IsQuadratic naturalTensor A) (hout : ∃ a ∈ A, a.2 ≠ 1) :
    rank A = 1 ∧ fixedCodim naturalTensor A = 3 := by
  change rank A = 1 ∧ fixedCodim (BinaryPermutation.ThreeTensor.action BinaryLinearThree.W) A = 3
  refine ⟨BinaryPermutation.ThreeTensor.rank_eq_one _ BinaryLinearThree.natural_injective A hA hq hout, ?_⟩
  obtain ⟨a, ha, hat⟩ := hout
  have he := BinaryPermutation.ThreeTensor.fixedCodim_eq_dimension BinaryLinearThree.W A hq a ha hat
  simpa [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector] using he

/-- An outer actor on the dual natural tensor has rank one and fixed codimension three. -/
theorem dual_tensor_outer_parameters (A : Subgroup TensorGroup) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (V := DualTensorSpace) dualNaturalTensor A) (hout : ∃ a ∈ A, a.2 ≠ 1) :
    rank A = 1 ∧ fixedCodim (V := DualTensorSpace) dualNaturalTensor A = 3 := by
  change rank A = 1 ∧ fixedCodim (V := DualTensorSpace) (BinaryPermutation.ThreeTensor.action BinaryLinearThree.W.dual) A = 3
  refine ⟨BinaryPermutation.ThreeTensor.rank_eq_one _ BinaryLinearThree.dual_injective A hA hq hout, ?_⟩
  obtain ⟨a, ha, hat⟩ := hout
  have he := BinaryPermutation.ThreeTensor.fixedCodim_eq_dimension BinaryLinearThree.W.dual A hq a ha hat
  simpa [Subspace.dual_finrank_eq, BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector] using he

/-- An outer actor on the Steinberg tensor has rank one and fixed codimension eight. -/
theorem steinberg_tensor_outer_parameters (A : Subgroup TensorGroup) (hA : IsElementaryTwo A)
    (hq : IsQuadratic steinbergTensor A) (hout : ∃ a ∈ A, a.2 ≠ 1) :
    rank A = 1 ∧ fixedCodim steinbergTensor A = 8 := by
  change rank A = 1 ∧ fixedCodim (BinaryPermutation.ThreeTensor.action BinaryLinearThree.S) A = 8
  refine ⟨BinaryPermutation.ThreeTensor.rank_eq_one _ BinaryLinearThree.steinberg_injective A hA hq hout, ?_⟩
  obtain ⟨a, ha, hat⟩ := hout
  have he := BinaryPermutation.ThreeTensor.fixedCodim_eq_dimension BinaryLinearThree.S A hq a ha hat
  simpa only [BinaryLinearThree.finrank_steinberg] using he

/-- The natural tensor excludes outer quadratic actors of ratio at most two. -/
theorem natural_tensor_outer_bound (A : Subgroup TensorGroup) (hA : IsElementaryTwo A)
    (hq : IsQuadratic naturalTensor A) (hout : ∃ a ∈ A, a.2 ≠ 1) :
    2 * rank A < fixedCodim naturalTensor A := by
  obtain ⟨hr, hc⟩ := natural_tensor_outer_parameters A hA hq hout
  omega

/-- The dual natural tensor excludes outer quadratic actors of ratio at most two. -/
theorem dual_tensor_outer_bound (A : Subgroup TensorGroup) (hA : IsElementaryTwo A)
    (hq : IsQuadratic (V := DualTensorSpace) dualNaturalTensor A) (hout : ∃ a ∈ A, a.2 ≠ 1) :
    2 * rank A < fixedCodim (V := DualTensorSpace) dualNaturalTensor A := by
  obtain ⟨hr, hc⟩ := dual_tensor_outer_parameters A hA hq hout
  omega

/-- The single-Steinberg bound excludes every quadratic actor on its tensor. -/
theorem steinberg_tensor_bound
    (hS : ∀ B, IsElementaryTwo B → IsQuadratic BinaryLinearThree.S B →
      rank B < fixedCodim BinaryLinearThree.S B)
    (A : Subgroup TensorGroup) (hA : IsElementaryTwo A)
    (hq : IsQuadratic steinbergTensor A) :
    2 * rank A < fixedCodim steinbergTensor A := by
  by_cases hout : ∃ a ∈ A, a.2 ≠ 1
  · obtain ⟨hr, hc⟩ := steinberg_tensor_outer_parameters A hA hq hout
    omega
  · apply BinaryPermutation.ThreeTensor.component_bound _ hS A hA hq
    push Not at hout
    exact hout

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- Transport the Steinberg exclusion through actual group and module equivalences. -/
theorem steinberg_tensor_bound_of_equiv
    (σ : Representation (ZMod 2) H U) (eH : H ≃* TensorGroup)
    (eV : σ.Equiv (steinbergTensor.comp eH.toMonoidHom))
    (hS : ∀ B, IsElementaryTwo B → IsQuadratic BinaryLinearThree.S B →
      rank B < fixedCodim BinaryLinearThree.S B)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic σ A) :
    2 * rank A < fixedCodim σ A := by
  obtain ⟨he, hq', hr, hc⟩ := BinaryPermutation.ThreeTensor.transport_quadratic
    BinaryLinearThree.S σ eH eV A hA hq
  rw [hc, ← hr]
  exact steinberg_tensor_bound hS _ he hq'

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.OuterActors
