module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.FullAction

/-!
# The intrinsic operator space and its full endomorphism commutant

The prescribed kernel coordinates transport the certified matrix algebra to
actual endomorphisms of the displacement kernel. The ten-space has dimension
ten, consists of commuting square-zero operators, and generates a
56-dimensional algebra with the first adapted coordinate cyclic. Its commutant
inside the entire endomorphism ring is exactly that algebra.

This is transport through an explicit algebra equivalence, not a restriction
to a selected subgroup or a claim about a normalizer. Coordinate certificates
and provenance are documented in `IntrinsicAlgebra/source/README.md`.
-/

@[expose] public section
set_option maxRecDepth 2048
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
attribute [local irreducible] kernelCoordEquiv kernelSpace operator generatedAlgebra operatorSpace intrinsicOperator op

/-- The literal kernel basis identifies matrices with endomorphisms of the actual kernel. -/
noncomputable def kernelEndEquiv : SmallMatrix ≃ₐ[ZMod 2] Module.End (ZMod 2) kernelSpace :=
  Matrix.toLinAlgEquiv'.trans (kernelCoordEquiv.conjAlgEquiv (ZMod 2))

theorem intrinsicOperator_eq (v : Fin 10 → ZMod 2) :
    intrinsicOperator v = kernelEndEquiv (op v) := by
  unfold intrinsicOperator kernelEndEquiv
  rfl

/-- The intrinsic ten-space, as actual endomorphisms rather than coordinate matrices. -/
noncomputable def intrinsicOperatorSpace : Submodule (ZMod 2) (Module.End (ZMod 2) kernelSpace) :=
  operatorSpace.map kernelEndEquiv.toLinearMap

/-- The generated algebra on the actual displacement kernel. -/
noncomputable def intrinsicAlgebra : Subalgebra (ZMod 2) (Module.End (ZMod 2) kernelSpace) :=
  generatedAlgebra.map kernelEndEquiv.toAlgHom

theorem kernelEndEquiv_operator (i : Fin 10) :
    kernelEndEquiv (operator i) = intrinsicOperator (Pi.single i 1) := by
  rw [intrinsicOperator_eq, op_single]

theorem intrinsicOperatorSpace_eq_span :
    intrinsicOperatorSpace = Submodule.span (ZMod 2)
      (Set.range (fun i : Fin 10 => intrinsicOperator (Pi.single i 1))) := by
  rw [intrinsicOperatorSpace, operatorSpace, Submodule.map_span, ← Set.range_comp']
  exact congrArg (fun f : Fin 10 → Module.End (ZMod 2) kernelSpace =>
    Submodule.span (ZMod 2) (Set.range f)) (funext kernelEndEquiv_operator)

theorem intrinsicAlgebra_eq_adjoin :
    intrinsicAlgebra = Algebra.adjoin (ZMod 2)
      (Set.range (fun i : Fin 10 => intrinsicOperator (Pi.single i 1))) := by
  rw [intrinsicAlgebra, generatedAlgebra, AlgHom.map_adjoin, ← Set.range_comp']
  exact congrArg (fun f : Fin 10 → Module.End (ZMod 2) kernelSpace =>
    Algebra.adjoin (ZMod 2) (Set.range f)) (funext kernelEndEquiv_operator)

theorem intrinsicAlgebra_finrank : Module.finrank (ZMod 2) intrinsicAlgebra = 56 :=
  (generatedAlgebra.equivMapOfInjective kernelEndEquiv.toAlgHom
    kernelEndEquiv.injective).toLinearEquiv.finrank_eq.symm.trans generatedAlgebra_finrank

theorem intrinsicOperatorSpace_finrank :
    Module.finrank (ZMod 2) intrinsicOperatorSpace = 10 := by
  rw [intrinsicOperatorSpace, LinearEquiv.finrank_map_eq kernelEndEquiv.toLinearEquiv,
    operatorSpace_finrank]

theorem mem_intrinsicAlgebra (G : SmallMatrix) :
    kernelEndEquiv G ∈ intrinsicAlgebra ↔ G ∈ generatedAlgebra := by
  rw [intrinsicAlgebra, Subalgebra.mem_map]
  constructor
  · rintro ⟨H, hH, he⟩
    exact kernelEndEquiv.injective he ▸ hH
  · intro hG
    exact ⟨G, hG, rfl⟩

theorem kernelEndEquiv_apply (M : SmallMatrix) (v : SmallColumn) :
    kernelEndEquiv M (kernelCoordEquiv v) = kernelCoordEquiv (M *ᵥ v) := by
  change kernelCoordEquiv (M *ᵥ (kernelCoordEquiv.symm (kernelCoordEquiv v))) = _
  rw [kernelCoordEquiv.symm_apply_apply]

/-- The first adapted coordinate is cyclic on the actual kernel. -/
theorem intrinsicAlgebra_cyclic (w : kernelSpace) :
    ∃ E ∈ intrinsicAlgebra, E (kernelCoordEquiv cyclicVector) = w := by
  obtain ⟨v, rfl⟩ := kernelCoordEquiv.surjective w
  obtain ⟨M, hM, he⟩ := generatedAlgebra_cyclic v
  refine ⟨kernelEndEquiv M, (mem_intrinsicAlgebra M).mpr hM, ?_⟩
  rw [kernelEndEquiv_apply, he]

/-- The full commutant statement transported to End(K), with no invertibility restriction. -/
theorem intrinsic_commutant (E : Module.End (ZMod 2) kernelSpace) :
    (∀ i : Fin 10, E * intrinsicOperator (Pi.single i 1) =
      intrinsicOperator (Pi.single i 1) * E) ↔ E ∈ intrinsicAlgebra := by
  obtain ⟨G, rfl⟩ := kernelEndEquiv.surjective E
  simp only [intrinsicOperator_eq, op_single, ← map_mul, kernelEndEquiv.injective.eq_iff,
    mem_intrinsicAlgebra]
  change (∀ i, G * operator i = operator i * G) ↔ G ∈ generatedAlgebra.toSubmodule
  rw [generatedAlgebra_toSubmodule_eq, commutes_operator_iff_mem_algebraSpan]

/-- Every linear combination belongs to the operator space. -/
theorem op_mem_operatorSpace (v : Fin 10 → ZMod 2) : op v ∈ operatorSpace := by
  rw [operatorSpace, op_apply]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))

theorem intrinsicOperator_mem (v : Fin 10 → ZMod 2) :
    intrinsicOperator v ∈ intrinsicOperatorSpace := by
  rw [intrinsicOperator_eq]
  exact ⟨op v, op_mem_operatorSpace v, rfl⟩

theorem op_mem_generatedAlgebra (v : Fin 10 → ZMod 2) : op v ∈ generatedAlgebra := by
  rw [op_apply]
  exact generatedAlgebra.sum_mem (fun i _ =>
    generatedAlgebra.smul_mem (operator_mem_generatedAlgebra i) (v i))

theorem op_mul_comm (v w : Fin 10 → ZMod 2) : op v * op w = op w * op v :=
  (generatedAlgebra_commute (op_mem_generatedAlgebra v) (op_mem_generatedAlgebra w)).eq

private theorem square_zero_add (A B : SmallMatrix) (hAB : A * B = B * A)
    (hA : A * A = 0) (hB : B * B = 0) : (A + B) * (A + B) = 0 := by
  rw [add_mul, mul_add, mul_add, hA, hB, zero_add, add_zero, hAB]
  ext i j
  exact CharTwo.add_self_eq_zero ((B * A) i j)

/-- Square-zero extends to the whole ten-space in characteristic two. -/
theorem operatorSpace_square_zero {A : SmallMatrix} (hA : A ∈ operatorSpace) : A * A = 0 := by
  rw [operatorSpace] at hA
  induction hA using Submodule.span_induction with
  | mem A hA => obtain ⟨i, rfl⟩ := hA; exact operator_mul_self i
  | zero => exact zero_mul _
  | add A B hA hB ihA ihB =>
    apply square_zero_add A B _ ihA ihB
    have hle : Submodule.span (ZMod 2) (Set.range operator) ≤ generatedAlgebra.toSubmodule := by
      exact Submodule.span_le.mpr (fun _ ⟨i, hi⟩ => hi ▸ operator_mem_generatedAlgebra i)
    exact (generatedAlgebra_commute (hle hA) (hle hB)).eq
  | smul a A _ ih => simp only [smul_mul_assoc, mul_smul_comm, ih, smul_zero]

theorem op_mul_self (v : Fin 10 → ZMod 2) : op v * op v = 0 :=
  operatorSpace_square_zero (op_mem_operatorSpace v)

theorem intrinsicOperator_mul_self (v : Fin 10 → ZMod 2) :
    intrinsicOperator v * intrinsicOperator v = 0 := by
  rw [intrinsicOperator_eq, ← map_mul, op_mul_self, map_zero]

theorem intrinsicOperator_mul_comm (v w : Fin 10 → ZMod 2) :
    intrinsicOperator v * intrinsicOperator w = intrinsicOperator w * intrinsicOperator v := by
  rw [intrinsicOperator_eq v, intrinsicOperator_eq w,
    ← map_mul kernelEndEquiv, ← map_mul kernelEndEquiv, op_mul_comm]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
