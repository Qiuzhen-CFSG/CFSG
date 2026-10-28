module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Transpose displacement on an adjoint tensor

The trace-zero endomorphisms of a three-space have dimension eight. For any
operator g on W, the displacement of transpose tensor g contains an injected
copy of W × W. Use the upper matrix units E₀₁ and E₀₂ as seeds and extract
those same two entries: transpose sends both seeds into the lower triangle,
so contraction of their displacement is minus the original pair. Thus the
moved dimension is at least one quarter of the full tensor dimension.

This calculation uses actual trace-zero matrices and imposes no rank or
involution premise on g. Its consumer is the pure-adjoint outer tensor branch
of Aschbacher–Smith K.3.2. Source: Guralnick–Malle, Classification of 2F-modules
II, Proposition 4.8 step 3A, manuscript p.27.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open Representation.SL3.BinaryDefiningFactors
namespace Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose
variable (K : Type*) [Field K]

local instance : AddCommGroup (AdjointSpace K) := inferInstance

/-- Matrix transpose restricted to the literal trace-zero endomorphism space. -/
def adjointTranspose : Module.End K (AdjointSpace K) where
  toFun x := ⟨(LinearMap.toMatrix' x.val).transpose.toLin', by
    rw [LinearMap.mem_ker, Matrix.trace_toLin'_eq, Matrix.trace_transpose,
      ← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact x.property⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add, Matrix.transpose_add]
  map_smul' c x := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, map_smul, Matrix.transpose_smul, RingHom.id_apply]

/-- The transpose operator agrees with transpose in the natural matrix coordinates. -/
@[simp] theorem matrix_adjointTranspose (x : AdjointSpace K) :
    LinearMap.toMatrix' (adjointTranspose K x).val = (LinearMap.toMatrix' x.val).transpose := by
  exact LinearMap.toMatrix'_toLin' _

private def entry (i j : Fin 3) : AdjointSpace K →ₗ[K] K :=
  (LinearMap.proj j).comp ((LinearMap.proj i).comp
    ((LinearMap.toMatrix').toLinearMap.comp (AdjointSpace K).subtype))

private def upperUnit (j : Fin 3) (hj : j ≠ 0) : AdjointSpace K :=
  ⟨(LinearMap.proj j).smulRight (Pi.single 0 1), by
    simp [LinearMap.trace_smulRight, hj]⟩

variable {K} {W : Type*} [AddCommGroup W] [Module K W]

private def contract (i j : Fin 3) : AdjointSpace K ⊗[K] W →ₗ[K] W :=
  (TensorProduct.lid K W).toLinearMap.comp
    (TensorProduct.map (entry K i j) (LinearMap.id : Module.End K W))

@[simp] private theorem contract_tmul (i j : Fin 3) (x : AdjointSpace K) (w : W) :
    contract i j (x ⊗ₜ[K] w) = (LinearMap.toMatrix' x.val) i j • w := by
  simp only [contract, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, LinearMap.id_apply]
  rfl

private def seed : W × W →ₗ[K] AdjointSpace K ⊗[K] W :=
  (TensorProduct.mk K _ _ (upperUnit K 1 (by decide))).comp (LinearMap.fst K W W) +
    (TensorProduct.mk K _ _ (upperUnit K 2 (by decide))).comp (LinearMap.snd K W W)

/-- Transpose on the adjoint factor and an arbitrary operator on the other factor. -/
def graphTensor (g : Module.End K W) : Module.End K (AdjointSpace K ⊗[K] W) :=
  TensorProduct.map (adjointTranspose K) g

private theorem contract_displace_seed (g : Module.End K W) (w : W × W) :
    (contract 0 1 ((graphTensor g - 1) (seed w)),
     contract 0 2 ((graphTensor g - 1) (seed w))) = -w := by
  ext <;> simp [seed, graphTensor, upperUnit, adjointTranspose, Matrix.toLin'_apply]

/-- Two upper-entry copies give a quarter-dimension bound, over any field. -/
theorem graph_tensor_displacement [FiniteDimensional K W] (g : Module.End K W) :
    Module.finrank K (AdjointSpace K ⊗[K] W) ≤
      4 * Module.finrank K (graphTensor g - 1).range := by
  let D := graphTensor g - 1
  let J : W × W →ₗ[K] D.range := D.rangeRestrict.comp seed
  have hJ : Function.Injective J := by
    intro x y h
    have he := congrArg (fun z : D.range => (contract 0 1 z.val, contract 0 2 z.val)) h
    change (contract 0 1 (D (seed x)), contract 0 2 (D (seed x))) =
      (contract 0 1 (D (seed y)), contract 0 2 (D (seed y))) at he
    rw [contract_displace_seed, contract_displace_seed] at he
    exact neg_injective he
  have hdim := LinearMap.finrank_le_finrank_of_injective hJ
  rw [Module.finrank_prod] at hdim
  rw [Module.finrank_tensorProduct, finrank_adjointSpace]
  change _ ≤ 4 * Module.finrank K D.range
  omega
end Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose
