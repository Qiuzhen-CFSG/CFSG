module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.CharP.Two

/-!
# Scalar rigidity and involutory tensor exchanges

Schur's lemma compares two operators inducing the same automorphism of an
irreducible representation. If both square to one in characteristic two, their
scalar ratio is one. More generally, a scalar multiple of the exchange
`x tensor y ↦ f(y) tensor g(x)` which squares to one is exactly
`x tensor y ↦ f(y) tensor f⁻¹(x)`. Apply its square to `f(u) tensor u`, then
apply `f⁻¹ tensor 1`; injectivity of diagonal tensors determines the second map.
No conjugacy or group cocycle trivialization is required.

The concrete natural G₂ pair in `HalfTensor.PairDisplacement.Intertwiners`
uses these results to remove scalar ambiguity in both normalizer branches.
Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace Representation.TensorInvolutionIntertwiners
variable {K U : Type*} [Field K] [CharP K 2] [AddCommGroup U] [Module K U]
  [FiniteDimensional K U]

/-- In characteristic two a diagonal pure tensor determines its vector. -/
theorem diagonal_tensor_injective : Function.Injective (fun x : U => x ⊗ₜ[K] x) := by
  intro x y h
  let b := Module.finBasis K U
  apply b.repr.injective
  ext j
  let q : U ⊗[K] U →ₗ[K] K :=
    (_root_.TensorProduct.lid K K).toLinearMap.comp
      (_root_.TensorProduct.map (b.coord j) (b.coord j))
  have he := congrArg q h
  change b.repr x j * b.repr x j = b.repr y j * b.repr y j at he
  simpa only [CharTwo.neg_eq, or_self] using mul_self_eq_mul_self_iff.mp he

/-- The square-one equation absorbs the scalar and determines the second exchange map. -/
theorem normalize_exchange (f g : U ≃ₗ[K] U) (c : K)
    (T : Module.End K (U ⊗[K] U)) (h2 : T * T = 1)
    (hT : ∀ x y, T (x ⊗ₜ[K] y) = c • (f y ⊗ₜ[K] g x)) :
    ∀ x y, T (x ⊗ₜ[K] y) = f y ⊗ₜ[K] f.symm x := by
  have hg (x : U) : c • g x = f.symm x := by
    have hall (u : U) : c • g (f u) = u := by
      have hh' := congrArg (fun A : Module.End K (U ⊗[K] U) =>
        (_root_.TensorProduct.map f.symm.toLinearMap (LinearMap.id : Module.End K U))
          (A (f u ⊗ₜ[K] u))) h2
      simp only [Module.End.mul_apply, hT, map_smul, _root_.TensorProduct.map_tmul,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.id_apply,
        Module.End.one_apply] at hh'
      apply diagonal_tensor_injective (K := K)
      simpa only [_root_.TensorProduct.smul_tmul, _root_.TensorProduct.tmul_smul] using hh'
    simpa only [f.apply_symm_apply] using hall (f.symm x)
  intro x y
  rw [hT, ← _root_.TensorProduct.tmul_smul, hg]

section Schur
variable {G : Type*} [Group G] [IsAlgClosed K]
  (ρ : Representation K G U) [Representation.IsIrreducible ρ]

omit [CharP K 2] in
/-- Schur scalar rigidity, expressed directly for endomorphisms commuting with the action. -/
theorem scalar_of_commutes (C : Module.End K U)
    (hC : ∀ g, C * ρ g = ρ g * C) : ∃ c : K, C = c • 1 := by
  let A : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := C, isIntertwining' := hC }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective A
  refine ⟨c, ?_⟩
  have he := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f.toLinearMap) hc
  change c • (1 : Module.End K U) = C at he
  exact he.symm

omit [CharP K 2] in
/-- Two linear operators inducing the same group automorphism differ by a scalar. -/
theorem same_automorphism_scalar (α : MulAut G) (T : Module.End K U)
    (S : U ≃ₗ[K] U)
    (hT : ∀ g, T * ρ g = ρ (α g) * T)
    (hS : ∀ g, S.toLinearMap * ρ g = ρ (α g) * S.toLinearMap) :
    ∃ c : K, T = c • S.toLinearMap := by
  have hinv (g : G) : S.symm.toLinearMap * ρ (α g) = ρ g * S.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply S.injective
    have he := congrArg (fun A : Module.End K U => A (S.symm v)) (hS g)
    simpa only [Module.End.mul_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using he.symm
  obtain ⟨c, hc⟩ := scalar_of_commutes ρ (S.symm.toLinearMap * T) (by
    intro g
    rw [mul_assoc, hT, ← mul_assoc, hinv, mul_assoc])
  refine ⟨c, ?_⟩
  ext v
  have he := congrArg (fun A : Module.End K U => S (A v)) hc
  simpa only [Module.End.mul_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_smul] using he

/-- In characteristic two, two involutions inducing the same automorphism are equal. -/
theorem same_automorphism_involutions_eq [Nontrivial U]
    (α : MulAut G) (T : Module.End K U) (S : U ≃ₗ[K] U)
    (hT : ∀ g, T * ρ g = ρ (α g) * T)
    (hS : ∀ g, S.toLinearMap * ρ g = ρ (α g) * S.toLinearMap)
    (hT2 : T * T = 1) (hS2 : S.toLinearMap * S.toLinearMap = 1) :
    T = S.toLinearMap := by
  obtain ⟨c, rfl⟩ := same_automorphism_scalar ρ α T S hT hS
  have hc : c * c = 1 := by
    have he : (c * c) • (1 : Module.End K U) = (1 : K) • (1 : Module.End K U) := by
      simpa only [smul_mul_assoc, mul_smul_comm, smul_smul, hS2, one_smul] using hT2
    exact (smul_left_injective K (one_ne_zero : (1 : Module.End K U) ≠ 0)) he
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa only [pow_two, one_mul] using hc)
  rw [hc1, one_smul]
end Schur

end Representation.TensorInvolutionIntertwiners
