module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Theory.Representation.JacobsonDensity

/-!
# Separating tensor factors by left endomorphisms

If an invariant subspace of `V ⊗ W` is stable under every operator `A ⊗ 1`,
its tensor coordinates form an invariant subspace of `W`. Rank-one operators
extract those coordinates. Irreducibility of `W` therefore makes the original
subspace zero or the whole tensor product. Stability under a generating family
of left operators suffices by induction on the algebra they generate.
Conversely, the checked Jacobson density theorem proves that a family with no
nontrivial common invariant subspace generates the full endomorphism algebra
over an algebraically closed field.

This is the linear-algebra step in the infinitesimal proof of the ordinary
Steinberg tensor theorem (GLS3, Theorem 2.8.5 / [St2, Theorem 13.1]).
No density or restricted-representation theorem is assumed implicitly.
-/

open Theory.AlgebraicGroup
open scoped TensorProduct
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
@[expose] public noncomputable section
universe u v w
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {W : Type w} [AddCommGroup W] [Module k W]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- Extracting a coordinate of the left tensor factor is a rank-one endomorphism. -/
theorem rankOne_rTensor (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (i : Fin (Module.finrank k V)) (v : V) (z : V ⊗[k] W) :
    ((b.coord i).smulRight v).rTensor W z =
      v ⊗ₜ[k] ((TensorProduct.equivFinsuppOfBasisLeft b) z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [LinearMap.rTensor_tmul, LinearMap.smulRight_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, Module.Basis.coord_apply,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, Finsupp.add_apply, TensorProduct.tmul_add]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- Stability under a generating family implies stability under all left endomorphisms. -/
theorem left_stable_of_adjoin_eq_top {ι : Type*} (D : ι → Module.End k V)
    (hD : Algebra.adjoin k (Set.range D) = ⊤)
    (U : Submodule k (V ⊗[k] W))
    (hU : ∀ i z, z ∈ U → (D i).rTensor W z ∈ U) :
    ∀ A : Module.End k V, ∀ z, z ∈ U → A.rTensor W z ∈ U := by
  intro A
  have hA : A ∈ Algebra.adjoin k (Set.range D) := by rw [hD]; trivial
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    obtain ⟨i, rfl⟩ := hA
    exact hU i
  | algebraMap c =>
    intro z hz
    have heq : (algebraMap k (Module.End k V) c).rTensor W = c • LinearMap.id := by
      ext v w
      simp [Module.algebraMap_end_apply, TensorProduct.smul_tmul]
    rw [heq]
    exact U.smul_mem c hz
  | add A B hA hB ihA ihB =>
    intro z hz
    rw [LinearMap.rTensor_add, LinearMap.add_apply]
    exact U.add_mem (ihA z hz) (ihB z hz)
  | mul A B hA hB ihA ihB =>
    intro z hz
    rw [LinearMap.rTensor_mul, Module.End.mul_apply]
    exact ihA _ (ihB z hz)

omit [IsAlgClosed k] in
/-- An invariant tensor subspace stable under every endomorphism of the left
factor is zero or the whole space when the right factor is irreducible. -/
theorem tensor_submodule_eq_bot_or_top
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hσ : IsAlgebraicallyIrreducibleRepresentation σ)
    (U : Submodule k (V ⊗[k] W))
    (hU : IsInvariantSubmodule
      (algebraicAction (Representation.tprod
        ((Units.coeHom _).comp ρ.action) ((Units.coeHom _).comp σ.action))) U)
    (hleft : ∀ A : Module.End k V, ∀ z, z ∈ U → A.rTensor W z ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  let C : Submodule k W :=
    { carrier := {w | ∀ v : V, v ⊗ₜ[k] w ∈ U}
      zero_mem' := by intro v; simp
      add_mem' := by
        intro w₁ w₂ h₁ h₂ v
        rw [TensorProduct.tmul_add]
        exact U.add_mem (h₁ v) (h₂ v)
      smul_mem' := by
        intro c w hw v
        rw [TensorProduct.tmul_smul]
        exact U.smul_mem c (hw v) }
  have hC : IsInvariantSubmodule σ C := by
    intro g w hw v
    have hz := hU g _ (hw ((ρ.action g⁻¹).val v))
    change (ρ.action g).val ((ρ.action g⁻¹).val v) ⊗ₜ[k] (σ.action g).val w ∈ U at hz
    have hi : (ρ.action g).val ((ρ.action g⁻¹).val v) = v := by
      change ((ρ.action g).val * (ρ.action g⁻¹).val) v = v
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rwa [hi] at hz
  rcases hσ C hC with hzero | htop
  · left
    apply eq_bot_iff.mpr
    intro z hz
    let b := Module.finBasis k V
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    change (TensorProduct.equivFinsuppOfBasisLeft b) z i = 0
    have hi : (TensorProduct.equivFinsuppOfBasisLeft b) z i ∈ C := by
      intro v
      rw [← rankOne_rTensor b i v z]
      exact hleft _ z hz
    simpa only [hzero, Submodule.mem_bot] using hi
  · right
    apply top_unique
    intro z _
    induction z using TensorProduct.induction_on with
    | zero => exact U.zero_mem
    | tmul v w =>
      have hw : w ∈ C := by rw [htop]; trivial
      exact hw v
    | add x y hx hy => exact U.add_mem (hx trivial) (hy trivial)

/-- Over an algebraically closed field, a family with no nontrivial common
invariant subspace generates the full endomorphism algebra. -/
theorem adjoin_eq_top_of_irreducible_family [Nontrivial V] {ι : Type*} (D : ι → Module.End k V)
    (hD : ∀ U : Submodule k V,
      (∀ i v, v ∈ U → D i v ∈ U) → U = ⊥ ∨ U = ⊤) :
    Algebra.adjoin k (Set.range D) = ⊤ := by
  let A := Algebra.adjoin k (Set.range D)
  let ρ : Representation k A V := A.val.toMonoidHom
  have : Representation.IsIrreducible ρ := by
    change IsSimpleOrder (Subrepresentation ρ)
    rw [isSimpleOrder_iff]
    constructor
    · refine ⟨⟨⊥, ⊤, ?_⟩⟩
      intro h
      have heq : (⊥ : Submodule k V) = ⊤ :=
        congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top heq
    · intro U
      rcases hD U.toSubmodule (fun i v hv =>
        U.apply_mem_toSubmodule ⟨D i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ hv) with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  have hdense := Representation.jacobson_density_surjective_isAlgClosed_rep ρ
  apply top_unique
  rw [← hdense]
  apply Algebra.adjoin_le
  rintro _ ⟨a, rfl⟩
  exact a.property


end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
