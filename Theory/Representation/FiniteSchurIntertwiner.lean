module

public import Theory.Representation.EndFieldRep
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Coefficient linearity from the finite Schur field

For an irreducible representation over a finite field, Schur's lemma and
Wedderburn's little theorem make its commuting ring a field. Thus every
commuting endomorphism commutes with any larger coefficient field acting on
the module. In particular, two intertwiners for the same change of actors
have the same coefficient semilinearity if one is invertible.

The field structure is supplied by `Representation.endField_field`.
The natural SU₃ application recovers the compatible module and matrix field
actions used in Aschbacher–Smith, K.3.3, printed p.456.
-/

public section

namespace Representation.FiniteSchurIntertwiner
variable {k F H W : Type*} [Field k] [Finite k] [Monoid H]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (τ : Representation k H W) [IsIrreducible τ]

/-- The endomorphisms of a finite irreducible representation commute. -/
theorem commute (f q : IntertwiningMap τ τ) (v : W) : f (q v) = q (f v) := by
  have he : f * q = q * f := by
    apply (IntertwiningMap.equivAlgEnd τ).injective
    rw [map_mul, map_mul, mul_comm]
  exact congrArg (fun t : IntertwiningMap τ τ => t v) he

variable [Field F] [Module F W] [SMulCommClass F k W]

/-- A commuting endomorphism is linear over any commuting coefficient field. -/
theorem map_smul (hτ : ∀ (x : H) (c : F) (v : W), τ x (c • v) = c • τ x v)
    (f : W →ₗ[k] W) (hf : ∀ (x : H) (v : W), f (τ x v) = τ x (f v))
    (c : F) (v : W) : f (c • v) = c • f v := by
  let q : W →ₗ[k] W :=
    { toFun := fun v => c • v
      map_add' := smul_add c
      map_smul' := fun a v => smul_comm c a v }
  exact commute τ (f.intertwiningMap_of_isIntertwiningMap τ τ hf)
    (q.intertwiningMap_of_isIntertwiningMap τ τ (fun x v => (hτ x c v).symm)) v

/-- Two operators implementing the same change of actors have the same coefficient
semilinearity when one is invertible. The quotient of the operators commutes
with the irreducible representation and therefore with its coefficient scalars. -/
theorem semilinear_of_intertwining
    (hτ : ∀ (x : H) (c : F) (v : W), τ x (c • v) = c • τ x v)
    (a : H → H) (A : W →ₗ[k] W) (B : W ≃ₗ[k] W) (σ : F ≃+* F)
    (hA : ∀ (x : H) (v : W), A (τ x v) = τ (a x) (A v))
    (hB : ∀ (x : H) (v : W), B (τ x v) = τ (a x) (B v))
    (hσ : ∀ (c : F) (v : W), B (c • v) = σ c • B v)
    (c : F) (v : W) : A (c • v) = σ c • A v := by
  let f : W →ₗ[k] W := B.symm.toLinearMap.comp A
  have hf (x : H) (v : W) : f (τ x v) = τ x (f v) := by
    apply B.injective
    change B (B.symm (A (τ x v))) = B (τ x (B.symm (A v)))
    rw [B.apply_symm_apply, hB, B.apply_symm_apply, hA]
  have hc := map_smul τ hτ f hf c v
  have he := congrArg B hc
  simpa only [hσ, f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using he
end Representation.FiniteSchurIntertwiner
