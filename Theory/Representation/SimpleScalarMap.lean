module

public import Theory.Representation.EndFieldRep
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Extending a nonzero map into a simple action

An equivariant map from a base-field module extends by scalar multiplication
to the coefficient field. Simplicity of the target makes this map surjective.
Equal dimensions therefore give an actual scalar-extension equivalence.
These elementary maps are used by the arbitrary-field A₆ four-space recognition.
-/
open scoped TensorProduct
open Representation Module
@[expose] public noncomputable section
namespace Representation.SimpleScalarMap
variable {k F G U V : Type*} [Field k] [Field F] [Algebra k F]
 [Group G] [AddCommGroup U] [Module k U] [FiniteDimensional k U]
 [AddCommGroup V] [Module F V] [Module k V] [IsScalarTower k F V]
 [FiniteDimensional F V]
def extendMap (σ : Representation k G U) (ρ : Representation F G V)
 (i : U →ₗ[k] V) (hc : ∀ g u, i (σ g u) = ρ g (i u)) :
 (extendScalars F σ).IntertwiningMap ρ where
 toLinearMap := TensorProduct.AlgebraTensorModule.lift
   { toFun := fun c => c • i
     map_add' := fun _ _ => add_smul _ _ _
     map_smul' := fun _ _ => mul_smul _ _ _ }
 isIntertwining' g := by
   apply TensorProduct.AlgebraTensorModule.ext
   intro c u
   change c • i (σ g u) = ρ g (c • i u)
   rw [hc,map_smul]
omit [FiniteDimensional F V] in
theorem finrank_le (σ : Representation k G U) (ρ : Representation F G V) [ρ.IsIrreducible]
 (i : U →ₗ[k] V) (hi : i ≠ 0)
 (hc : ∀ g u, i (σ g u) = ρ g (i u)) :
 Module.finrank F V ≤ Module.finrank k U := by
 let f := extendMap σ ρ i hc
 have hf : f ≠ 0 := by
   intro h
   apply hi
   ext u
   have hh := congrArg (fun q : (extendScalars F σ).IntertwiningMap ρ =>
     q (1 ⊗ₜ[k] u)) h
   simpa [f,extendMap] using hh
 have hs := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
 have hd := LinearMap.finrank_le_finrank_of_surjective hs
 simpa only [Module.finrank_baseChange] using hd
theorem equiv_of_finrank_eq (σ : Representation k G U) (ρ : Representation F G V) [ρ.IsIrreducible]
 (i : U →ₗ[k] V) (hi : i ≠ 0)
 (hc : ∀ g u, i (σ g u) = ρ g (i u))
 (hd : Module.finrank k U = Module.finrank F V) :
 Nonempty ((extendScalars F σ).Equiv ρ) := by
 let f := extendMap σ ρ i hc
 have hf : f ≠ 0 := by
   intro h
   apply hi
   ext u
   have hh := congrArg (fun q : (extendScalars F σ).IntertwiningMap ρ =>
     q (1 ⊗ₜ[k] u)) h
   simpa [f,extendMap] using hh
 have hs := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
 exact ⟨f.ofBijective ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
   (by simpa only [Module.finrank_baseChange] using hd)).mpr hs,hs⟩⟩

end Representation.SimpleScalarMap
