module
public import Theory.Representation.CyclicSeedTensor

/-!
# Pointwise centralizers of a binary tensor seed plane

If a product actor fixes the whole plane u ⊗ F₂² pointwise for u nonzero,
its first factor fixes u and its second factor acts trivially. Binary
scalars have no nontrivial units, so scalar cancellation between the two
factors cannot occur. This determines the correct scalar-cubic placement
in the original first tensor of Aschbacher–Smith 13.8.29–30, printed p.964.
-/

public section
open scoped TensorProduct
namespace Representation.CyclicSeedTensor
open QuadraticFourGroup.TensorClassification
variable {K I U W : Type*} [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]

/-- A pointwise fixed binary seed plane forces both original factor actions. -/
theorem fixed_seed_plane_factors
    (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (u : U) (hu : u ≠ 0) (g : K × I)
    (hfix : ∀ v, externalTensor σ μ g (u ⊗ₜ[ZMod 2] v) = u ⊗ₜ[ZMod 2] v) :
    σ g.1 u = u ∧ μ g.2 = 1 := by
  have hc (v : Fin 2 → ZMod 2) (j : Fin 2) :
      (μ g.2 v) j • σ g.1 u = v j • u := by
    have hh := congrArg (fun z => TensorProduct.piScalarRight (ZMod 2) (ZMod 2) U (Fin 2) z j)
      (hfix v)
    simpa only [externalTensor_apply,TensorProduct.map_tmul,
      TensorProduct.piScalarRight_apply,TensorProduct.piScalarRightHom_tmul] using hh
  have hz : (μ g.2 first) 0 • σ g.1 u = u := by
    simpa only [first,Pi.single_eq_same,one_smul] using hc first 0
  have hn : (μ g.2 first) 0 ≠ 0 := by
    intro hzero
    rw [hzero,zero_smul] at hz
    exact hu hz.symm
  have ho : (μ g.2 first) 0 = 1 :=
    (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hn
  have hleft : σ g.1 u = u := by simpa only [ho,one_smul] using hz
  refine ⟨hleft,?_⟩
  apply LinearMap.ext
  intro v
  funext j
  change (μ g.2 v) j = v j
  exact smul_left_injective (ZMod 2) hu (by simpa only [hleft] using hc v j)

/-- The conclusion respects any equivariant tensor coordinates. -/
theorem fixed_marked_seed_plane_factors
    (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (ρ : Representation (ZMod 2) (K × I) W) (e : (externalTensor σ μ).Equiv ρ)
    (u : U) (hu : u ≠ 0) (g : K × I)
    (hfix : ∀ v, ρ g (e (u ⊗ₜ[ZMod 2] v)) = e (u ⊗ₜ[ZMod 2] v)) :
    σ g.1 u = u ∧ μ g.2 = 1 := by
  apply fixed_seed_plane_factors σ μ u hu g
  intro v
  apply e.injective
  exact (IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g _).trans (hfix v)

end Representation.CyclicSeedTensor
