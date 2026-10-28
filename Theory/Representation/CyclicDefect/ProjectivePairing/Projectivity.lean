module

public import Theory.Representation.ProjectiveTrace
public import Mathlib.RepresentationTheory.Rep.Iso


/-!
# Projectivity of representations on linear maps

A genuine projective splitting is a retract of the free group representation.
Projection to its identity coefficient has group norm equal to the identity;
the retraction therefore gives such a norm witness on every projective module.
Precomposing linear maps by this witness gives a norm witness for `linHom P ρ`.
The trace criterion then proves that this representation is projective.

This supplies the tensor-projectivity step in Feit IV.3.3, without assuming
projective lifts, scalar-product positivity, or semisimplicity in characteristic
`p`. It also allows arbitrary target representations, including tensor products.
-/

public section

noncomputable section
open scoped BigOperators MonoidAlgebra
namespace Representation.CyclicDefect.ProjectivePairing
variable {K G : Type*} [Field K] [Group G] [Fintype G]

private def coeffOne : MonoidAlgebra K G →ₗ[K] MonoidAlgebra K G :=
  (MonoidAlgebra.lsingle (1 : G)).comp
    ((Finsupp.lapply (1 : G)).comp (MonoidAlgebra.coeffLinearEquiv K).toLinearMap)

private def freeProjection (α : Type*) : Module.End K (α →₀ MonoidAlgebra K G) :=
  Finsupp.mapRange.linearMap (coeffOne (K := K) (G := G))

private theorem freeProjection_norm (α : Type*) (v : α →₀ MonoidAlgebra K G) :
    ∑ g : G, (Representation.free K G α) g⁻¹
      (freeProjection α ((Representation.free K G α) g v)) = v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]
  | single i x =>
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [Finsupp.single_add, map_add, Finset.sum_add_distrib, hx, hy]
    | single h r =>
      have ht (g : G) : (Representation.free K G α) g⁻¹
          (freeProjection α ((Representation.free K G α) g
            (Finsupp.single i (MonoidAlgebra.single h r)))) =
          if g = h⁻¹ then Finsupp.single i (MonoidAlgebra.single h r) else 0 := by
        simp only [Representation.free_single_single, freeProjection,
          Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, coeffOne,
          LinearMap.comp_apply, Finsupp.lapply_apply, MonoidAlgebra.coeffLinearEquiv]
        by_cases hg : g = h⁻¹
        · subst g
          simp
        · have hne : g * h ≠ 1 := fun hh => hg (eq_inv_of_mul_eq_one_left hh)
          simp [hne, hg]
      simp_rw [ht]
      simp

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The converse to the norm criterion, obtained from a genuine projective splitting. -/
theorem exists_norm (ρ : Representation K G V)
    [Module.Projective (MonoidAlgebra K G) ρ.asModule] :
    ∃ θ : Module.End K V, ∀ v, ∑ g : G, ρ g⁻¹ (θ (ρ g v)) = v := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective (MonoidAlgebra K G) ρ.asModule).out
  let F := Representation.free K G ρ.asModule
  let e := Representation.finsuppLEquivFreeAsModule K G ρ.asModule
  let i0 : ρ.asModule →ₗ[MonoidAlgebra K G] F.asModule := e.toLinearMap.comp s
  let q0 : F.asModule →ₗ[MonoidAlgebra K G] ρ.asModule :=
    (Finsupp.linearCombination (MonoidAlgebra K G) id).comp e.symm.toLinearMap
  let i : ρ.IntertwiningMap F := (IntertwiningMap.equivLinearMapAsModule ρ F).symm i0
  let q : F.IntertwiningMap ρ := (IntertwiningMap.equivLinearMapAsModule F ρ).symm q0
  have hqi (v : V) : q (i v) = v := by
    change ρ.asModuleEquiv (q0 (i0 (ρ.asModuleEquiv.symm v))) = v
    simpa [q0, i0, LinearMap.comp_apply] using congrArg ρ.asModuleEquiv (hs (ρ.asModuleEquiv.symm v))
  refine ⟨q.toLinearMap.comp ((freeProjection ρ.asModule).comp i.toLinearMap), fun v => ?_⟩
  change (∑ g : G, ρ g⁻¹ (q (freeProjection ρ.asModule (i (ρ g v))))) = v
  simp_rw [← q.isIntertwining, i.isIntertwining]
  rw [← map_sum, freeProjection_norm, hqi]

variable {W : Type*} [AddCommGroup W] [Module K W]

/-- Linear maps out of a projective representation form a projective representation. -/
theorem projective_linHom (P : Representation K G V) (ρ : Representation K G W)
    [Module.Projective (MonoidAlgebra K G) P.asModule] :
    Module.Projective (MonoidAlgebra K G) (linHom P ρ).asModule := by
  obtain ⟨θ, hθ⟩ := exists_norm P
  let T : Module.End K (V →ₗ[K] W) :=
    { toFun := fun f => f.comp θ
      map_add' := fun f h => by ext; simp
      map_smul' := fun r f => by ext; simp }
  apply ProjectiveTrace.projective_of_norm (linHom P ρ) T
  intro f
  ext v
  have he (g : G) : (linHom P ρ g⁻¹ (T (linHom P ρ g f))) v =
      f (P g⁻¹ (θ (P g v))) := by
    simp only [linHom_apply, T, LinearMap.comp_apply, inv_inv]
    change (ρ g⁻¹ * ρ g) (f (P g⁻¹ (θ (P g v)))) = _
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [LinearMap.sum_apply, he, ← map_sum, hθ]
end Representation.CyclicDefect.ProjectivePairing
