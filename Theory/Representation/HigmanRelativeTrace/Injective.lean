module
public import Theory.Representation.HigmanRelativeTrace
public import Mathlib.Algebra.Module.Injective

/-!
# Injectivity from a relative trace

A linear endomorphism with group trace equal to the identity also proves
injectivity. Extend a map linearly from a subspace, compose with the trace
seed, and sum its conjugates. The resulting equivariant extension agrees
with the original map. No division by the group order occurs.

This is the injective form of Higman's trace criterion, used to split the
deleted A₅ isotypic part in Aschbacher--Smith 5.1.14 and 5.1.19.
-/

public noncomputable section
open scoped MonoidAlgebra

namespace ModularBlock.HigmanRelativeTrace

set_option backward.isDefEq.respectTransparency false in
theorem injective_of_relative_trace_id
    {k G M : Type*} [Field k] [Group G] [Fintype G]
    [AddCommGroup M] [Module k M] [Module k[G] M]
    [IsScalarTower k k[G] M]
    (a : M →ₗ[k] M) (ha : ∑ g : G, a.conjugate g = LinearMap.id) :
    Module.Injective k[G] M := by
  constructor
  intro X Y _ _ _ _ i hi f
  let : Module k X := Module.compHom X (algebraMap k k[G])
  let : Module k Y := Module.compHom Y (algebraMap k k[G])
  let := IsScalarTower.of_compHom k k[G] X
  let := IsScalarTower.of_compHom k k[G] Y
  obtain ⟨r, hr⟩ := (i.restrictScalars k).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi)
  let b := a.comp ((f.restrictScalars k).comp r)
  refine ⟨b.sumOfConjugatesEquivariant G, ?_⟩
  intro x
  rw [LinearMap.sumOfConjugatesEquivariant_apply]
  simp only [LinearMap.conjugate_apply]
  calc
    _ = ∑ g : G, MonoidAlgebra.single g⁻¹ (1 : k) •
        a (MonoidAlgebra.single g (1 : k) • f x) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [← i.map_smul]
      change _ • a (f (r (i (_ • x)))) = _
      rw [show r (i (MonoidAlgebra.single g (1 : k) • x)) = _ from
        LinearMap.congr_fun hr _]
      rw [LinearMap.id_apply, f.map_smul]
    _ = (∑ g : G, a.conjugate g) (f x) := by
      simp only [LinearMap.sum_apply, LinearMap.conjugate_apply]
    _ = f x := by rw [ha]; rfl
end ModularBlock.HigmanRelativeTrace

