module

public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.EndFieldRep
public import Theory.Representation.ScalarDescent

/-!
# Scalar transport for the rank-one model comparisons

Actual representation equivalences commute with extension of scalars, and the
tensor associator intertwines successive extensions. In Schur degree one the
map `a ⊗ v ↦ a • v` identifies the extension to the endomorphism field with the
Schur representation. Its explicit section proves surjectivity, and the scalar
dimension tower proves injectivity.

These maps connect the algebraic-closure comparison with the scalar extension
to the defining field in Aschbacher--Smith, G.9.3(16), printed p.354, and the
field-of-definition discussion in GLS volume 3, §2.8.8.
-/

public section

open scoped MatrixGroups MonoidAlgebra TensorProduct
namespace Representation.SL2.BinarySmall
noncomputable section

section BaseChange
variable {R S G W W' : Type*} [Field R] [Field S] [Algebra R S] [Group G]
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
  {ρ : Representation R G W} {τ : Representation R G W'}

/-- Extending an actual intertwiner extends the representation equivalence. -/
def baseChangeRepEquiv (d : ρ.Equiv τ) : (extendScalars S ρ).Equiv (extendScalars S τ) := by
  refine Representation.Equiv.mk (d.toLinearEquiv.baseChange R S W W') ?_
  intro g
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a v =>
    simpa [extendScalars_apply, LinearMap.baseChange_tmul] using
      congrArg (fun v => a ⊗ₜ[R] v)
        (Representation.IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap g v)
end BaseChange

section Tower
variable {R S F G W : Type*} [Field R] [Field S] [Field F]
  [Algebra R S] [Algebra S F] [Algebra R F] [IsScalarTower R S F]
  [Group G] [AddCommGroup W] [Module R W]

/-- The tensor associativity map intertwines successive scalar extensions. -/
def scalarTowerRepEquiv (ρ : Representation R G W) :
    (extendScalars F (extendScalars S ρ)).Equiv (extendScalars F ρ) := by
  refine Representation.Equiv.mk (TensorProduct.AlgebraTensorModule.cancelBaseChange R S F F W) ?_
  intro g
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a v =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy
    | tmul b v => simp [extendScalars_apply, LinearMap.baseChange_tmul]
end Tower

end
end Representation.SL2.BinarySmall

namespace Representation.SL2.BinarySmall
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]
local instance schurOneBinaryAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- In Schur degree one, evaluation of scalar endomorphisms identifies scalar
extension to the Schur field with the actual Schur representation. -/
def schurOneBaseChangeEquiv (hs : Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = 1) :
    (extendScalars (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) ρ).Equiv
      ρ.endFieldRep := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let L := LinearMap.liftBaseChange E ρ.asModuleEquiv.symm.toLinearMap
  have hsurj : Function.Surjective L := by
    intro v
    exact ⟨1 ⊗ₜ[ZMod 2] ρ.asModuleEquiv v, by simp [L]⟩
  have hdim : Module.finrank E (E ⊗[ZMod 2] V) = Module.finrank E ρ.asModule := by
    rw [Module.finrank_baseChange]
    have ht := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [hs, one_mul] at ht
    exact ρ.asModuleEquiv.finrank_eq.symm.trans ht.symm
  have hbij : Function.Bijective L :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  refine Representation.Equiv.mk (LinearEquiv.ofBijective L hbij) (fun g => ?_)
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a v =>
    simp [L, extendScalars_apply, LinearMap.baseChange_tmul, endFieldRep_apply]

end
end Representation.SL2.BinarySmall
