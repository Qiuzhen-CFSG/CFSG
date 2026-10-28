module

public import Theory.Representation.EndFieldDegree
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Involution displacement over the actual endomorphism field

For an irreducible representation over a finite field, the existing
endomorphism-field action is absolutely irreducible and remains faithful.
The original vector-space equivalence restricts to an equivalence of the
ranges of the literal operators `τ t - id`. Their dimensions therefore
satisfy the scalar tower law, including the original binary field degree.

Consequently an absolute involution estimate for a fixed group implies the
same estimate for every irreducible action over a finite coefficient field.
The group, element and action are retained; no absolute irreducibility of
the original action is required.

Source: the scalar-field reduction used by Guralnick--Malle,
*Classification of 2F-modules, II*, §§3.1 and 8.3, in particular Lemma 8.6.
The model-specific bound is an explicit prerequisite, not a conclusion here.
-/

@[expose] public section

open scoped MonoidAlgebra
open Representation

namespace Triality.InnerDisplacement
variable {F G V : Type*} [Field F] [Finite F] [Group G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  (ρ : Representation F G V) [ρ.IsIrreducible]

/-- The same displacement vectors, viewed over the original field. -/
private noncomputable def rangeEquiv (t : G) :
    LinearMap.range (ρ.endFieldRep t - LinearMap.id) ≃ₗ[F]
      LinearMap.range (ρ t - LinearMap.id) where
  toFun v := ⟨ρ.asModuleEquiv v, by
    obtain ⟨w, hw⟩ := v.property
    exact ⟨ρ.asModuleEquiv w, congrArg ρ.asModuleEquiv hw⟩⟩
  invFun v := ⟨ρ.asModuleEquiv.symm v, by
    obtain ⟨w, hw⟩ := v.property
    exact ⟨ρ.asModuleEquiv.symm w, congrArg ρ.asModuleEquiv.symm hw⟩⟩
  left_inv v := Subtype.ext (ρ.asModuleEquiv.symm_apply_apply v)
  right_inv v := Subtype.ext (ρ.asModuleEquiv.apply_symm_apply v)
  map_add' x y := Subtype.ext (map_add ρ.asModuleEquiv (x : ρ.asModule) (y : ρ.asModule))
  map_smul' a v := Subtype.ext (map_smul ρ.asModuleEquiv a (v : ρ.asModule))

/-- Displacement dimension multiplies by the degree of the Schur field. -/
theorem displacement_eq_endField_mul (t : G) :
    Module.finrank F (LinearMap.range (ρ t - LinearMap.id)) =
      Module.finrank F (Module.End F[G] ρ.asModule) *
        Module.finrank (Module.End F[G] ρ.asModule)
          (LinearMap.range (ρ.endFieldRep t - LinearMap.id)) := by
  rw [Module.finrank_mul_finrank F (Module.End F[G] ρ.asModule)]
  exact (rangeEquiv ρ t).finrank_eq.symm

variable [Algebra (ZMod 2) F]
  [Algebra (ZMod 2) (Module.End F[G] ρ.asModule)]

/-- Binary displacement is unchanged after enlarging the coefficient field. -/
theorem binary_displacement_eq_endField (t : G) :
    Module.finrank (ZMod 2) F * Module.finrank F (LinearMap.range (ρ t - LinearMap.id)) =
      Module.finrank (ZMod 2) (Module.End F[G] ρ.asModule) *
        Module.finrank (Module.End F[G] ρ.asModule)
          (LinearMap.range (ρ.endFieldRep t - LinearMap.id)) := by
  rw [displacement_eq_endField_mul ρ t, ← mul_assoc, Module.finrank_mul_finrank]

end Triality.InnerDisplacement

namespace Triality.InnerDisplacement
universe u v

/-- The remaining bound for absolutely irreducible actions on a fixed group.
This definition makes no assertion that the estimate holds. -/
def AbsoluteBound (G : Type u) [Group G] (b : ℕ) : Prop :=
  ∀ (E W : Type v) [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (τ : Representation E G W),
    IsAbsolutelyIrreducible τ → Function.Injective τ →
    ∀ t : G, t ≠ 1 → t ^ 2 = 1 →
      b < Module.finrank (ZMod 2) E *
        Module.finrank E (LinearMap.range (τ t - LinearMap.id))

/-- An absolute bound descends with the exact coefficient-field factor. -/
theorem of_absoluteBound {G : Type u} [Group G] {b : ℕ}
    (h : AbsoluteBound.{u, v} G b)
    {E W : Type v} [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (τ : Representation E G W) [τ.IsIrreducible] (hf : Function.Injective τ)
    (t : G) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    b < Module.finrank (ZMod 2) E *
      Module.finrank E (LinearMap.range (τ t - LinearMap.id)) := by
  let K := Module.End E[G] τ.asModule
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap E K).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Finite τ.asModule := Module.finite_of_finite E
  let : FiniteDimensional K τ.asModule := Module.Finite.of_finite
  rw [binary_displacement_eq_endField τ t]
  exact h K τ.asModule τ.endFieldRep (endFieldRep_isAbsolutelyIrreducible τ)
    ((endFieldRep_injective_iff τ).mpr hf) t ht ht2
end Triality.InnerDisplacement
