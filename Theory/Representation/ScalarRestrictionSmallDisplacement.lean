module
public import Theory.Representation.SchurDisplacement
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel

/-!
# Small normalizer displacement in a scalar restriction

Suppose an irreducible normal subgroup acts through an actual representation
over an extension F of the binary field. A normalizing actor whose moved
space is smaller than half the module and smaller than the degree of F
acts trivially. The actor need not be an involution or be F-linear a priori.

The Schur-displacement bound first forces the actor to commute with every
component endomorphism. Transported F-scalars are such endomorphisms, so
the actor is F-linear. Its displacement dimension is therefore divisible
by the coefficient-field degree, and the strict upper bound makes it zero.

Source application: Aschbacher–Smith, Lemma 13.5.21, printed pp.923–924,
the natural SU₃(2^n) row with n>=2 and its original displacement-two actor.
This proves a consequence of that marking, not an exclusion of the valid
unmarked row of Table B.4.5.
-/

open Subgroup
namespace Representation

variable {G V W F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Field F] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module F W]
  [Module (ZMod 2) W] [IsScalarTower (ZMod 2) F W]

/-- A sufficiently small normalizer displacement vanishes when the irreducible
layer action is a genuine scalar restriction over a larger coefficient field. -/
public theorem small_displacement_eq_one_of_scalar_restriction
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [IsIrreducible (ρ.comp L.subtype)]
    (σ : Representation F L W) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ (g : L) (v : V), e (ρ g v) = σ g (e v))
    (t : G) (ht : t ∈ normalizer (L : Set G))
    (hhalf : 2 * Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) <
      Module.finrank (ZMod 2) V)
    (hfield : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) <
      Module.finrank (ZMod 2) F) : ρ t = 1 := by
  have hschur : IsSchurLinear ρ L t := by
    by_contra h
    exact (not_le_of_gt hhalf) (finrank_le_twice_displacement_of_not_isSchurLinear ρ L t ht h)
  let scalar (c : F) : IntertwiningMap (ρ.comp L.subtype) (ρ.comp L.subtype) := {
    toLinearMap := e.symm.toLinearMap.comp
      (((c • (LinearMap.id : Module.End F W)).restrictScalars (ZMod 2)).comp e.toLinearMap)
    isIntertwining' := by
      intro g
      ext v
      apply e.injective
      change e (e.symm (c • e (ρ g v))) = e (ρ g (e.symm (c • e v)))
      rw [e.apply_symm_apply, he, he, e.apply_symm_apply, map_smul] }
  let T : Module.End (ZMod 2) W := e.toLinearMap.comp ((ρ t).comp e.symm.toLinearMap)
  have hscalar (c : F) (v : W) : T (c • v) = c • T v := by
    have hh := LinearMap.congr_fun (hschur (scalar c)).eq (e.symm v)
    apply_fun e at hh
    simpa only [scalar, T, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply,
      e.apply_symm_apply, Module.End.mul_apply] using hh
  let δ : W →ₗ[F] W := {
    toFun := fun v => T v - v
    map_add' := by intro v w; simp only [map_add]; abel
    map_smul' := by intro c v; simp only [hscalar,smul_sub]; rfl }
  have hδ : δ.restrictScalars (ZMod 2) =
      e.toLinearMap.comp ((ρ t - 1).comp e.symm.toLinearMap) := by
    ext v
    change e (ρ t (e.symm v)) - v = e (ρ t (e.symm v) - e.symm v)
    rw [map_sub,e.apply_symm_apply]
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) =
      Module.finrank (ZMod 2) (δ.restrictScalars (ZMod 2)).range := by
    rw [hδ, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e.symm.range]
    exact (Submodule.equivMapOfInjective e.toLinearMap e.injective _).finrank_eq
  have hprod : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) =
      Module.finrank (ZMod 2) F * Module.finrank F δ.range := by
    rw [hr,LinearMap.range_restrictScalars]
    have heq := ((Submodule.restrictScalarsEquiv (ZMod 2) F W δ.range).restrictScalars
      (ZMod 2)).finrank_eq
    rw [heq,Module.finrank_mul_finrank]
  have hzero : Module.finrank F δ.range=0 := by
    by_contra hh
    have hp : 1≤Module.finrank F δ.range := Nat.one_le_iff_ne_zero.mpr hh
    have hge := Nat.mul_le_mul_left (Module.finrank (ZMod 2) F) hp
    rw [mul_one,←hprod] at hge
    omega
  have hz : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1))=0 := by rw [hprod,hzero,mul_zero]
  exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
end Representation
