module

public import Theory.SpecificGroups.BinaryLinear.NestedRadicals

/-!
# The common radical of a line and a larger binary subspace

Let W < U with W a line. An element in both parabolic radicals is a
rank-one transvection wβ with β vanishing on U. Choose y in U outside W
and a functional α vanishing on W with α(y) = 1. Then wβ is the
commutator of wα in the W-radical and yβ in the U-radical.

This extends the checked two-dimensional calculation in `NestedRadicals`
to the 1+3+1 flag used in Aschbacher–Smith E.6.8, printed pp.247–248
(combined manuscript of 1 March 2004). It uses the actual linear actions.
-/

public section

open Subgroup
open scoped commutatorElement
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem line_cross_commutator (w y : V)
    (α β : V →ₗ[ZMod 2] ZMod 2)
    (hαw : α w = 0) (hβw : β w = 0) (hβy : β y = 0) (hαy : α y = 1) :
    ⁅transvection w α hαw, transvection y β hβy⁆ = transvection w β hβw := by
  ext v
  change (v + β v • y + α (v + β v • y) • w +
    β (v + β v • y + α (v + β v • y) • w) • y +
    α (v + β v • y + α (v + β v • y) • w +
      β (v + β v • y + α (v + β v • y) • w) • y) • w) = v + β v • w
  simp only [map_add, map_smul, hαw, hβw, hβy, hαy, smul_eq_mul, mul_zero,
    mul_one, add_zero]
  match_scalars <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      mul_zero, mul_one, zero_add]

/-- For a line inside a larger space, the common radical consists of cross commutators. -/
theorem radical_inf_le_commutator_of_finrank_one
    {W U : Submodule (ZMod 2) V} [FiniteDimensional (ZMod 2) W]
    (hdim : Module.finrank (ZMod 2) W = 1) (hWU : W < U) :
    radical W ⊓ radical U ≤ ⁅radical W, radical U⁆ := by
  classical
  obtain ⟨y, hyU, hyW⟩ := SetLike.exists_of_lt hWU
  obtain ⟨α, hαy, hαW⟩ := W.exists_le_ker_of_notMem hyW
  have hαy1 : α y = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hαy
  intro g hg
  let d : V →ₗ[ZMod 2] W := (g.toLinearMap - LinearMap.id).codRestrict W hg.1.2
  let b : Module.Basis (Fin 1) (ZMod 2) W := Module.finBasisOfFinrankEq (ZMod 2) W hdim
  let β : V →ₗ[ZMod 2] ZMod 2 := (b.coord 0).comp d
  have hβU : U ≤ β.ker := by
    intro u hu
    have hdu : d u = 0 := by
      apply Subtype.ext
      change g u - u = 0
      rw [hg.2.1 u hu, sub_self]
    change b.coord 0 (d u) = 0
    rw [hdu, map_zero]
  have he : g = transvection (b 0 : V) β (hβU (hWU.le (b 0).property)) := by
    ext v
    have hsum := congrArg (fun w : W => (w : V)) (b.sum_repr (d v))
    simp only [Fin.sum_univ_one, Submodule.coe_smul] at hsum
    change β v • (b 0 : V) = g v - v at hsum
    change g v = v + β v • (b 0 : V)
    rw [hsum]
    module
  rw [he, ← line_cross_commutator (b 0 : V) y α β (hαW (b 0).property)
    (hβU (hWU.le (b 0).property)) (hβU hyU) hαy1]
  exact commutator_mem_commutator (transvection_mem (b 0).property hαW)
    (transvection_mem hyU hβU)
end BinaryLinear

end
