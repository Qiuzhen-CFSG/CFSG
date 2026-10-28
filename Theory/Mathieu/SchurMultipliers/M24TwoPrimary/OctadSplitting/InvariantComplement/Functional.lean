module

public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.FirstCohomologyDuality
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Fixed functionals over the natural binary four-space

The dot product identifies the contragredient natural SL₄(2) action with the
inverse-transpose twist of the natural action. Transport of the checked natural
cohomology calculation therefore gives H¹ = 0 on the dual, without a
self-duality assertion.

For an equivariant surjection with fixed kernel, the dual image is the kernel's
annihilator and has trivial quotient. Its vanishing first cohomology expresses
every functional as an annihilator functional plus a fixed functional. Starting
with value one on a nonzero kernel vector gives the required fixed functional.
This follows the fixed-functional argument of `M23TwoKernelSource.HeptadFunctional`,
using the natural SL₄(2) calculation in place of the A₇ representation theorem.

Source: Aschbacher–Smith, I.1.5 and I.1.6(6), printed p.408 (PDF p.419).
-/

@[expose] public section

open Representation Representation.OneCohomology Module Matrix
open scoped MatrixGroups
namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary.InvariantComplement
noncomputable section
abbrev Four := Fin 4 → ZMod 2
abbrev SL := SL(4, ZMod 2)
abbrev natural := specialLinearNatural (k := ZMod 2) 4

private theorem transpose_mul (g h : SL) : (g * h).transpose = h.transpose * g.transpose := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _
private theorem transpose_one : (1 : SL).transpose = 1 := by
  apply Subtype.ext
  exact Matrix.transpose_one
private theorem transpose_inv (g : SL) : g⁻¹.transpose = g.transpose⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← transpose_mul, mul_inv_cancel, transpose_one]

private def graphNaturalDual : Representation.Equiv
    (natural.comp (BinaryLinear.OuterCyclic.graphSL 4).toMonoidHom) natural.dual where
  toLinearEquiv := dotProductEquiv (ZMod 2) (Fin 4)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change ((g.transpose⁻¹).val *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (g⁻¹.val *ᵥ w)
    rw [← transpose_inv]
    change (g⁻¹.val.transpose *ᵥ v) ⬝ᵥ w = _
    rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.transpose_transpose]

/-- Inverse transpose transports natural cohomology vanishing to the dual module. -/
theorem dual_H1_subsingleton : Subsingleton (H1 natural.dual) := by
  let e := graphNaturalDual
  let a := BinaryLinear.OuterCyclic.graphSL 4
  have he : ∀ g v, e.symm (natural.dual g v) = natural (a g) (e.symm v) := by
    intro g v
    exact LinearMap.congr_fun (e.symm.isIntertwining' g) v
  let := SLHigherNatural.H1_subsingleton_of_four_le (K := ZMod 2) (d := 4) (by decide)
  exact (H1Congr _ _ a e.symm.toLinearEquiv he).injective.subsingleton

/-- A central extension of the natural four-space admits an invariant
functional taking value one on a prescribed nonzero kernel vector. -/
theorem exists_fixed_functional {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) SL W)
    (p : σ.IntertwiningMap natural) (hp : Function.Surjective p)
    (hk : p.toLinearMap.ker ≤ fixed σ)
    (z : W) (hz : p z = 0) (hzne : z ≠ 0) :
    ∃ ψ : Module.Dual (ZMod 2) W, ψ z = 1 ∧
      ∀ (a : SL) (w : W), ψ (σ a w) = ψ w := by
  let d := dualIntertwining p
  let U : Subrepresentation σ.dual := d.range
  have hU : U.toSubmodule = p.toLinearMap.ker.dualAnnihilator :=
    p.toLinearMap.range_dualMap_eq_dualAnnihilator_ker
  have hd : Function.Injective d := LinearMap.dualMap_injective_of_surjective hp
  let e : Module.Dual (ZMod 2) Four ≃ₗ[ZMod 2] U.toSubmodule :=
    LinearEquiv.ofBijective d.toLinearMap.rangeRestrict
      ⟨fun x y h => hd (congrArg Subtype.val h), by
        rintro ⟨y, x, hx⟩
        exact ⟨x, Subtype.ext hx⟩⟩
  have he (a : SL) (v : Module.Dual (ZMod 2) Four) :
      e (natural.dual a v) = U.toRepresentation a (e v) := by
    apply Subtype.ext
    exact LinearMap.congr_fun (d.isIntertwining' a) v
  have hH : Module.finrank (ZMod 2) (H1 (k := ZMod 2)
      (G := SL) (W := U.toSubmodule) U.toRepresentation) = 0 := by
    rw [← (H1Congr (k := ZMod 2) (G := SL)
      (H := SL) (V := Module.Dual (ZMod 2) Four)
      (W := U.toSubmodule) natural.dual U.toRepresentation
      (MulEquiv.refl _) e he).finrank_eq]
    let := dual_H1_subsingleton
    exact Module.finrank_zero_of_subsingleton
  let : Subsingleton (H1 (k := ZMod 2) (G := SL)
    (W := U.toSubmodule) U.toRepresentation) := Module.finrank_zero_iff.mp hH
  have ht : HasTrivialQuotient U := by
    intro a φ
    change σ.dual a φ - φ ∈ U.toSubmodule
    rw [hU, Submodule.mem_dualAnnihilator]
    intro w hw
    change φ (σ a⁻¹ w) - φ w = 0
    rw [hk hw a⁻¹, sub_self]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hzne
  have hs := (extensionClass_eq_zero_iff U ht φ).mp (Subsingleton.elim _ _)
  obtain ⟨l, hl, ψ, hψ, hsum⟩ := Submodule.mem_sup.mp hs
  have hlz : l z = 0 := by
    rw [hU] at hl
    rw [Submodule.mem_dualAnnihilator] at hl
    exact hl z hz
  refine ⟨ψ, ?_, ?_⟩
  · have h := congrArg (fun f : Module.Dual (ZMod 2) W => f z) hsum
    simpa only [LinearMap.add_apply, hlz, zero_add, hφ] using h
  · intro a w
    have h := congrArg (fun f : Module.Dual (ZMod 2) W => f w) (hψ a⁻¹)
    simpa only [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      LinearMap.comp_apply] using h

end
end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary.InvariantComplement
