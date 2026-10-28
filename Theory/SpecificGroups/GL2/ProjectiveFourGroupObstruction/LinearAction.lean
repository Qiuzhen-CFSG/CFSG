module

public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.ElementaryAbelian.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.Finiteness
/-!
# Four-groups on elementary abelian groups of rank two

An elementary abelian group V of order p² is explicitly linearized over ZMod p.
A basis identifies its full automorphism group with GL₂(p). Transport of the
scalar involution theorem shows that every faithful four-group of automorphisms
contains inversion on V when p is odd.

Source: the linear action underlying the two obstructions at the end of
Aschbacher–Smith §13.1, printed p.876.
-/

namespace IsElementaryAbelian

open scoped IsMulCommutative
open Matrix

private noncomputable def autLinear {p : ℕ} [Fact p.Prime] {V : Type*} [Group V]
    [IsElementaryAbelian p V] : MulAut V ≃* (Additive V ≃ₗ[ZMod p] Additive V) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      invFun := fun a => MulEquiv.toAdditive.symm a.toAddEquiv
      left_inv := by intro a; ext; rfl
      right_inv := by intro a; ext; rfl
      map_mul' := by intro a b; ext; rfl }

/-- A faithful four-group of automorphisms of an elementary abelian group of
order p², p odd, contains inversion. -/
public theorem exists_inverting_of_four_group {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V E : Type*} [Group V] [Finite V]
    [IsElementaryAbelian p V] [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hV : Nat.card V = p ^ 2) (hE : Nat.card E = 4)
    (f : E →* MulAut V) (hf : Function.Injective f) :
    ∃ a : E, a ≠ 1 ∧ ∀ v : V, f a v = v⁻¹ := by
  have hdim : Module.finrank (ZMod p) (Additive V) = 2 := by
    have hs := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    have he : p ^ Module.finrank (ZMod p) (Additive V) = p ^ 2 := by
      change Nat.card V = _ at hs
      simpa only [Nat.card_zmod, hV] using hs.symm
    exact Nat.pow_right_injective (Fact.out : p.Prime).one_lt he
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive V) hdim
  let e : GL (Fin 2) (ZMod p) ≃* (Additive V ≃ₗ[ZMod p] Additive V) :=
    (Units.mapEquiv (Matrix.toLinAlgEquiv b).toMulEquiv).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)
  let g : E →* GL (Fin 2) (ZMod p) := e.symm.toMonoidHom.comp (autLinear.toMonoidHom.comp f)
  have hg : Function.Injective g := e.symm.injective.comp (autLinear.injective.comp hf)
  have hp' : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (Fact.out : p.Prime).ne_one)
  obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.exists_neg_one_of_four_group hp' hE g hg
  have he : autLinear (f a) = e (-1) := by
    have := congrArg e ha
    simpa [g] using this
  have hinv (v : V) : f a v = v⁻¹ := by
    change (autLinear (p := p) (f a)) (Additive.ofMul v) = -Additive.ofMul v
    rw [he]
    simp [e, LinearMap.GeneralLinearGroup.generalLinearEquiv,
      LinearMap.GeneralLinearGroup.toLinearEquiv]
  refine ⟨a, ?_, hinv⟩
  intro h
  have hz : (1 : GL (Fin 2) (ZMod p)) = -1 := by simpa [h] using ha
  have hh : (1 : ZMod p) = -1 := congrArg (fun m : GL (Fin 2) (ZMod p) => m.val 0 0) hz
  exact hp' (by linear_combination hh)

end IsElementaryAbelian
