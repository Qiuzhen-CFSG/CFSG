module

public import Theory.Representation.FiniteFieldSemilinearDisplacement.Descent
public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.Linarith

/-!
# Displacement of finite-field semilinear actors

A binary-linear actor of order `p`, semilinear for a coefficient-field
automorphism of the same order, has fixed binary dimension `n*d/p`.
We identify the two cyclic groups by their marked generators and apply the
constructed semilinear descent theorem. Rank-nullity gives displacement
`(p-1)*n*d/p`; for odd prime `p` this is at least `2*n*d/3`.

The equality only needs positive order. No faithfulness of the representation
or preselected fixed basis is required. The binary scalar actions are compatible
by the scalar-tower instance for modules over `ZMod 2`.

Source: Aschbacher–Smith, H.0.1, printed p.377, manuscript of 1 March 2004.
-/

public section

open Module

namespace Representation.FiniteFieldSemilinearDisplacement
open Representation.BinaryOffender
variable {F M V : Type*} [Field F] [Algebra (ZMod 2) F] [Group M]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V] [FiniteDimensional F V]

private def binaryAut : (F ≃+* F) →* (F ≃ₐ[ZMod 2] F) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ) (fun a => by
    exact congrArg (fun (f : ZMod 2 →+* F) => f a)
      (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) F))
        (algebraMap (ZMod 2) F)))
  map_one' := by ext a; rfl
  map_mul' := by intro σ τ; ext a; rfl

private theorem binaryAut_injective : Function.Injective (binaryAut (F := F)) := by
  intro σ τ h
  ext a
  exact congrArg (fun f : F ≃ₐ[ZMod 2] F => f a) h

variable [Finite F]

/-- Fixed-space dimension for an actor and coefficient automorphism of the same positive order. -/
theorem fixedSpace_formula (ρ : Representation (ZMod 2) M V)
    {p : ℕ} (hp : 0 < p) (x : M) (hx : orderOf x = p)
    (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hsemi : ∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v) :
    p * finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers x)) =
      finrank (ZMod 2) F * finrank F V := by
  classical
  let H := Subgroup.zpowers x
  let γ : H := ⟨x, Subgroup.mem_zpowers x⟩
  have hγ : ∀ y : H, y ∈ Subgroup.zpowers γ := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n, Subtype.ext hn⟩
  let δ : Subgroup.zpowers σ := ⟨σ, Subgroup.mem_zpowers σ⟩
  have hδ : ∀ y : Subgroup.zpowers σ, y ∈ Subgroup.zpowers δ := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n, Subtype.ext hn⟩
  have hord : orderOf γ = orderOf δ := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hx.trans hσ.symm
  let e : H ≃* Subgroup.zpowers σ := mulEquivOfOrderOfEq hγ hδ hord
  let τ : H →* (F ≃ₐ[ZMod 2] F) :=
    binaryAut.comp ((Subgroup.zpowers σ).subtype.comp e.toMonoidHom)
  have hτ : Function.Injective τ :=
    binaryAut_injective.comp (Subtype.val_injective.comp e.injective)
  have hτγ : τ γ = binaryAut σ := by
    change binaryAut ((mulEquivOfOrderOfEq hγ hδ hord γ : Subgroup.zpowers σ) : F ≃+* F) = _
    rw [mulEquivOfOrderOfEq_apply_gen]
  have hfin : IsOfFinOrder x := orderOf_pos_iff.mp (hx ▸ hp)
  let : Finite H := hfin.finite_zpowers.to_subtype
  let : Fintype H := Fintype.ofFinite H
  let ρH := ρ.comp H.subtype
  have hsemiH : ∀ (g : H) (a : F) (v : V), ρH g (a • v) = τ g a • ρH g v := by
    intro g
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hγ g))
    subst g
    induction n with
    | zero => intro a v; simp [ρH]
    | succ n ih =>
      intro a v
      simp only [pow_succ', map_mul, Module.End.mul_apply, AlgEquiv.mul_apply]
      rw [ih, hτγ]
      exact hsemi _ _
  have he := Descent.card_mul_finrank_invariants ρH τ hτ hsemiH
  have hcard : Nat.card H = p := (Nat.card_zpowers x).trans hx
  rw [hcard] at he
  exact he

/-- Exact binary displacement of a finite-order semilinear field actor. -/
theorem fixedCodim_formula (ρ : Representation (ZMod 2) M V)
    {p : ℕ} (hp : 0 < p) (x : M) (hx : orderOf x = p)
    (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hsemi : ∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v) :
    p * fixedCodim ρ (Subgroup.zpowers x) =
      (p - 1) * finrank (ZMod 2) F * finrank F V := by
  let : FiniteDimensional (ZMod 2) V := Module.Finite.trans F V
  have hfix := fixedSpace_formula ρ hp x hx σ hσ hsemi
  have hadd := fixedCodim_add_finrank ρ (Subgroup.zpowers x)
  have htower := Module.finrank_mul_finrank (ZMod 2) F V
  have hp1 : p - 1 + 1 = p := by omega
  nlinarith

/-- The displacement of an odd prime field actor is at least two thirds of the
binary dimension. -/
theorem two_thirds_le_fixedCodim (ρ : Representation (ZMod 2) M V)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (x : M) (hx : orderOf x = p)
    (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hsemi : ∀ (a : F) (v : V), ρ x (a • v) = σ a • ρ x v) :
    2 * finrank (ZMod 2) F * finrank F V ≤
      3 * fixedCodim ρ (Subgroup.zpowers x) := by
  have he := fixedCodim_formula ρ hp.pos x hx σ hσ hsemi
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := ho
    have := hp.two_le
    omega
  apply le_of_mul_le_mul_left (a := p) _ hp.pos
  calc
    p * (2 * finrank (ZMod 2) F * finrank F V) =
        (2 * p) * (finrank (ZMod 2) F * finrank F V) := by ac_rfl
    _ ≤ (3 * (p - 1)) * (finrank (ZMod 2) F * finrank F V) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = 3 * (p * fixedCodim ρ (Subgroup.zpowers x)) := by rw [he]; ac_rfl
    _ = p * (3 * fixedCodim ρ (Subgroup.zpowers x)) := by ac_rfl
end Representation.FiniteFieldSemilinearDisplacement
