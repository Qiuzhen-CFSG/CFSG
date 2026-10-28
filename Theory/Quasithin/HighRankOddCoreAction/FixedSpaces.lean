module
public import Theory.Quasithin.HighRankOddCoreAction
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Fixed-space ranks of actual subgroup actions

The fixed subgroup of a characteristic restriction of conjugation embeds
in the original ambient involution centralizer. For an action on an
elementary abelian p-group, the literal fixed subgroup is the one-eigenspace
of its associated ZMod p representation. Cardinality therefore transports
the original group bound to the precise linear fixed-space dimension.

Source: the Frattini fixed-space step in Aschbacher–Smith, A.1.28, p.26.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.Quasithin

public theorem finrank_eigenspace_one_le_of_fixed_card
    {A V : Type*} [Group A] [Group V] [Finite V]
    {p n : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (f : A →* MulAut V) (a : A) (hc : Nat.card (f a).fixedSubgroup ≤ p ^ n) :
    let _ := MulDistribMulAction.compHom V f
    let ρ : Representation (ZMod p) A (Additive V) := Representation.ofElementaryAbelianAction
    Module.finrank (ZMod p) (Module.End.eigenspace (ρ a) 1) ≤ n := by
  let _ := MulDistribMulAction.compHom V f
  let ρ := Representation.ofElementaryAbelianAction (p := p) (A := A) (G := V)
  let e : (f a).fixedSubgroup ≃ (Module.End.eigenspace (ρ a) (1 : ZMod p)) := {
    toFun := fun v => ⟨Additive.ofMul v.val, by
      rw [Module.End.mem_eigenspace_iff, one_smul]
      change Additive.ofMul (f a v.val) = Additive.ofMul v.val
      exact congrArg (Additive.ofMul : V → Additive V) ((MulAut.mem_fixedSubgroup (f a) v.val).mp v.property)⟩
    invFun := fun v => ⟨Additive.toMul v.val, by
      have hv := Module.End.mem_eigenspace_iff.mp v.property
      rw [one_smul] at hv
      exact (MulAut.mem_fixedSubgroup (f a) (Additive.toMul v.val)).mpr (congrArg (Additive.toMul : Additive V → V) hv)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : p ^ Module.finrank (ZMod p) (Module.End.eigenspace (ρ a) (1 : ZMod p)) ≤ p ^ n := by
    calc
      _ = Nat.card (Module.End.eigenspace (ρ a) (1 : ZMod p)) := by
        simpa only [Nat.card_zmod] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := (Module.End.eigenspace (ρ a) (1 : ZMod p)))).symm
      _ = Nat.card (f a).fixedSubgroup := (Nat.card_congr e).symm
      _ ≤ _ := hc
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard

/-- The fixed subgroup of a characteristic restriction embeds in the actual
ambient centralizer of the conjugating element. -/
public theorem primeRank_fixed_characteristic_conjugation_le
    {G : Type*} [Group G] [Finite G] (p : ℕ)
    (Q : Subgroup G) [Q.Normal] (X : Subgroup Q) [X.Characteristic] (a : G) :
    primeRank p (MulAut.characteristic X (MulAut.conjNormal a)).fixedSubgroup ≤
      primeRank p (centralizer ({a} : Set G)) := by
  let α : MulAut X := MulAut.characteristic X (MulAut.conjNormal a)
  let f : α.fixedSubgroup →* centralizer ({a} : Set G) :=
    (Q.subtype.comp X.subtype).restrict (fun x hx => by
      apply mem_centralizer_singleton_iff.mpr
      change ((x : Q) : G) * a = a * ((x : Q) : G)
      have hh := congrArg (fun z : X => ((z : Q) : G)) ((MulAut.mem_fixedSubgroup _ _).mp hx)
      change a * ((x : Q) : G) * a⁻¹ = ((x : Q) : G) at hh
      have hh' := congrArg (fun z : G => z * a) hh
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh'.symm)
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.ext
      (congrArg (fun z : centralizer ({a} : Set G) => (z : G)) h)))
  exact Theory.GroupTheory.primeRank_le_of_injective p f hf
end Theory.Quasithin
