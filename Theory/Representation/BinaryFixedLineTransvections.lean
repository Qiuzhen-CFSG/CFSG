module
public import Theory.Representation.BinaryOffender.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.LinearAlgebra.DisplacementFiltration
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness

/-!
# Faithful centered transvections from a fixed line

For a commutative binary actor, an element fixing the marked space has
hyperplane displacement in the common fixed line. Its total displacement
therefore has dimension at most two. Excluding these elements makes the
marked action faithful. A faithful full centered-transvection action then
identifies the actor with the functionals vanishing on its center, giving
its exact rank.

The original same-flag application is in Chapter12.Section09.NaturalSource.
Components.NonabelianFixedLine. These are linear consequences of the geometry
in Aschbacher--Smith G.10.1 and G.11.1(3i), printed pp.357,364.
-/

public noncomputable section
open Subgroup Module Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryFixedLine
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (X : Subgroup G)
  (v : V) (hv : v ≠ 0) (W : Submodule (ZMod 2) V)

include hv

/-- An actor fixing W has rank at most two when all hyperplane displacements
lie in W and the common fixed space is the marked line. -/
theorem rank_le_two_of_fixes_marked [IsMulCommutative X]
    (A : Submodule (ZMod 2) V) (hA : finrank (ZMod 2) (V ⧸ A) ≤ 1)
    (hdisp : ∀ x : X, ∀ u ∈ A, ρ x u - u ∈ W)
    (hfixed : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (a : X) (ha : ∀ w ∈ W, ρ a w = w) :
    finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 2 := by
  have hm : A.map (ρ a - LinearMap.id) ≤ Submodule.span (ZMod 2) {v} := by
    rw [← hfixed]
    rintro _ ⟨u,hu,rfl⟩ x
    change ρ x (ρ a u - u) = ρ a u - u
    have hc : ρ x (ρ a u) = ρ a (ρ x u) := by
      rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul]
      exact congrArg (fun g : G => ρ g u) (congrArg Subtype.val (mul_comm x a))
    have he := ha (ρ x u - u) (hdisp x u hu)
    rw [map_sub] at he ⊢
    rw [hc]
    exact sub_eq_sub_iff_add_eq_add.mpr (by
      have he' := sub_eq_sub_iff_add_eq_add.mp he
      simpa only [add_comm] using he')
  have hh := Submodule.finrank_mono hm
  rw [finrank_span_singleton hv] at hh
  have hb := LinearMap.finrank_range_le_quotient_add_map (ρ a - LinearMap.id) A
  omega

/-- A faithful full centered-transvection action identifies its actor with
all functionals vanishing on the marked point, giving the exact binary rank. -/
theorem actor_rank_of_faithful_full_transvections [Finite X] [IsElementaryAbelian 2 X]
    (hvW : v ∈ W)
    (htrans : ∀ x : X, ∃ f : Module.Dual (ZMod 2) W,
      f ⟨v,hvW⟩ = 0 ∧ ∀ w : W, ρ x w = (w : V) + f w • v)
    (hfull : ∀ f : Module.Dual (ZMod 2) W, f ⟨v,hvW⟩ = 0 →
      ∃ x : X, ∀ w : W, ρ x w = (w : V) + f w • v)
    (hfaith : ∀ x y : X, (∀ w : W, ρ x w = ρ y w) → x = y) :
    finrank (ZMod 2) (Additive X) + 1 = finrank (ZMod 2) W := by
  classical
  let p : W := ⟨v,hvW⟩
  let A := (Submodule.span (ZMod 2) {p}).dualAnnihilator
  let f : X → A := fun x => ⟨(htrans x).choose,by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro w hw
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul,show (htrans x).choose p = 0 from (htrans x).choose_spec.1,smul_zero]⟩
  have hf (x : X) (w : W) : ρ x w = (w : V) + (f x : Module.Dual (ZMod 2) W) w • v :=
    (htrans x).choose_spec.2 w
  have hinj : Function.Injective f := by
    intro x y he
    apply hfaith x y
    intro w
    rw [hf,hf,he]
  have hsurj : Function.Surjective f := by
    intro φ
    have hp : (φ : Module.Dual (ZMod 2) W) p = 0 :=
      (Submodule.mem_dualAnnihilator _).mp φ.property p (Submodule.mem_span_singleton_self _)
    obtain ⟨x,hx⟩ := hfull φ hp
    refine ⟨x,Subtype.ext (LinearMap.ext fun w => ?_)⟩
    have he := (hf x w).symm.trans (hx w)
    exact (smul_left_injective (ZMod 2) hv) (add_left_cancel he)
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hinj,hsurj⟩)
  rw [Nat.card_congr Additive.ofMul] at hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A),Nat.card_zmod] at hc
  have hr : finrank (ZMod 2) (Additive X) = finrank (ZMod 2) A :=
    (Nat.pow_right_injective (by decide : 1 < 2)) hc
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span (ZMod 2) {p})
  rw [finrank_span_singleton (show p ≠ 0 from fun he => hv (congrArg Subtype.val he))] at hd
  change 1 + finrank (ZMod 2) A = finrank (ZMod 2) W at hd
  omega
end Representation.BinaryFixedLine
