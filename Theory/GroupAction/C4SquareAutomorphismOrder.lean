module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Orders of automorphism groups of C₄ × C₄

Every automorphism subgroup of a C₄-square has order dividing 96. An ordered
pair is a basis exactly when its two squares are distinct nonidentity elements.
The 96 such pairs form a free set for every automorphism subgroup, so the
orbit decomposition gives the divisibility. The basis count and the sixteen
coordinate normal forms are checked finite computations.

This is the finite-action reduction for the extension problem in
Janko–Thompson, Math. Z. 113 (1970), 1.4(c), printed p.386. It makes no
assumption about an order-three automorphism or any ambient simple group.
-/

namespace C4SquareExtension
/-- The coordinate model of a homocyclic group of order sixteen. -/
public abbrev Model := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)
private def Good (x : Model × Model) : Prop :=
  x.1 ^ 2 ≠ 1 ∧ x.2 ^ 2 ≠ 1 ∧ x.1 ^ 2 ≠ x.2 ^ 2
private instance (x : Model × Model) : Decidable (Good x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private theorem good_card : Nat.card {x : Model × Model // Good x} = 96 := by
  rw [Nat.card_eq_fintype_card]
  decide
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem good_generate : ∀ a b : Model, Good (a,b) → ∀ x : Model,
    ∃ i j : Fin 4, x = a ^ i.val * b ^ j.val := by decide

/-- Every group of automorphisms of the coordinate model has order dividing 96. -/
public theorem model_aut_subgroup_card_dvd (C : Subgroup (MulAut Model)) :
    Nat.card C ∣ 96 := by
  let X : SubMulAction C (Model × Model) := {
    carrier := {x | Good x}
    smul_mem' := by
      intro c x hx
      change Good ((c : MulAut Model) x.1, (c : MulAut Model) x.2)
      refine ⟨?_, ?_, ?_⟩
      · intro h
        apply hx.1
        apply (c : MulAut Model).injective
        rw [map_pow, map_one]
        exact h
      · intro h
        apply hx.2.1
        apply (c : MulAut Model).injective
        rw [map_pow, map_one]
        exact h
      · intro h
        apply hx.2.2
        apply (c : MulAut Model).injective
        rw [map_pow, map_pow]
        exact h }
  have hstab (v : X) : MulAction.stabilizer C v = ⊥ := by
    apply bot_unique
    intro c hc
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hh := congrArg Subtype.val hc
    have h1 : (c : MulAut Model) v.val.1 = v.val.1 := congrArg Prod.fst hh
    have h2 : (c : MulAut Model) v.val.2 = v.val.2 := congrArg Prod.snd hh
    obtain ⟨i,j,hx⟩ := good_generate v.val.1 v.val.2 v.property x
    change (c : MulAut Model) x = x
    rw [hx, map_mul, map_pow, map_pow, h1, h2]
  have hequiv := MulAction.selfEquivOrbitsQuotientProd (G := C) (X := X) hstab
  have hc : Nat.card X = 96 := good_card
  rw [← hc, Nat.card_congr hequiv, Nat.card_prod]
  exact dvd_mul_left _ _

/-- Every automorphism subgroup of a C₄-square has order dividing 96. -/
public theorem aut_subgroup_card_dvd {A : Type*} [Group A]
    (model : Nonempty (A ≃* Model)) (C : Subgroup (MulAut A)) :
    Nat.card C ∣ 96 := by
  obtain ⟨e⟩ := model
  have hh := model_aut_subgroup_card_dvd (C.map (MulAut.congr e).toMonoidHom)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hh

end C4SquareExtension
