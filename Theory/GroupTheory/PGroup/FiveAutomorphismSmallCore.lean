module
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.FixedPointFree

/-!
# A free five-action on a small two-group

Orbit counting shows that a finite group of order dividing thirty-two with
an automorphism of order dividing five and no nonidentity fixed point has
order one or sixteen. In the latter case every invariant subgroup is trivial
or full. Applying this to the Frattini subgroup makes the two-group elementary.

This supplies the intrinsic-core shape step for the local A5 section in M22,
Aschbacher--Smith A.3.12(12) and A.3.14(6), pp.47--49. The concrete Mathieu
consumer constructs the free action from involution centralizer orders.
-/

public section
open Subgroup
namespace Theory.GroupTheory

private theorem fixed_eq_bot {Q : Type*} [Group Q] (a : MulAut Q)
    (hf : MonoidHom.FixedPointFree a) : FixedPoints.subgroup (zpowers a) Q = ⊥ := by
  apply bot_unique
  intro x hx
  exact hf x (hx ⟨a, mem_zpowers a⟩)

private theorem card_one_or_sixteen {Q : Type*} [Group Q] [Finite Q]
    (hd : Nat.card Q ∣ 32) (a : MulAut Q) (ha : a ^ 5 = 1)
    (hf : MonoidHom.FixedPointFree a) : Nat.card Q = 1 ∨ Nat.card Q = 16 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := zpowers a
  have hp : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [A, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one ha)
  have hm := hp.card_modEq_card_fixedPoints Q
  change Nat.card Q % 5 = Nat.card (FixedPoints.subgroup A Q) % 5 at hm
  rw [fixed_eq_bot a hf, card_bot] at hm
  have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show (32 : ℕ).divisors = {1,2,4,8,16,32} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

/-- A free action of order dividing five forces a two-group of order dividing
thirty-two to be trivial or elementary of order sixteen. -/
theorem elementary_sixteen_of_free_five_small_core
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (hd : Nat.card Q ∣ 32) (a : MulAut Q) (ha : a ^ 5 = 1)
    (hf : MonoidHom.FixedPointFree a) :
    Nat.card Q = 1 ∨ (IsElementaryAbelian 2 Q ∧ Nat.card Q = 16) := by
  rcases card_one_or_sixteen hd a ha hf with h1 | h16
  · exact Or.inl h1
  right
  refine ⟨?_, h16⟩
  let : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let A := zpowers a
  have hA : Nat.card A = 5 := by
    rw [Nat.card_zpowers]
    apply (Nat.dvd_prime (by decide : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one ha) |>.resolve_left
    intro ho
    have hone : a = 1 := orderOf_eq_one_iff.mp ho
    have hall : ∀ x : Q, x = 1 := fun x => hf x (by rw [hone]; rfl)
    let : Subsingleton Q := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hc : Nat.card Q = 1 := Nat.card_unique
    omega
  let : IsInvariant A Q (frattini Q) := isInvariant_of_characteristic _
  have hphi : frattini Q = ⊥ := by
    rcases invariant_eq_bot_or_top_of_five_actor hA h16 (fixed_eq_bot a hf) (frattini Q) with hb | ht
    · exact hb
    · have hb : (⊥ : Subgroup Q) = ⊤ := frattini_nongenerating (by simp [ht])
      have hc : Nat.card Q = 1 := by
        have hh := congrArg (fun H : Subgroup Q => Nat.card H) hb
        simpa only [card_bot, card_top] using hh.symm
      omega
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi

end Theory.GroupTheory
