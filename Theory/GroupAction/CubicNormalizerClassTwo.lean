module
public import Theory.GroupAction.FixedFreeThreeClassTwo
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
/-!
# Cubic normalizer actions and central commutators

A cubic subgroup normalizing a finite group and fixing only its identity
acts through a fixed-point-free cubic automorphism. Neumann's theorem
therefore makes every commutator central. The statement retains the
original subgroup inclusion and actual normalizer action.
Source: B. H. Neumann's fixed-point-free order-three theorem; application
in Aschbacher--Smith 10.2.3(4), printed p.747.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem cubic_fixedFree_commutator_le_center (a : MulAut G)
    (ha : a^3=1) (hf : MonoidHom.FixedPointFree a) : _root_.commutator G ≤ center G := by
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (orderOf_dvd_of_pow_eq_one ha) with h | h
  · have ha1 : a=1 := orderOf_eq_one_iff.mp h
    have hi (x : G) : x=1 := hf x (by simp [ha1])
    intro x hx
    rw [hi x]
    exact one_mem _
  · exact a.commutator_le_center_of_orderOf_eq_three_of_fixedPointFree h hf

theorem commutator_le_center_of_cubic_normalizer (P D : Subgroup G)
    (hD : Nat.card D = 3) (hn : D ≤ normalizer (P : Set G))
    (hf : P ⊓ centralizer (D : Set G) = ⊥) : _root_.commutator P ≤ center P := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hd : D ≠ ⊥ := by intro h; simp [h] at hD
  obtain ⟨d,hd,hd1⟩ := D.bot_or_exists_ne_one.resolve_left hd
  let d' : D := ⟨d,hd⟩
  have hd' : d' ≠ 1 := fun h => hd1 (congrArg D.subtype h)
  let a : MulAut P := P.normalizerMonoidHom ⟨d,hn hd⟩
  apply cubic_fixedFree_commutator_le_center a
  · have hdn : (⟨d,hn hd⟩ : normalizer (P : Set G))^3=1 := by
      apply Subtype.ext
      exact congrArg D.subtype (hD ▸ pow_card_eq_one' (x := d'))
    change (P.normalizerMonoidHom ⟨d,hn hd⟩)^3=1
    rw [←map_pow,hdn,map_one]
  · intro x hx
    have hdx : d*(x:G)*d⁻¹=(x:G) := congrArg P.subtype hx
    have hcomm : Commute d (x:G) := mul_inv_eq_iff_eq_mul.mp hdx
    have hc : (x:G) ∈ centralizer (D : Set G) := by
      intro y hy
      obtain ⟨k,hk⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card hD (g' := (⟨y,hy⟩ : D)) hd')
      have hy' : d^k=y := congrArg D.subtype hk
      rw [←hy']
      exact (hcomm.zpow_left k).eq
    have hx1 : (x:G)=1 := mem_bot.mp (hf ▸ (show (x:G) ∈ P ⊓ centralizer (D : Set G) from ⟨x.property,hc⟩))
    exact Subtype.ext hx1
end Subgroup
