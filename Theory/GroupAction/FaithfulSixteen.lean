module

public import Theory.GroupAction.OrderFifteenOnSixteen
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Faithful actions on a group of order sixteen

A faithful action by a group whose order is divisible by five has no proper
nontrivial invariant subgroup. A faithful cyclic group of order fifteen acts
regularly on the nonidentity elements. These statements retain the supplied
action, without assuming an elementary abelian group or a chosen basis.

Cauchy's theorem supplies an order-five actor. Faithfulness and orbit counting
make its fixed subgroup trivial, and the existing order-five invariant-subgroup
lemma applies. For regularity, a generator induces an order-fifteen automorphism;
its powers are transitive, and an automorphism commuting with its order-five
subgroup cannot fix a nonidentity point unless it is trivial.

Application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.989 (the action on the order-sixteen quotient Q/F).
The underlying order-fifteen action result is proved in `OrderFifteenOnSixteen`.
-/

open scoped IsMulCommutative

namespace Theory.GroupAction

/-- A faithful cyclic group of order fifteen acts regularly on the nonidentity
elements of a group of order sixteen. -/
public theorem faithful_cyclic_fifteen_regular
    {A V : Type*} [Group A] [Finite A] [IsCyclic A] [Group V] [Finite V]
    (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 15) (hV : Nat.card V = 16)
    (x y : V) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃! a : A, ρ a x = y := by
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic A)
  have hoa : orderOf (ρ a) = 15 :=
    (orderOf_injective ρ hρ a).trans ((orderOf_eq_card_of_zpowers_eq_top ha).trans hA)
  have hfive : orderOf ((ρ a) ^ (3 : ℕ)) = 5 := by
    rw [orderOf_pow, hoa]
    decide
  have hfree (b : A) (hb : ρ b x = x) : b = 1 := by
    apply hρ
    rw [map_one]
    apply MulAut.eq_one_of_commute_five_of_fixed hV ((ρ a) ^ (3 : ℕ))
      (ρ b) hfive ?_ x hx hb
    exact ((show Commute a b from mul_comm a b).map ρ).pow_left 3
  obtain ⟨n, hn⟩ := MulAut.exists_zpow_apply_eq_of_order_fifteen hV (ρ a) hoa x y hx hy
  refine ⟨a ^ n, by simpa only [map_zpow] using hn, ?_⟩
  intro b hb
  have heq : ρ (a ^ n) x = ρ b x := by simpa only [map_zpow, hb] using hn
  have hprod : (a ^ n)⁻¹ * b = 1 := hfree _ (by
    rw [map_mul, map_inv]
    change (ρ (a ^ n)).symm (ρ b x) = x
    rw [← heq]
    exact (ρ (a ^ n)).symm_apply_apply x)
  exact (inv_mul_eq_one.mp hprod).symm

/-- A faithful automorphism group with order divisible by five has no proper
nontrivial invariant subgroup on a group of order sixteen. -/
public theorem invariant_eq_bot_or_top_of_faithful_five
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V] [FaithfulSMul A V]
    (hA : 5 ∣ Nat.card A) (hV : Nat.card V = 16)
    (D : Subgroup V) [IsInvariant A V D] : D = ⊥ ∨ D = ⊤ := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 hA
  let B := Subgroup.zpowers a
  have hB : Nat.card B = 5 := (Nat.card_zpowers a).trans ha
  have hnot : FixedPoints.subgroup B V ≠ ⊤ := by
    intro htop
    have he : a = 1 := by
      apply eq_of_smul_eq_smul (α := V)
      intro v
      have hv : v ∈ FixedPoints.subgroup B V := htop ▸ Subgroup.mem_top v
      simpa only [Subgroup.smul_def, one_smul] using hv ⟨a, Subgroup.mem_zpowers a⟩
    simp [he] at ha
  let _ : IsInvariant B V D := ⟨fun b v =>
    IsInvariant.invariant (A := A) (G := V) (H := D) (b : A) v⟩
  exact invariant_eq_bot_or_top_of_five_actor hB hV
    (fixed_eq_bot_of_five_action_card_sixteen hB hV hnot) D

/-- It is enough that the image of an action has order divisible by five.
The whole actor need not act faithfully. -/
public theorem invariant_eq_bot_or_top_of_image_five
    {A V : Type*} [Group A] [Group V] [Finite V]
    (ρ : A →* MulAut V) (hA : 5 ∣ Nat.card ρ.range) (hV : Nat.card V = 16)
    (D : Subgroup V) (hD : ∀ a : A, ∀ v : V, v ∈ D ↔ ρ a v ∈ D) :
    D = ⊥ ∨ D = ⊤ := by
  let _ : IsInvariant ρ.range V D := ⟨by
    intro b v
    obtain ⟨a, ha⟩ := b.property
    change v ∈ D ↔ (b : MulAut V) v ∈ D
    rw [← ha]
    exact hD a v⟩
  exact invariant_eq_bot_or_top_of_faithful_five hA hV D

/-- In the regular action, an actor fixing a nonidentity element is trivial. -/
public theorem eq_one_of_faithful_cyclic_fifteen_fixed
    {A V : Type*} [Group A] [Finite A] [IsCyclic A] [Group V] [Finite V]
    (ρ : A →* MulAut V) (hρ : Function.Injective ρ)
    (hA : Nat.card A = 15) (hV : Nat.card V = 16)
    (a : A) (x : V) (hx : x ≠ 1) (ha : ρ a x = x) : a = 1 := by
  exact (faithful_cyclic_fifteen_regular ρ hρ hA hV x x hx hx).unique ha (by simp)

end Theory.GroupAction
