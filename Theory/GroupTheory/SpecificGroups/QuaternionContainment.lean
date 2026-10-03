module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Tactic.Group

/-!
# Quaternion containment detected by outside elements of order four

Let U be an abelian subgroup of a group G such that every element outside U
has central square. If K contains every outside element of order four, it
contains every subgroup isomorphic to QuaternionGroup m for m ≥ 2.

Write a,b for the standard quaternion generators. The elements b and ab have
order four, a² is nontrivial, and a*b*a=b. If a lies in U, noncommutativity
forces b and ab outside U. Otherwise the central square of a and the inversion
relation force a⁴=1, so a itself has order four; either b or ab lies outside U.
In both cases the two generators lie in K, and the explicit model normal forms
establish containment.

This elementary reduction is used in ABG Chapter II §1 Lemma 2(v), article p.9,
to prove uniqueness of the largest quaternion subgroup in a wreathed group.
It requires neither finiteness of G nor an index condition on U.
-/

namespace QuaternionGroup
variable {G : Type*} [Group G]

private theorem inverted_four (a b : G) (hrel : a * b * a = b)
    (hc : Commute (a ^ 2) b) : a ^ 4 = 1 := by
  have hh : a ^ 2 * b * a ^ 2 = b := by
    calc
      _ = a * (a * b * a) * a := by simp only [pow_two, mul_assoc]
      _ = b := by rw [hrel, hrel]
  have he : b * a ^ 4 = b := by
    calc
      _ = (a ^ 2 * b) * a ^ 2 := by rw [hc.eq]; group
      _ = b := hh
  exact mul_left_cancel (he.trans (mul_one b).symm)

private theorem pair_mem (U K : Subgroup G)
    (hU : ∀ a ∈ U, ∀ b ∈ U, Commute a b)
    (hcentral : ∀ a ∉ U, ∀ b : G, Commute (a ^ 2) b)
    (hK : ∀ a ∉ U, orderOf a = 4 → a ∈ K)
    (a b : G) (ha2 : a ^ 2 ≠ 1) (hb : orderOf b = 4)
    (hab : orderOf (a*b) = 4) (hrel : a*b*a=b) : a ∈ K ∧ b ∈ K := by
  have hnc : ¬ Commute a b := by
    intro hc
    apply ha2
    have hh : b * a ^ 2 = b := by
      calc
        _ = a*b*a := by rw [hc.eq]; simp only [pow_two, mul_assoc]
        _ = b := hrel
    exact mul_left_cancel (hh.trans (mul_one b).symm)
  by_cases ha : a ∈ U
  · have hbu : b ∉ U := fun hb => hnc (hU a ha b hb)
    have habu : a*b ∉ U := by
      intro hh
      exact hbu ((U.mul_mem_cancel_left ha).mp hh)
    have hbK := hK b hbu hb
    have habK := hK (a*b) habu hab
    exact ⟨(K.mul_mem_cancel_right hbK).mp habK, hbK⟩
  · have ha4 : orderOf a = 4 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      change orderOf a = 2 ^ (1 + 1)
      apply orderOf_eq_prime_pow
      · simpa using ha2
      · exact inverted_four a b hrel (hcentral a ha b)
    have haK := hK a ha ha4
    refine ⟨haK, ?_⟩
    by_cases hbu : b ∈ U
    · have habu : a*b ∉ U := by
        intro hh
        exact ha ((U.mul_mem_cancel_right hbu).mp hh)
      exact (K.mul_mem_cancel_left haK).mp (hK (a*b) habu hab)
    · exact hK b hbu hb

/-- Quaternion subgroups lie in any subgroup containing all order-four elements
outside an abelian subgroup whose outside elements have central square. -/
public theorem subgroup_le_of_outer_order_four (U K Q : Subgroup G)
    (hU : ∀ a ∈ U, ∀ b ∈ U, Commute a b)
    (hcentral : ∀ a ∉ U, ∀ b : G, Commute (a ^ 2) b)
    (hK : ∀ a ∉ U, orderOf a = 4 → a ∈ K)
    {m : ℕ} (hm : 2 ≤ m) (e : Q ≃* QuaternionGroup m) : Q ≤ K := by
  let : NeZero m := ⟨by omega⟩
  let f : QuaternionGroup m →* G := Q.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Q.subtype_injective.comp e.symm.injective
  let a := f (QuaternionGroup.a 1)
  let b := f (QuaternionGroup.xa 0)
  have ha2 : a ^ 2 ≠ 1 := by
    intro he
    have hd : 2 * m ∣ 2 := by
      have hh := orderOf_dvd_of_pow_eq_one he
      rw [orderOf_injective f hf, QuaternionGroup.orderOf_a_one] at hh
      exact hh
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hb : orderOf b = 4 := by
    dsimp [b]
    rw [orderOf_injective f hf, QuaternionGroup.orderOf_xa]
  have hab : orderOf (a*b) = 4 := by
    dsimp [a,b]
    rw [← map_mul, orderOf_injective f hf, QuaternionGroup.a_mul_xa, QuaternionGroup.orderOf_xa]
  have hrel : a*b*a=b := by
    dsimp [a,b]
    simp only [← map_mul, QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a,
      sub_add_cancel]
  obtain ⟨haK,hbK⟩ := pair_mem U K hU hcentral hK a b ha2 hb hab hrel
  intro q hq
  let qq : Q := ⟨q,hq⟩
  have hqf : f (e qq) = q := by simp [f,qq]
  rw [← hqf]
  cases e qq with
  | a i =>
    have hi : (QuaternionGroup.a i : QuaternionGroup m) = QuaternionGroup.a 1 ^ i.val := by simp
    rw [hi,map_pow]
    exact K.pow_mem haK _
  | xa i =>
    have hi : (QuaternionGroup.xa i : QuaternionGroup m) = QuaternionGroup.xa 0 * QuaternionGroup.a 1 ^ i.val := by simp
    rw [hi,map_mul,map_pow]
    exact K.mul_mem hbK (K.pow_mem haK _)
end QuaternionGroup
