module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.IntervalCases

/-!
# Involutions in stabilizers of actions on six points

Every stabilizer for an action of a group of order eight on six points
has even order, by orbit-stabilizer. The same holds for a faithful action
of a group of order ten: an odd stabilizer would have order five and index
two. Its order-five generator has a unique fixed point. Normality of the
stabilizer would force the whole group to fix that point, a contradiction.
Cauchy's theorem supplies an involution fixing each prescribed point.

These structural arguments apply to the Sylow two and dihedral subgroups
in the degree-six A₆ action used by Aschbacher, *Sporadic Groups* (1994),
47.6(4), printed p.264. They do not enumerate permutations or presume a
specific labeling of the six cosets.
-/

public section

open Subgroup MulAction
namespace SixPointInvolutionStabilizers
variable {H Ω : Type*} [Group H] [Finite H] [Finite Ω] [MulAction H Ω]

omit [Finite H] [Finite Ω] in
private theorem orbit_stabilizer_card (v : Ω) :
    Nat.card (orbit H v) * Nat.card (stabilizer H v) = Nat.card H := by
  rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup H v)]

omit [Finite H] in
theorem even_stabilizer_of_card_eight (hH : Nat.card H = 8)
    (hΩ : Nat.card Ω = 6) (v : Ω) : 2 ∣ Nat.card (stabilizer H v) := by
  have hc := orbit_stabilizer_card (H := H) v
  rw [hH] at hc
  have hb := Nat.card_le_card_of_injective (Subtype.val : orbit H v → Ω) Subtype.val_injective
  rw [hΩ] at hb
  generalize Nat.card (orbit H v) = n at hc hb
  interval_cases n <;> omega

omit [Finite Ω] in
private theorem fixed_eq_of_order_five [Fintype Ω] [DecidableEq Ω]
    (hΩ : Nat.card Ω = 6) (f : Equiv.Perm Ω) (hf : orderOf f = 5)
    {a b : Ω} (ha : f a = a) (hb : f b = b) : a = b := by
  have hc : f.IsCycle := Equiv.Perm.isCycle_of_prime_order (by rw [hf]; decide) (by
    have hle := f.support.card_le_univ
    rw [← Nat.card_eq_fintype_card, hΩ] at hle
    omega)
  have hs : f.support.card = 5 := hc.orderOf.symm.trans hf
  have hcomp : f.supportᶜ.card ≤ 1 := by
    rw [Finset.card_compl, ← Nat.card_eq_fintype_card, hΩ, hs]
  exact Finset.card_le_one.mp hcomp a (by simpa using ha) b (by simpa using hb)

theorem even_stabilizer_of_card_ten [FaithfulSMul H Ω]
    (hH : Nat.card H = 10) (hΩ : Nat.card Ω = 6) (v : Ω) :
    2 ∣ Nat.card (stabilizer H v) := by
  classical
  let : Fintype Ω := Fintype.ofFinite Ω
  by_contra hodd
  have hc := orbit_stabilizer_card (H := H) v
  rw [hH] at hc
  have hb := Nat.card_le_card_of_injective (Subtype.val : orbit H v → Ω) Subtype.val_injective
  rw [hΩ] at hb
  have hs : Nat.card (stabilizer H v) = 5 := by
    generalize Nat.card (orbit H v) = n at hc hb
    interval_cases n <;> omega
  have hi : (stabilizer H v).index = 2 := by
    have he := (stabilizer H v).index_mul_card
    rw [hs, hH] at he
    omega
  let : (stabilizer H v).Normal := normal_of_index_eq_two hi
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer H v) 5 (by rw [hs])
  let f := MulAction.toPermHom H Ω
  have ht5 : orderOf (f (t : H)) = 5 := by
    rw [orderOf_injective f MulAction.toPerm_injective, orderOf_submonoid, ht]
  have htv : f (t : H) v = v := t.property
  have hfix (g : H) : g • v = v := by
    have hh : g⁻¹ * (t : H) * g ∈ stabilizer H v := by
      simpa only [inv_inv] using
        (inferInstance : (stabilizer H v).Normal).conj_mem (t : H) t.property g⁻¹
    have htg : f (t : H) (g • v) = g • v := by
      change (t : H) • (g • v) = g • v
      calc
        _ = g • ((g⁻¹ * (t : H) * g) • v) := by simp [mul_smul]
        _ = _ := congrArg (g • ·) (mem_stabilizer_iff.mp hh)
    exact fixed_eq_of_order_five hΩ _ ht5 htg htv
  have htop : stabilizer H v = ⊤ := eq_top_iff.mpr (fun g _ => hfix g)
  rw [htop, card_top, hH] at hs
  omega

theorem exists_involution_fixed_of_card_eight (hH : Nat.card H = 8)
    (hΩ : Nat.card Ω = 6) (v : Ω) :
    ∃ t : H, orderOf t = 2 ∧ t • v = v := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
    (even_stabilizer_of_card_eight hH hΩ v)
  exact ⟨t, (Subgroup.orderOf_coe t).trans ht, t.property⟩

theorem exists_involution_fixed_of_card_ten [FaithfulSMul H Ω]
    (hH : Nat.card H = 10) (hΩ : Nat.card Ω = 6) (v : Ω) :
    ∃ t : H, orderOf t = 2 ∧ t • v = v := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
    (even_stabilizer_of_card_ten hH hΩ v)
  exact ⟨t, (Subgroup.orderOf_coe t).trans ht, t.property⟩
end SixPointInvolutionStabilizers
