module

public import Theory.GroupTheory.PRegularLift
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Normalized sums over odd-order elements

Odd normal quotients preserve normalized sums of inflated functions: oddness
is constant on each quotient fiber, whose size cancels against the group order.
For a central two-subgroup, every odd quotient element has exactly one odd
lift. The corresponding normalized sum is divided by the kernel order.
Group isomorphisms preserve these sums, and a two-group contributes only its
identity. These counting facts are independent of character theory.

Source: the quotient calculations underlying Fong, *Some Sylow subgroups of
order 32*, J. Algebra 6 (1967), printed pp. 71, 73–74.
-/

public section

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace OddElementSum
variable {G : Type*} [Group G] [Finite G]

/-- The group-order-normalized sum restricted to odd-order elements. -/
@[expose] def normalized (f : G → ℝ) : ℝ :=
  (Nat.card G : ℝ)⁻¹ * ∑ g : G, if Odd (orderOf g) then f g else 0

omit [Finite G] in
theorem odd_quotient_iff (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N)) (g : G) :
    Odd (orderOf (QuotientGroup.mk' N g)) ↔ Odd (orderOf g) := by
  refine ⟨fun h => ?_, fun h => h.of_dvd_nat (orderOf_map_dvd _ _)⟩
  have hmem : g ^ orderOf (QuotientGroup.mk' N g) ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (g ^ orderOf (QuotientGroup.mk' N g)) = 1
    rw [map_pow, pow_orderOf_eq_one]
  apply (h.mul hN).of_dvd_nat
  apply orderOf_dvd_iff_pow_eq_one.mpr
  rw [pow_mul]
  exact orderOf_dvd_iff_pow_eq_one.mp (N.orderOf_dvd_natCard hmem)

theorem normalized_odd_quotient (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (f : (G ⧸ N) → ℝ) :
    normalized (fun g => f (QuotientGroup.mk' N g)) = normalized f := by
  classical
  have hsum : (∑ g : G, if Odd (orderOf g) then f (QuotientGroup.mk' N g) else 0) =
      (Nat.card N : ℝ) * ∑ q : G ⧸ N, if Odd (orderOf q) then f q else 0 := by
    simp_rw [← odd_quotient_iff N hN]
    rw [← Fintype.sum_fiberwise' (QuotientGroup.mk' N)
      (fun q => if Odd (orderOf q) then f q else 0), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    have hc : Fintype.card {g : G // QuotientGroup.mk' N g = q} = Nat.card N := by
      rw [← Nat.card_eq_fintype_card]
      convert Nat.card_congr
        (MonoidHom.fiberEquivKerOfSurjective (QuotientGroup.mk'_surjective N) q) using 1
      · exact Nat.card_congr (Equiv.refl _)
      · rw [QuotientGroup.ker_mk']
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
  unfold normalized
  rw [hsum, N.card_eq_card_quotient_mul_card_subgroup, Nat.cast_mul, mul_inv_rev]
  have hn : (Nat.card N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp
  congr 5
  exact Subsingleton.elim _ _

omit [Finite G] in
theorem odd_central_quotient_injective (Z : Subgroup G) [Z.Normal]
    (hc : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    {a b : G} (ha : Odd (orderOf a)) (hb : Odd (orderOf b))
    (he : QuotientGroup.mk' Z a = QuotientGroup.mk' Z b) : a = b := by
  have hz : a * b⁻¹ ∈ Z := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' Z (a * b⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hab : Commute a b⁻¹ := by
    apply mul_right_cancel (b := b⁻¹)
    simpa only [mul_assoc] using (Subgroup.mem_center_iff.mp (hc hz) b⁻¹).symm
  have ho : Odd (orderOf (a * b⁻¹)) :=
    (ha.mul (by simpa using hb)).of_dvd_nat hab.orderOf_mul_dvd_mul_orderOf
  have hone : (⟨a * b⁻¹, hz⟩ : Z) = 1 := by
    by_contra hn
    have hd := hZ.dvd_orderOf hn
    have ho' : Odd (orderOf (⟨a * b⁻¹, hz⟩ : Z)) := by simpa using ho
    exact (Nat.not_even_iff_odd.mpr ho') (even_iff_two_dvd.mpr hd)
  exact mul_inv_eq_one.mp (congrArg Subtype.val hone)

theorem normalized_central_two_quotient (Z : Subgroup G) [Z.Normal]
    (hc : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    (f : (G ⧸ Z) → ℝ) :
    normalized (fun g => f (QuotientGroup.mk' Z g)) =
      (Nat.card Z : ℝ)⁻¹ * normalized f := by
  classical
  have hsum : (∑ g : G, if Odd (orderOf g) then f (QuotientGroup.mk' Z g) else 0) =
      ∑ q : G ⧸ Z, if Odd (orderOf q) then f q else 0 := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    apply Finset.sum_bij (fun g _ => QuotientGroup.mk' Z g)
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hg.of_dvd_nat (orderOf_map_dvd _ _)
    · intro a ha b hb he
      exact odd_central_quotient_injective Z hc hZ (Finset.mem_filter.mp ha).2
        (Finset.mem_filter.mp hb).2 he
    · intro q hq
      have hodd := (Finset.mem_filter.mp hq).2
      obtain ⟨g, hg, he⟩ := (QuotientGroup.mk' Z).exists_pRegular_lift
        (QuotientGroup.mk'_surjective Z) 2 Nat.prime_two q
        (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hodd)
      refine ⟨g, ?_, he⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hg)
    · intros; rfl
  unfold normalized
  rw [hsum, Z.card_eq_card_quotient_mul_card_subgroup, Nat.cast_mul, mul_inv_rev, mul_assoc]
  congr 5
  exact Subsingleton.elim _ _

theorem normalized_equiv {K : Type*} [Group K] [Finite K]
    (e : G ≃* K) (f : K → ℝ) : normalized (fun g => f (e g)) = normalized f := by
  classical
  unfold normalized
  rw [Nat.card_congr e.toEquiv]
  congr 1
  exact Fintype.sum_equiv e.toEquiv _ _ (fun g => by
    change (if Odd (orderOf g) then f (e g) else 0) =
      if Odd (orderOf (e g)) then f (e g) else 0
    rw [e.orderOf_eq])
theorem normalized_congr {f h : G → ℝ}
    (he : ∀ g, Odd (orderOf g) → f g = h g) : normalized f = normalized h := by
  classical
  unfold normalized
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  split_ifs with hg
  · exact he g hg
  · rfl

theorem normalized_twoGroup (hG : IsPGroup 2 G) (f : G → ℝ) :
    normalized f = (Nat.card G : ℝ)⁻¹ * f 1 := by
  classical
  unfold normalized
  congr 1
  rw [Finset.sum_eq_single 1]
  · simp
  · intro g _ hne
    have hn : ¬ Odd (orderOf g) := fun hg =>
      (Nat.not_even_iff_odd.mpr hg) (even_iff_two_dvd.mpr (hG.dvd_orderOf hne))
    simp only [if_neg hn]
  · simp
end OddElementSum
