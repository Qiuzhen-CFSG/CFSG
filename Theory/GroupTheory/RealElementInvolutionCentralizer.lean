module
public import Theory.GroupTheory.EvenCentralizerFixedInvolution
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Real elements inside involution centralizers

For a real element with even centralizer, take an odd power of an inverter
that has two-power order. Its cyclic two-group fixes an involution of the
centralizer. Both the original element and this inverter then lie in that
involution centralizer. No assumption that the inverter has order two is used.

Source application: the J4 local exclusion in Aschbacher--Smith 12.1.1,
printed p.788, via the two native involution centralizers.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- A real element with even centralizer has an inverter in an involution centralizer. -/
theorem real_element_in_involution_centralizer
    {G : Type*} [Group G] [Finite G] (x : G) (hr : IsConj x x⁻¹)
    (hc : 2 ∣ Nat.card (centralizer (zpowers x : Set G))) :
    ∃ z a : G, orderOf z = 2 ∧ x ∈ centralizer ({z} : Set G) ∧
      a ∈ centralizer ({z} : Set G) ∧ a*x*a⁻¹ = x⁻¹ := by
  obtain ⟨a,ha⟩ := isConj_iff.mp hr
  obtain ⟨k,m,hm,ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  have hpow : (a^m)^(2^k) = 1 := by
    rw [←pow_mul,Nat.mul_comm,←ho,pow_orderOf_eq_one]
  have hi : a^m*x*(a^m)⁻¹ = x⁻¹ := by
    obtain ⟨j,rfl⟩ := hm
    have he : ∀ j : ℕ, a^(2*j+1)*x*(a^(2*j+1))⁻¹ = x⁻¹ := by
      intro j
      induction j with
      | zero => simpa using ha
      | succ j ih =>
        rw [show 2*(j+1)+1 = (2*j+1)+2 by omega,pow_add,pow_two]
        calc
          _ = a^(2*j+1) * (a * (a*x*a⁻¹) * a⁻¹) * (a^(2*j+1))⁻¹ := by group
          _ = a^(2*j+1) * (a * x⁻¹ * a⁻¹) * (a^(2*j+1))⁻¹ := by rw [ha]
          _ = a^(2*j+1) * x * (a^(2*j+1))⁻¹ := by
            have hh := congrArg Inv.inv ha
            simp only [mul_inv_rev,inv_inv,←mul_assoc] at hh
            rw [hh]
          _ = x⁻¹ := ih
    exact he j
  let A := zpowers x
  let R := zpowers (a^m)
  have hR : IsPGroup 2 R := IsPGroup.of_card_dvd_pow (n := k) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hpow)
  have hn : R ≤ normalizer (A : Set G) := by
    apply zpowers_le.mpr
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    change zpowers (a^m*x*(a^m)⁻¹) = zpowers x
    rw [hi,zpowers_inv]
  obtain ⟨z,hz,h⟩ := exists_involution_centralizing_normalizing_two_group A R hR hn hc
  exact ⟨z,a^m,hz,h ((show A ≤ A ⊔ R from le_sup_left) (mem_zpowers x)),
    h ((show R ≤ A ⊔ R from le_sup_right) (mem_zpowers (a^m))),hi⟩
end Theory.GroupTheory
