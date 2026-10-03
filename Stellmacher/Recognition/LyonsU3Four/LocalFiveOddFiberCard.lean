module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveQuarticExtensionValues
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveOddElements

/-!
# Odd-element counts in the local complement fibers

For each nonidentity element of the complement, projection of the odd fiber to
`S / Z(S)` is a bijection. The fixed-point-free action on this quotient makes
its displacement map surjective; conjugating a complement element therefore
supplies an odd lift of every coset. Two odd lifts differ by a central
involution, which their fifth powers force to be trivial. The quotient has
sixteen elements. The identity fiber contains only the identity.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373–374,
equation (3.3).
-/

namespace Stellmacher.Recognition.LyonsU3Four
private theorem complement_generates : ∀ x : FiveComplement, x ≠ 1 →
    ∃ n : Fin 5, x ^ (n : ℕ) = Multiplicative.ofAdd (1 : ZMod 5) := by decide

variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
variable (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))

include h β hβ hα
private theorem quotient_fixed (x : FiveComplement) (hx : x ≠ 1)
    (q : S ⧸ Subgroup.center S)
    (hq : (Subgroup.quotientAut (Subgroup.center S) (α x)) q = q) : q = 1 := by
  obtain ⟨n, hn⟩ := complement_generates x hx
  have hp (k : ℕ) : (Subgroup.quotientAut (Subgroup.center S) (α x) ^ k) q = q := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hq, ih]
  apply order_fifteen_cube_quotient_fixed_eq_one S h β hβ
  have he := hp n
  rw [← map_pow, ← map_pow, hn, hα, map_pow] at he
  exact he

private theorem quotient_displacement_surjective (x : FiveComplement) (hx : x ≠ 1) :
    Function.Surjective (fun q : S ⧸ Subgroup.center S =>
      q * (Subgroup.quotientAut (Subgroup.center S) (α x) q)⁻¹) := by
  apply Finite.surjective_of_injective
  intro q r he
  let a := Subgroup.quotientAut (Subgroup.center S) (α x)
  have he' : a q * q⁻¹ = a r * r⁻¹ := by
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv he
  have hf : a (r⁻¹ * q) = r⁻¹ * q := by
    rw [map_mul, map_inv]
    calc
      (a r)⁻¹ * a q = (a r)⁻¹ * (a q * q⁻¹) * q := by group
      _ = (a r)⁻¹ * (a r * r⁻¹) * q := by rw [he']
      _ = r⁻¹ * q := by group
  exact (inv_mul_eq_one.mp (quotient_fixed h β hβ α hα x hx _ hf)).symm

private theorem central_inl_commute (c : S) (hc : c ∈ Subgroup.center S)
    (u : LocalFiveGroup S α) : Commute (SemidirectProduct.inl c) u := by
  change SemidirectProduct.inl c * u = u * SemidirectProduct.inl c
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rw [localFive_action_fixes_center h β hβ α hα u.right ⟨c, hc⟩]
    exact (Subgroup.mem_center_iff.mp hc u.left).symm
  · simp

private theorem odd_fiber_injective (x : FiveComplement) (hx : x ≠ 1) :
    Function.Injective (fun u : {u : LocalFiveGroup S α //
      Odd (orderOf u) ∧ u.right = x} => QuotientGroup.mk' (Subgroup.center S) u.1.left) := by
  intro u v he
  have hu1 : u.1 ≠ 1 := by intro he; exact hx (u.2.2.symm.trans (by simp [he]))
  have hv1 : v.1 ≠ 1 := by intro he; exact hx (v.2.2.symm.trans (by simp [he]))
  have hu5 : u.1 ^ 5 = 1 := by
    simpa only [localFive_odd_order_eq_five h α u.1 u.2.1 hu1] using pow_orderOf_eq_one u.1
  have hv5 : v.1 ^ 5 = 1 := by
    simpa only [localFive_odd_order_eq_five h α v.1 v.2.1 hv1] using pow_orderOf_eq_one v.1
  let c : S := u.1.left / v.1.left
  have hc : c ∈ Subgroup.center S := QuotientGroup.eq_iff_div_mem.mp he
  let z : LocalFiveGroup S α := SemidirectProduct.inl c
  have hz2 : z ^ 2 = 1 := by
    let := h.center_elementary
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian c hc, map_one]
  have huv : u.1 = z * v.1 := by
    apply SemidirectProduct.ext
    · change u.1.left = c * α 1 v.1.left
      rw [map_one, MulAut.one_apply]
      exact (div_mul_cancel _ _).symm
    · simpa [z] using u.2.2.trans v.2.2.symm
  have hz5 : z ^ 5 = 1 := by
    rw [huv, (central_inl_commute h β hβ α hα c hc v.1).mul_pow, hv5, mul_one] at hu5
    exact hu5
  have hz1 : z = 1 := by
    calc
      z = z ^ 5 := by
        change z = z ^ (2 * 2 + 1)
        rw [pow_succ, pow_mul, hz2]
        simp
      _ = 1 := hz5
  apply Subtype.ext
  simpa [hz1] using huv

private theorem odd_fiber_surjective (x : FiveComplement) (hx : x ≠ 1) :
    Function.Surjective (fun u : {u : LocalFiveGroup S α //
      Odd (orderOf u) ∧ u.right = x} => QuotientGroup.mk' (Subgroup.center S) u.1.left) := by
  intro q
  obtain ⟨r, hr⟩ := quotient_displacement_surjective h β hβ α hα x hx q
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center S) r
  let u : LocalFiveGroup S α := MulAut.conj (SemidirectProduct.inl s) (SemidirectProduct.inr x)
  have hx5 : x ^ 5 = 1 := by
    have hh : ∀ t : FiveComplement, t ^ 5 = 1 := by decide
    exact hh x
  have hu5 : u ^ 5 = 1 := by
    change (MulAut.conj (SemidirectProduct.inl s) (SemidirectProduct.inr x)) ^ 5 = 1
    rw [← map_pow, ← map_pow, hx5, map_one, map_one]
  have huo : Odd (orderOf u) := Odd.of_dvd_nat (by decide : Odd 5)
    (orderOf_dvd_of_pow_eq_one hu5)
  have hur : u.right = x := by simp [u, MulAut.conj_apply]
  refine ⟨⟨u, huo, hur⟩, ?_⟩
  change QuotientGroup.mk' (Subgroup.center S) u.left = q
  rw [← hr]
  simp only [Subgroup.quotientAut_apply_mk]
  simp [u, MulAut.conj_apply]

variable (S)

/-- The identity complement fiber has one odd element; every other fiber has sixteen. -/
public theorem localFive_odd_fiber_card (x : FiveComplement) :
    Nat.card {u : LocalFiveGroup S α // Odd (orderOf u) ∧ u.right = x} =
      if x = 1 then 1 else 16 := by
  classical
  by_cases hx : x = 1
  · subst x
    rw [if_pos rfl]
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨1, by simp⟩, ?_⟩
    intro u
    exact Subtype.ext ((localFive_odd_right_eq_one_iff S α u.1 u.2.1).mp u.2.2)
  · rw [if_neg hx, ← center_quotient_card S h]
    exact Nat.card_congr (Equiv.ofBijective _
      ⟨odd_fiber_injective h β hβ α hα x hx,
        odd_fiber_surjective h β hβ α hα x hx⟩)
end Stellmacher.Recognition.LyonsU3Four
