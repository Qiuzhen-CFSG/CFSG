module

public import Theory.GroupAction.FiveOrbitSumFree
public import Theory.GroupAction.Order512FiveInvolutionCosets

/-!
# Commuting involutions in the order-512 core

All nonidentity derived cosets admitting square-one lifts form one five-orbit
in the elementary abelian quotient of order sixteen. That orbit is sum-free.
If b and x commute and both square to one, so does bx. Thus x or bx must lie
in the derived subgroup whenever b does not.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–676, the involutory cosets used in the centralizer calculation.
-/

namespace Theory.GroupAction
open Subgroup

/-- An involution commuting with a fixed involution outside the derived
subgroup belongs to one of the two derived cosets represented by 1 and b. -/
public theorem parrott_commuting_involution_derived_cosets {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 512)
    (hclass : 3 ≤ Group.nilpotencyClass V) (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V ≤ center V)
    (b : V) (hb : b ^ 2 = 1) (hbD : b ∉ commutator V)
    (x : V) (hx : x ^ 2 = 1) (hcomm : Commute b x) :
    x ∈ commutator V ∨ b * x ∈ commutator V := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 V) := ⟨hV⟩
  let _ : Group.IsNilpotent V := hV.isNilpotent
  obtain ⟨_, _, hPhi, hUpper, _, hDcard⟩ :=
    parrott_twoGroup_structure hV hcard hclass hA hfixed
  let D := commutator V
  let q := QuotientGroup.mk' D
  let _ : IsElementaryAbelian 2 (V ⧸ D) := by
    let _ := isElementaryAbelian_quotient_frattini (R := V) (p := 2)
    let e := QuotientGroup.quotientMulEquivOfEq hPhi
    refine { is_comm := ⟨fun x y => e.injective ?_⟩, exponent_dvd_p := ?_ }
    · simpa only [map_mul] using (mul_comm' (e x) (e y))
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply e.injective
        simpa only [map_pow, map_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ frattini V)) (e x))
  let _ : MulDistribMulAction A (V ⧸ D) :=
    quotientMulDistribMulAction D (isInvariant_of_characteristic D)
  have hquot : Nat.card (V ⧸ D) = 16 := by
    have hh := D.index_mul_card
    change Nat.card (V ⧸ D) * Nat.card D = Nat.card V at hh
    rw [hDcard, hcard] at hh
    omega
  have hZD : center V ≤ D := by
    change center V ≤ commutator V
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono V (show 1 ≤ 2 by decide)
  have hfix : FixedPoints.subgroup A (V ⧸ D) = ⊥ := by
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable V) (by rw [hA, hcard]; decide)
      D (isInvariant_of_characteristic D), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hfixed.trans hZD
  have hbne : q b ≠ 1 := fun hh => hbD ((QuotientGroup.eq_one_iff b).mp hh)
  have hmem (y : V) (hy : y ^ 2 = 1) (hyD : y ∉ D) :
      q y ∈ MulAction.orbit A (q b) := by
    obtain ⟨a, ha⟩ := (parrott_involutory_derived_coset_census
      hV hcard hclass hA hfixed b hb hbD).2 y hy hyD
    change a • q y = q b at ha
    exact ⟨a⁻¹, by change a⁻¹ • q b = q y; rw [← ha]; exact inv_smul_smul a (q y)⟩
  by_cases hxD : x ∈ D
  · exact Or.inl hxD
  right
  by_contra hbxD
  have hbx : (b * x) ^ 2 = 1 := by rw [hcomm.mul_pow, hb, hx, mul_one]
  have hmem' := hmem (b * x) hbx hbxD
  rw [map_mul] at hmem'
  exact five_orbit_base_mul_not_mem hA hquot hfix (q b) hbne (q x)
    (hmem x hx hxD) hmem'

end Theory.GroupAction
