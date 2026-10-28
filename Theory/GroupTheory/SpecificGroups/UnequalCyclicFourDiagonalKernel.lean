module

public import Theory.GroupTheory.SpecificGroups.UnequalCyclicFourNormControlDefs

/-!
# The involutive kernel of the two diagonal coordinates

An involution-fixing automorphism of C_(2 ^ n) × C₄, with n ≥ 3, whose square
and diagonal coordinates are trivial belongs to the norm-control subgroup.
Writing its two generator images as u and w, the short coordinate of f² = 1
forces u.2² = 1. The long coordinate then says that the long exponent r
satisfies r² = 1 modulo 2 ^ n. Since r = 1 modulo four, 2 ^ (n - 1) divides r - 1,
so both generator squares are fixed. On fourth roots the displacement is an
involution with trivial short coordinate, hence lies in the long power line.

This is the coordinate kernel argument associated with MacWilliams,
*On 2-groups with no normal abelian subgroups of rank 3*, Trans. AMS 150
(1970), §1.2. The elementary divisibility argument follows the local calculation
in `Theory.GroupTheory.PGroup.CyclicSelfCentralizerFour`.
-/

open Subgroup

namespace UnequalCyclicFourNormControl

private theorem generator_pow_val (k : ℕ) [NeZero k] (z : Multiplicative (ZMod k)) :
    (Multiplicative.ofAdd (1 : ZMod k)) ^ z.toAdd.val = z := by
  apply Multiplicative.toAdd.injective
  simp [toAdd_pow, nsmul_eq_mul]

private theorem eq_generator_powers (n : ℕ) (x : V n) :
    x = longGenerator n ^ x.1.toAdd.val * shortGenerator n ^ x.2.toAdd.val := by
  apply Prod.ext
  · simpa [longGenerator, shortGenerator] using (generator_pow_val (2 ^ n) x.1).symm
  · simpa [longGenerator, shortGenerator] using (generator_pow_val 4 x.2).symm

private theorem half_power_dvd_sub_one (n r : ℕ) (hn : 3 ≤ n) (hr4 : r % 4 = 1)
    (hrr : 2 ^ n ∣ r * r - 1) : 2 ^ (n - 1) ∣ r - 1 := by
  have hrlower : 1 ≤ r := by omega
  have hrprod : 2 ^ n ∣ (r - 1) * (r + 1) := by
    convert hrr using 1
    have ht : r - 1 + 1 = r := by omega
    have ht2 : r * r - 1 + 1 = r * r := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hrplus : r + 1 = 2 * (r / 2 + 1) := by omega
  have hsplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hsplit, hrplus, ← mul_assoc, mul_right_comm] at hrprod
  have hdiv := (Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)).mp hrprod
  have hodd : Nat.Coprime 2 (r / 2 + 1) := Nat.coprime_two_left.mpr (by
    exact ⟨r / 4, by omega⟩)
  exact (hodd.pow_left (n - 1)).dvd_mul_right.mp hdiv

/-- Involutive automorphisms with trivial diagonal coordinates satisfy norm control. -/
public theorem diagonal_kernel_mem (n : ℕ) (hn : 3 ≤ n) (f : involutionFixing n)
    (hf : (f : MulAut (V n)) ^ 2 = 1) (hd : diagonal n hn f = 1) :
    (f : MulAut (V n)) ∈ controlSubgroup n := by
  -- Record the generator images and the coordinates of the long-generator image.
  let u := (f : MulAut (V n)) (longGenerator n)
  let w := (f : MulAut (V n)) (shortGenerator n)
  let r := u.1.toAdd.val
  let s := u.2.toAdd.val
  have hr4 : r % 4 = 1 := by
    have h : (ZMod.castHom
        (show 4 ∣ 2 ^ n from pow_dvd_pow 2 (show 2 ≤ n by omega)) (ZMod 4))
        u.1.toAdd = 1 := congrArg Prod.fst hd
    rw [← ZMod.natCast_zmod_val u.1.toAdd, map_natCast] at h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, show (1 : ZMod 4).val = 1 from rfl] using hv
  have hw : w.2 = (shortGenerator n).2 := by
    apply Multiplicative.toAdd.injective
    change w.2.toAdd = (1 : ZMod 4)
    exact congrArg (fun z : ZMod 4 × ZMod 4 => z.2) hd
  have hw2 : w ^ 2 = (shortGenerator n) ^ 2 := by
    rw [← map_pow]
    apply f.property
    apply Prod.ext
    · simp [shortGenerator]
    · change ((Multiplicative.ofAdd (1 : ZMod 4)) ^ 2) ^ 2 = 1
      decide
  have hff : (f : MulAut (V n)) u = longGenerator n := by
    have h := congrArg (fun a : MulAut (V n) => a (longGenerator n)) hf
    exact h
  have he : u ^ r * w ^ s = longGenerator n := by
    calc
      u ^ r * w ^ s = (f : MulAut (V n)) (longGenerator n ^ r * shortGenerator n ^ s) := by
        rw [map_mul, map_pow, map_pow]
      _ = (f : MulAut (V n)) u := congrArg _ (eq_generator_powers n u).symm
      _ = longGenerator n := hff
  -- The short coordinate of f² forces the lower-left coordinate to be even.
  have hs2 : u.2 ^ 2 = 1 := by
    have h := congrArg (fun x : V n => x.2.toAdd) he
    change (r • u.2.toAdd) + s • w.2.toAdd = 0 at h
    have hr : (r : ZMod 4) = 1 := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast, show (1 : ZMod 4).val = 1 from rfl] using hr4
    rw [hw] at h
    change r • u.2.toAdd + s • (1 : ZMod 4) = 0 at h
    simp only [nsmul_eq_mul, hr, one_mul, mul_one] at h
    change u.2.toAdd + (u.2.toAdd.val : ZMod 4) = 0 at h
    rw [ZMod.natCast_zmod_val] at h
    apply Multiplicative.toAdd.injective
    change 2 • u.2.toAdd = 0
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, two_mul] using h
  have hsEven : 2 ∣ s := by
    have h := congrArg Multiplicative.toAdd hs2
    change 2 • u.2.toAdd = 0 at h
    have hz : ((2 * s : ℕ) : ZMod 4) = 0 := by
      simpa [Nat.cast_mul, s, nsmul_eq_mul] using h
    have hh := (ZMod.natCast_eq_zero_iff _ _).mp hz
    omega
  have hws : w.1 ^ s = 1 := by
    obtain ⟨t, ht⟩ := hsEven
    rw [ht, pow_mul]
    have hh : w.1 ^ 2 = 1 := by simpa [shortGenerator] using congrArg Prod.fst hw2
    rw [hh, one_pow]
  -- The cross term vanishes, leaving a square root of one modulo 2^n.
  have hrr : 2 ^ n ∣ r * r - 1 := by
    have hh := congrArg Prod.fst he
    change u.1 ^ r * w.1 ^ s = Multiplicative.ofAdd (1 : ZMod (2 ^ n)) at hh
    rw [hws, mul_one, ← generator_pow_val (2 ^ n) u.1, ← pow_mul] at hh
    have hz := congrArg Multiplicative.toAdd hh
    have hrpos : 1 ≤ r * r := by
      have : 1 ≤ r := by omega
      nlinarith
    have hm : Nat.ModEq (2 ^ n) (r * r) 1 := by
      have hz' : ((r * r : ℕ) : ZMod (2 ^ n)) = 1 := by
        simpa [toAdd_pow, nsmul_eq_mul, r] using hz
      exact (ZMod.natCast_eq_natCast_iff (r * r) 1 (2 ^ n)).mp (by simpa only [Nat.cast_one] using hz')
    exact (Nat.modEq_iff_dvd' hrpos).mp hm.symm
  have hrhalf := half_power_dvd_sub_one n r hn hr4 hrr
  have hsplit : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ]
    congr 1
    omega
  have hu2 : u ^ 2 = (longGenerator n) ^ 2 := by
    apply Prod.ext
    · obtain ⟨t, ht⟩ := hrhalf
      have hr : r = 1 + 2 ^ (n - 1) * t := by
        have : 1 ≤ r := by omega
        omega
      change u.1 ^ 2 = (Multiplicative.ofAdd (1 : ZMod (2 ^ n))) ^ 2
      rw [← generator_pow_val (2 ^ n) u.1]
      change ((Multiplicative.ofAdd (1 : ZMod (2 ^ n))) ^ r) ^ 2 = _
      rw [← pow_mul, hr]
      have he : (1 + 2 ^ (n - 1) * t) * 2 = 2 + 2 ^ n * t := by rw [← hsplit]; ring
      rw [he, pow_add, pow_mul]
      have hp : (Multiplicative.ofAdd (1 : ZMod (2 ^ n))) ^ (2 ^ n) = 1 := by
        simpa using pow_card_eq_one' (x := Multiplicative.ofAdd (1 : ZMod (2 ^ n)))
      rw [hp, one_pow, mul_one]
    · exact hs2
  have hfix (x : V n) : (f : MulAut (V n)) (x ^ 2) = x ^ 2 := by
    rw [eq_generator_powers n x]
    simp only [mul_pow, map_mul, map_pow]
    rw [pow_right_comm _ _ 2, pow_right_comm _ _ 2]
    change (u ^ 2) ^ _ * (w ^ 2) ^ _ = _
    rw [hu2, hw2]
    simp only [pow_right_comm _ 2]
  apply (mem_controlSubgroup n f).mpr
  refine ⟨hfix, ?_⟩
  intro x hx
  have hdis : ((f : MulAut (V n)) x * x⁻¹) ^ 2 = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hfix, mul_inv_cancel]
  have hxs : ∃ y : A n, y ^ 2 = x.1 := roots_le_squares n hn (congrArg Prod.fst hx)
  obtain ⟨y, hy⟩ := hxs
  have hsnd : ((f : MulAut (V n)) x).2 = x.2 := by
    have hxy : x = (y,1) ^ 2 * shortGenerator n ^ x.2.toAdd.val := by
      apply Prod.ext
      · simpa [shortGenerator] using hy.symm
      · simpa [shortGenerator] using (generator_pow_val 4 x.2).symm
    rw [hxy, map_mul, hfix, map_pow]
    change _ * w.2 ^ _ = _
    rw [hw]
    rfl
  have hz : ((f : MulAut (V n)) x * x⁻¹).2 = 1 := by
    change ((f : MulAut (V n)) x).2 * x.2⁻¹ = 1
    rw [hsnd, mul_inv_cancel]
  -- In the long cyclic factor, the involutions are the highest power image.
  have hrange : (powMonoidHom (2 ^ (n - 1)) : A n →* A n).range =
      (powMonoidHom 2).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro z ⟨a, rfl⟩
      change (a ^ (2 ^ (n - 1))) ^ 2 = 1
      rw [← pow_mul, hsplit]
      simpa using pow_card_eq_one' (x := a)
    · rw [IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_ker]
      have hd : 2 ^ (n - 1) ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      have hd2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      simp only [A, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card,
        Nat.gcd_eq_right hd, Nat.gcd_eq_right hd2]
      rw [← hsplit, Nat.mul_div_right _ (by positivity)]
  have ha : ((f : MulAut (V n)) x * x⁻¹).1 ∈
      (powMonoidHom (2 ^ (n - 1)) : A n →* A n).range := by
    rw [hrange]
    exact congrArg Prod.fst hdis
  obtain ⟨a, ha⟩ := ha
  refine ⟨(a,1), Prod.ext ha ?_⟩
  change (1 : C4) ^ (2 ^ (n - 1)) = _
  rw [one_pow, hz]

end UnequalCyclicFourNormControl
