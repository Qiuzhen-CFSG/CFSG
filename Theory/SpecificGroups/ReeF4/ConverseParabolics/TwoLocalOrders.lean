module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.CoreActionRigidity.Structure
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Prime exclusions for Ree two-local normalizers

The full linear parabolic has five-free order: its radical is a two-group,
its Levi projects to SL₂(q) times the field torus, and q = 2^(2m+1) has
q² congruent to four modulo five. The established Suzuki-side three-free
calculation and full normalizer coverage therefore exclude fifteen from
the order of every normalizer of a nonidentity two-subgroup.

Source: GLS3 Theorem 3.1.3 and §§2.3, 2.6; Aschbacher–Smith F.1.12,
printed pp.263–264. This gives the native Ree order obstruction used in
the deleted-A₅ cases of C.3.1 and 13.5.15.
-/

public section

open Subgroup
namespace ReeF4.ConverseParabolics
private theorem field_square_mod_five (m : ℕ) :
    (2 ^ (2 * m + 1)) ^ 2 % 5 = 4 := by
  rw [← pow_mul]
  have he : (2 * m + 1) * 2 = 4 * m + 2 := by omega
  rw [he, pow_add, pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private theorem units_five_free (m : ℕ) : ¬ 5 ∣ Nat.card (CoefficientField m)ˣ := by
  rw [Nat.card_units, field_card]
  intro hd
  have hmod := Nat.dvd_iff_mod_eq_zero.mp hd
  have hpos : 0 < 2 ^ (2 * m + 1) := by positivity
  have hq : 2 ^ (2 * m + 1) % 5 = 1 := by omega
  have hs := field_square_mod_five m
  rw [Nat.pow_mod, hq] at hs
  norm_num at hs

private theorem sl_two_five_free (m : ℕ) :
    ¬ 5 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m)) := by
  rw [Atlas.card_sl_two, field_card]
  intro hd
  rcases (show Nat.Prime 5 by decide).dvd_mul.mp hd with hq | hs
  · exact (by decide : ¬ 5 ∣ 2) ((show Nat.Prime 5 by decide).dvd_of_dvd_pow hq)
  · have hmod := Nat.dvd_iff_mod_eq_zero.mp hs
    have hsq := field_square_mod_five m
    omega

/-- The full linear parabolic has five-free order, including its field torus. -/
theorem linear_parabolic_five_free {m : ℕ} (hm : 1 ≤ m) :
    ¬ 5 ∣ Nat.card (parabolic m .linear) := by
  let f := linearProjection hm
  have ht : ¬ 5 ∣ Nat.card
      (Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ) := by
    rw [Nat.card_prod]
    exact fun hd => ((show Nat.Prime 5 by decide).dvd_mul.mp hd).elim
      (sl_two_five_free m) (units_five_free m)
  intro hd
  rw [← f.ker.card_mul_index, index_ker] at hd
  rcases (show Nat.Prime 5 by decide).dvd_mul.mp hd with hk | hr
  · obtain ⟨n, hn⟩ := (linearProjection_ker_isPGroup hm).exists_card_eq
    change 5 ∣ Nat.card (linearProjection hm).ker at hk
    rw [hn] at hk
    exact (by decide : ¬ 5 ∣ 2) ((show Nat.Prime 5 by decide).dvd_of_dvd_pow hk)
  · exact ht (hr.trans f.range.card_subgroup_dvd_card)

/-- No two-local normalizer in a large Ree group has order divisible by fifteen. -/
theorem normalizer_fifteen_free {m : ℕ} (hm : 1 ≤ m)
    (R : Subgroup (Model m)) (hR : R ≠ ⊥) (hp : IsPGroup 2 R) :
    ¬ 15 ∣ Nat.card (normalizer (R : Set (Model m))) := by
  obtain ⟨g, s, hle⟩ := normalizer_cover hm R hR hp
  intro hd
  have hc := card_dvd_of_le hle
  rw [card_map_of_injective (MulAut.conj g).injective] at hc
  have h15 := hd.trans hc
  cases s with
  | linear => exact linear_parabolic_five_free hm ((by decide : 5 ∣ 15).trans h15)
  | suzuki => exact suzuki_parabolic_three_free hm ((by decide : 3 ∣ 15).trans h15)
end ReeF4.ConverseParabolics
