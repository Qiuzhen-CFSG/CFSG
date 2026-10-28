module
public import ABG.ChapterII.Section1.WreathedBase
public import ABG.ChapterII.Section1.WreathedRelations
public import ABG.ChapterII.Section1.WreathedDiagonalOrder

/-!
# Outer elements of order four in a wreathed group

In the chosen wreathed presentation of ABG Chapter II §1 Lemma 2(v)
(article pp.9–10), every element outside the abelian base `U` of order four
lies in the distinguished quaternion subgroup `Y`.

The normal form writes an outer element as `s^i*t^j*z`. Its square is the
central diagonal power `u^(i+j)`. Since `u` has exact order `2^n`, order four
forces the exponent modulo `2^n` to be `2^(n-1)`. The element is consequently
`(r^j)⁻¹*d`, which lies in `Y`. The central-square consequence is also exposed
for the quaternion containment argument. Exact diagonal order uses the
presentation's prescribed cardinality through uniqueness of coordinates.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

public theorem outer_normal_form_square (i j : ℕ) :
    (P.s ^ i * P.t ^ j * P.z) ^ 2 = P.u ^ (i + j) := by
  have hc : Commute P.s P.t := P.commute
  calc
    _ = P.s ^ i * P.t ^ j * (P.z * P.s ^ i) * P.t ^ j * P.z := by simp only [pow_two]; group
    _ = P.s ^ i * P.t ^ j * (P.t ^ i * P.z) * P.t ^ j * P.z := by rw [P.z_mul_s_pow]
    _ = P.s ^ i * (P.t ^ j * P.t ^ i) * (P.z * P.t ^ j) * P.z := by group
    _ = P.s ^ i * (P.t ^ j * P.t ^ i) * (P.s ^ j * P.z) * P.z := by rw [P.z_mul_t_pow]
    _ = P.s ^ i * (P.t ^ j * P.t ^ i) * P.s ^ j := by simp [mul_assoc, ← pow_two, P.z_sq]
    _ = (P.s ^ i * P.s ^ j) * (P.t ^ j * P.t ^ i) := by
      rw [mul_assoc, ← (hc.pow_pow j j |>.mul_right (hc.pow_pow j i)).eq, ← mul_assoc]
    _ = P.u ^ (i + j) := by rw [← pow_add, ← pow_add, Nat.add_comm j i, u, hc.mul_pow]

public theorem u_commute (g : S) : Commute P.u g := by
  have hc : Commute P.s P.t := P.commute
  have hs : Commute P.u P.s := (Commute.refl _).mul_left hc.symm
  have ht : Commute P.u P.t := hc.mul_left (Commute.refl _)
  have hz : Commute P.u P.z := by
    change P.s * P.t * P.z = P.z * (P.s * P.t)
    rw [← mul_assoc P.z, P.z_mul_s, mul_assoc P.t, P.z_mul_t]
    rw [← mul_assoc, ← P.commute]
  rcases P.exists_normal_form g with ⟨i,j,b,rfl⟩
  exact ((hs.pow_right _).mul_right (ht.pow_right _)).mul_right (hz.pow_right _)

public theorem exists_outer_normal_form {g : S} (hg : g ∉ P.U) :
    ∃ i j : ℕ, P.s ^ i * P.t ^ j * P.z = g := by
  rcases P.exists_normal_form g with ⟨i,j,b,h⟩
  have hb : b.val = 1 := by
    have := b.isLt
    by_contra hn
    have hb : b.val = 0 := by omega
    apply hg
    rw [P.mem_U_iff]
    exact ⟨i.val, j.val, by simpa [hb] using h⟩
  exact ⟨i.val,j.val,by simpa [hb] using h⟩

public theorem outer_square_commute {g : S} (hg : g ∉ P.U) (a : S) :
    Commute (g ^ 2) a := by
  rcases P.exists_outer_normal_form hg with ⟨i,j,rfl⟩
  rw [P.outer_normal_form_square]
  exact (P.u_commute a).pow_left _

private theorem reduced_double {N a : ℕ} (ha : a < N) (ha0 : a ≠ 0)
    (h : (a * 2) % N = 0) : a * 2 = N := by
  by_cases hh : a * 2 < N
  · rw [Nat.mod_eq_of_lt hh] at h
    omega
  · have hle : N ≤ a * 2 := by omega
    have hlt : a * 2 - N < N := by omega
    rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hlt] at h
    omega

private theorem half_power_of_order_four (i j : ℕ)
    (ho : orderOf (P.s ^ i * P.t ^ j * P.z) = 4)
    (hu : orderOf P.u = 2 ^ n) :
    (i + j) % (2 ^ n) = 2 ^ (n - 1) := by
  let a := (i+j) % (2^n)
  have ha : a < 2^n := Nat.mod_lt _ (by positivity)
  have he : P.u ^ a = (P.s ^ i * P.t ^ j * P.z) ^ 2 := by
    rw [P.outer_normal_form_square]
    dsimp only [a]
    rw [← hu]
    exact pow_mod_orderOf _ _
  have hn : a ≠ 0 := by
    intro hzero
    have hsq : (P.s ^ i * P.t ^ j * P.z) ^ 2 = 1 := by rw [← he, hzero, pow_zero]
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [ho] at hd
    norm_num at hd
  have hmod : (a * 2) % (2^n) = 0 := by
    have hpow : P.u ^ (a * 2) = 1 := by
      rw [pow_mul, he, ← pow_mul]
      norm_num
      rw [← ho, pow_orderOf_eq_one]
    exact Nat.mod_eq_zero_of_dvd (hu ▸ orderOf_dvd_of_pow_eq_one hpow)
  have hd := reduced_double ha hn hmod
  have hn : n = (n - 1) + 1 := by have := P.height; omega
  have hp : 2^n = 2^(n-1)*2 := by conv_lhs => rw [hn, pow_succ]
  rw [hp] at hd
  exact Nat.eq_of_mul_eq_mul_right (by omega) hd

public theorem outer_order_four_mem_Y {g : S} (hg : g ∉ P.U)
    (ho : orderOf g = 4) : g ∈ P.Y := by
  rcases P.exists_outer_normal_form hg with ⟨i,j,rfl⟩
  have hsum := P.half_power_of_order_four i j ho P.orderOf_u
  have hc : Commute P.s P.t := P.commute
  have hh : 2 ^ (n - 1) < 2 ^ n := by
    apply Nat.pow_lt_pow_right (by omega)
    have := P.height
    omega
  have he : P.s ^ (i + j) = P.s ^ (2^(n-1)) :=
    pow_eq_pow_of_modEq (show Nat.ModEq (2^n) (i+j) (2^(n-1)) by
      change (i+j) % (2^n) = (2^(n-1)) % (2^n)
      rw [hsum, Nat.mod_eq_of_lt hh]) P.s_pow
  have hr : P.r ∈ P.Y := Subgroup.subset_closure (by simp)
  have hd : P.d ∈ P.Y := Subgroup.subset_closure (by simp)
  have hm := P.Y.mul_mem (P.Y.inv_mem (P.Y.pow_mem hr j)) hd
  convert hm using 1
  dsimp only [r, d, x₂]
  rw [hc.inv_right.mul_pow, inv_pow, mul_inv_rev, inv_inv, ← he, pow_add]
  rw [(hc.pow_pow i j).eq, ((Commute.refl P.s).pow_pow i j).eq]
  group

end ABG.Wreathed.Presentation
