module
public import ABG.ChapterII.Section1.WreathedOuterFour

/-!
# The three involution classes of a wreathed group

For the chosen presentation of height `n ≥ 2`, the elements `x`, `x₂`, and
`z` have order two, are pairwise nonconjugate, and represent every involution.
This is ABG Chapter II §1 Lemma 2(i), article p.9, with the named generators
and cardinality from the preceding presentation.

Unique normal coordinates show that the elements of the base with square one
are exactly `1`, `x`, `x₂`, and `x₃`. Conjugation by `z` interchanges the last
two. The outer square formula forces an outer involution to be `r^i*z`,
which is conjugate to `z` by a power of `s`. Finally, `x` is central and the
only possible conjugates of `x₂` are `x₂` and `x₃`; uniqueness of coordinates
separates the three representatives. The square-one descriptions are also
exported for the four-subgroup and Omega arguments.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem base_eq_iff (i j k l : ℕ) :
    P.s ^ i * P.t ^ j = P.s ^ k * P.t ^ l ↔
      i % 2 ^ n = k % 2 ^ n ∧ j % 2 ^ n = l % 2 ^ n := by
  have h := P.normal_form_zpow_eq_iff (i : ℤ) j 0 k l 0
  simpa only [zpow_natCast, zpow_zero, mul_one, ← Int.natCast_emod, Nat.cast_inj,
    and_true] using h

include P in
private theorem half_double : 2 ^ (n - 1) * 2 = 2 ^ n := by
  have hn : n = (n - 1) + 1 := by have := P.height; omega
  conv_rhs => rw [hn, pow_succ]

include P in
private theorem doubled_mod_zero {i : ℕ} (hi : i < 2 ^ n)
    (h : (i * 2) % 2 ^ n = 0) : i = 0 ∨ i = 2 ^ (n - 1) := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  have hm := P.half_double
  have hp : 0 < 2 ^ (n - 1) := by positivity
  have hklt : k < 2 := by nlinarith
  interval_cases k <;> simp_all; omega

private theorem base_sq_eq_one {i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (h : (P.s ^ i * P.t ^ j) ^ 2 = 1) :
    (i = 0 ∨ i = 2 ^ (n - 1)) ∧ (j = 0 ∨ j = 2 ^ (n - 1)) := by
  have hh : P.s ^ (i * 2) * P.t ^ (j * 2) = P.s ^ 0 * P.t ^ 0 := by
    simpa only [pow_mul, pow_zero, one_mul] using
      ((show Commute P.s P.t from P.commute).pow_pow i j).mul_pow 2 |>.symm.trans h
  have hc := (P.base_eq_iff _ _ _ _).mp hh
  simp only [Nat.zero_mod] at hc
  exact ⟨P.doubled_mod_zero hi hc.1, P.doubled_mod_zero hj hc.2⟩

private theorem bounded_base_form {g : S} (hg : g ∈ P.U) :
    ∃ i j : Fin (2 ^ n), P.s ^ i.val * P.t ^ j.val = g := by
  obtain ⟨i, j, b, he⟩ := P.exists_normal_form g
  obtain ⟨k, l, hkl⟩ := (P.mem_U_iff g).mp hg
  have hb := ((P.normal_form_zpow_eq_iff (i.val : ℤ) j.val b.val k l 0).mp
    (by simpa only [zpow_natCast, zpow_zero, mul_one] using he.trans hkl.symm)).2.2
  have hb0 : b.val = 0 := by
    have hlt := b.isLt
    have hcast : (b.val : ℤ) < 2 := by exact_mod_cast hlt
    rw [Int.emod_eq_of_lt (by positivity) hcast] at hb
    norm_num at hb
    exact_mod_cast hb
  exact ⟨i, j, by simpa only [hb0, pow_zero, mul_one] using he⟩

public theorem base_involution_cases {g : S} (hg : g ∈ P.U) (hsq : g ^ 2 = 1) :
    g = 1 ∨ g = P.x ∨ g = P.x₂ ∨ g = P.x₃ := by
  obtain ⟨i, j, rfl⟩ := P.bounded_base_form hg
  obtain ⟨hi, hj⟩ := P.base_sq_eq_one i.isLt j.isLt hsq
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · left; simp [hi, hj]
  · exact Or.inr (Or.inr (Or.inr (by simp [hi, hj, x₃])))
  · exact Or.inr (Or.inr (Or.inl (by simp [hi, hj, x₂])))
  · exact Or.inr (Or.inl (by rw [P.x_eq_x₂_mul_x₃]; simp [hi, hj, x₂, x₃]))

include P in
private theorem half_lt : 2 ^ (n - 1) < 2 ^ n := by
  have := P.half_double
  have : 0 < 2 ^ (n - 1) := by positivity
  omega

public theorem x₂_orderOf : orderOf P.x₂ = 2 := by
  apply orderOf_eq_prime P.x₂_sq
  intro he
  have hh := (P.base_eq_iff (2 ^ (n - 1)) 0 0 0).mp
    (by simpa [x₂] using he)
  simp only [Nat.zero_mod, Nat.mod_eq_of_lt P.half_lt] at hh
  have : 0 < 2 ^ (n - 1) := by positivity
  omega

public theorem x_orderOf : orderOf P.x = 2 := by
  have hc : Commute P.x₂ P.x₃ := (show Commute P.s P.t from P.commute).pow_pow _ _
  apply orderOf_eq_prime
  · rw [P.x_eq_x₂_mul_x₃, hc.mul_pow, P.x₂_sq, P.x₃_sq, mul_one]
  · intro he
    have hh := (P.base_eq_iff (2 ^ (n - 1)) (2 ^ (n - 1)) 0 0).mp
      (by simpa only [P.x_eq_x₂_mul_x₃, x₂, x₃, pow_zero, one_mul] using he)
    simp only [Nat.zero_mod, Nat.mod_eq_of_lt P.half_lt] at hh
    have : 0 < 2 ^ (n - 1) := by positivity
    omega

private theorem base_ne_z (i j : ℕ) : P.s ^ i * P.t ^ j ≠ P.z := by
  intro he
  have hh := ((P.normal_form_zpow_eq_iff (i : ℤ) j 0 0 0 1).mp
    (by simpa only [zpow_natCast, zpow_zero, zpow_one, mul_one, one_mul] using he)).2.2
  norm_num at hh

public theorem z_not_mem_U : P.z ∉ P.U := by
  intro h
  obtain ⟨i, j, he⟩ := P.bounded_base_form h
  exact P.base_ne_z i.val j.val he

public theorem z_orderOf : orderOf P.z = 2 := by
  apply orderOf_eq_prime P.z_sq
  exact fun h => P.base_ne_z 0 0 (by simpa using h.symm)

private theorem conj_x₂_cases (g : S) :
    g * P.x₂ * g⁻¹ = P.x₂ ∨ g * P.x₂ * g⁻¹ = P.x₃ := by
  obtain ⟨i, j, b, rfl⟩ := P.exists_normal_form g
  have hc : Commute P.s P.t := P.commute
  have hc2 : Commute (P.s ^ i.val * P.t ^ j.val) P.x₂ :=
    ((Commute.self_pow P.s _).pow_left _).mul_left (hc.symm.pow_pow _ _)
  have hc3 : Commute (P.s ^ i.val * P.t ^ j.val) P.x₃ :=
    (hc.pow_pow _ _).mul_left ((Commute.self_pow P.t _).pow_left _)
  have hb := b.isLt
  have hcases : b.val = 0 ∨ b.val = 1 := by omega
  rcases hcases with h | h
  · left
    simp only [h, pow_zero, mul_one]
    rw [hc2.eq, mul_assoc, mul_inv_cancel, mul_one]
  · right
    simp only [h, pow_one]
    have hswap : P.z * P.x₂ * P.z⁻¹ = P.x₃ := by
      rw [x₂, P.z_mul_s_pow, mul_assoc, mul_inv_cancel, mul_one]; rfl
    calc
      _ = (P.s ^ i.val * P.t ^ j.val) * (P.z * P.x₂ * P.z⁻¹) *
          (P.s ^ i.val * P.t ^ j.val)⁻¹ := by group
      _ = P.x₃ := by rw [hswap, hc3.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem x_ne_x₂ : P.x ≠ P.x₂ := by
  intro h
  have hh := (P.base_eq_iff (2 ^ (n - 1)) (2 ^ (n - 1)) (2 ^ (n - 1)) 0).mp
    (by simpa only [P.x_eq_x₂_mul_x₃, x₂, x₃, pow_zero, mul_one] using h)
  simp only [Nat.zero_mod, Nat.mod_eq_of_lt P.half_lt] at hh
  have : 0 < 2 ^ (n - 1) := by positivity
  omega

public theorem x₂_not_isConj_z : ¬ IsConj P.x₂ P.z := by
  intro hconj
  obtain ⟨g, he⟩ := isConj_iff.mp hconj
  rcases P.conj_x₂_cases g with h | h
  · exact P.base_ne_z (2 ^ (n - 1)) 0 (by simpa [x₂] using h.symm.trans he)
  · exact P.base_ne_z 0 (2 ^ (n - 1)) (by simpa [x₃] using h.symm.trans he)

public theorem outer_involution_form {g : S} (hg : g ∉ P.U) (hsq : g ^ 2 = 1) :
    ∃ i : ℕ, g = P.r ^ i * P.z := by
  obtain ⟨i, j, rfl⟩ := P.exists_outer_normal_form hg
  have hu : P.u ^ (i + j) = 1 := (P.outer_normal_form_square i j).symm.trans hsq
  have hbase : P.s ^ (i + j) * P.t ^ (i + j) = P.s ^ 0 * P.t ^ 0 := by
    simpa only [u, (show Commute P.s P.t from P.commute).mul_pow, pow_zero, one_mul]
      using hu
  have hmod := (P.base_eq_iff _ _ _ _).mp hbase
  have ht : P.t ^ (i + j) = 1 := by
    rw [pow_eq_pow_mod _ P.t_pow, hmod.2, Nat.zero_mod, pow_zero]
  have hj : P.t ^ j = (P.t ^ i)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa only [← pow_add, Nat.add_comm j i] using ht
  refine ⟨i, ?_⟩
  rw [r, (show Commute P.s P.t from P.commute).inv_right.mul_pow, inv_pow, hj]

public theorem x_not_isConj_x₂ : ¬ IsConj P.x P.x₂ := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hc : Commute P.x g := (P.u_commute g).pow_left _
  have hx : P.x = P.x₂ := by
    simpa only [← hc.eq, mul_assoc, mul_inv_cancel, mul_one] using hg
  exact P.x_ne_x₂ hx

public theorem x_not_isConj_z : ¬ IsConj P.x P.z := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hc : Commute P.x g := (P.u_commute g).pow_left _
  have hx : P.x = P.z := by
    simpa only [← hc.eq, mul_assoc, mul_inv_cancel, mul_one] using hg
  exact P.base_ne_z (2 ^ (n - 1)) (2 ^ (n - 1))
    (by simpa only [P.x_eq_x₂_mul_x₃, x₂, x₃] using hx)

public theorem isConj_r_pow_mul_z (i : ℕ) : IsConj (P.r ^ i * P.z) P.z := by
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨P.s ^ i, ?_⟩
  have hs : SemiconjBy P.z (P.s ^ i) (P.t ^ i) := P.z_mul_s_pow i
  calc
    P.s ^ i * P.z * (P.s ^ i)⁻¹ = P.s ^ i * ((P.t ^ i)⁻¹ * P.z) := by
      rw [mul_assoc, hs.inv_right.eq]
    _ = P.r ^ i * P.z := by
      rw [r, (show Commute P.s P.t from P.commute).inv_right.mul_pow]
      simp only [inv_pow, mul_assoc]

public theorem outer_involution_isConj {g : S} (hg : g ∉ P.U) (hsq : g ^ 2 = 1) :
    IsConj g P.z := by
  obtain ⟨i, rfl⟩ := P.outer_involution_form hg hsq
  exact P.isConj_r_pow_mul_z i

public theorem involution_isConj {g : S} (hg : orderOf g = 2) :
    IsConj g P.x ∨ IsConj g P.x₂ ∨ IsConj g P.z := by
  classical
  have hsq : g ^ 2 = 1 := by rw [← hg, pow_orderOf_eq_one]
  by_cases hU : g ∈ P.U
  · rcases P.base_involution_cases hU hsq with h | h | h | h
    · simp [h] at hg
    · exact Or.inl (h ▸ IsConj.refl _)
    · exact Or.inr (Or.inl (h ▸ IsConj.refl _))
    · right; left
      rw [h]
      apply IsConj.symm
      apply isConj_iff.mpr
      refine ⟨P.z, ?_⟩
      rw [x₂, P.z_mul_s_pow, mul_assoc, mul_inv_cancel, mul_one]; rfl
  · exact Or.inr (Or.inr (P.outer_involution_isConj hU hsq))
/-- The three distinct involution classes specified in ABG II.1 Lemma 2(i). -/

public theorem involution_classes :
    orderOf P.x = 2 ∧ orderOf P.x₂ = 2 ∧ orderOf P.z = 2 ∧
    ¬ IsConj P.x P.x₂ ∧ ¬ IsConj P.x P.z ∧ ¬ IsConj P.x₂ P.z ∧
    ∀ g : S, orderOf g = 2 → IsConj g P.x ∨ IsConj g P.x₂ ∨ IsConj g P.z :=
  ⟨P.x_orderOf, P.x₂_orderOf, P.z_orderOf, P.x_not_isConj_x₂,
    P.x_not_isConj_z, P.x₂_not_isConj_z, fun _ h => P.involution_isConj h⟩
end ABG.Wreathed.Presentation
