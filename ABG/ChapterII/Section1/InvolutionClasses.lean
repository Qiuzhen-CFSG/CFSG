module
public import ABG.ChapterII.Section1.Center
public import ABG.ChapterII.Section1.PresentationCalculus

/-!
# The two conjugacy classes of quasi-dihedral involutions

For the actual semidihedral presentation, every involution is conjugate
either to the half-order power of the cyclic generator or to the second,
involutory generator. These representatives are not conjugate: the former
is central and the latter does not commute with the cyclic generator.

The proof applies the bounded normal forms. Among powers of the cyclic
generator, the order-two condition singles out its half-order power. In
the other coset, the square calculation forces an even exponent; the
explicit even-shift conjugation then reduces to the involutory generator.
This proves the involution assertion of ABG Chapter II, §1, Lemma 1(i),
article page 9 of `refs/latex/alperin-brauer-gorenstein.tex`.
-/
namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
/-- A bounded cyclic power of order two has the half-order exponent. -/
public theorem cyclic_involution {n : ℕ} (hn : 4 ≤ n) {a : G}
    (ha : orderOf a = 2 ^ (n - 1)) {i : ℕ} (hi : i < 2 ^ (n - 1))
    (hoi : orderOf (a ^ i) = 2) : i = 2 ^ (n - 2) := by
  have hm : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_comm]
  have hpos : 0 < 2 ^ (n - 2) := by positivity
  have hi0 : i ≠ 0 := by intro he; simp [he] at hoi
  have hd : 2 ^ (n - 1) ∣ i * 2 := by
    rw [← ha, orderOf_dvd_iff_pow_eq_one, pow_mul, ← hoi]
    exact pow_orderOf_eq_one _
  obtain ⟨d, hd⟩ := hd
  rw [hm] at hd hi
  have hdlt : d < 2 := by nlinarith
  have hipos : 0 < i := Nat.pos_of_ne_zero hi0
  have hdpos : 0 < d := by nlinarith
  have : d = 1 := by omega
  simp only [this, mul_one] at hd
  omega

private theorem central_not_conj_b {n : ℕ} (hn : 4 ≤ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hconj : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    ¬ IsConj (a ^ (2 ^ (n - 2))) b := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hcent := half_order_pow_mem_center hn a b ha hb hconj hgen
  have heq : a ^ (2 ^ (n - 2)) = b := by
    simpa only [Subgroup.mem_center_iff.mp hcent g, mul_assoc, mul_inv_cancel, mul_one] using hg
  apply generators_not_commute hn ha hconj
  rw [← heq]
  exact Commute.self_pow _ _

/-- A quasi-dihedral group has exactly two conjugacy classes of involutions. -/
public theorem involution_conjugacy_classes (hG : Stellmacher.IsSemidihedralGroup G) :
    ∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y ∧
      ∀ z : G, orderOf z = 2 → IsConj z x ∨ IsConj z y := by
  obtain ⟨n, a, b, hn, _, ha, hb, hconj, hgen, hforms⟩ := exists_normal_form hG
  refine ⟨a ^ (2 ^ (n - 2)), b, half_order_pow_orderOf hn ha, hb,
    central_not_conj_b hn a b ha hb hconj hgen, ?_⟩
  intro z hz
  obtain ⟨i, hi, rfl | rfl⟩ := hforms z
  · rw [cyclic_involution hn ha hi hz]
    exact Or.inl (IsConj.refl _)
  · have hd : 2 ^ (n - 1) ∣ 2 ^ (n - 2) * i := by
      rw [← ha, orderOf_dvd_iff_pow_eq_one, ← outer_square hn a b hb hconj i, ← hz]
      exact pow_orderOf_eq_one _
    have hm : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    rw [hm] at hd
    have heven : 2 ∣ i := (Nat.mul_dvd_mul_iff_left (by positivity)).mp hd
    obtain ⟨t, rfl⟩ := heven
    exact Or.inr (by simpa using (outer_even_shift_isConj hn a b ha hconj 0 t).symm)
end ABG.QuasiDihedral
