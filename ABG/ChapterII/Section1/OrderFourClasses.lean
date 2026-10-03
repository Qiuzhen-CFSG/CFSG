module
public import ABG.ChapterII.Section1.PresentationCalculus
public import ABG.ChapterII.Section1.GeneratorNoncommutative
/-!
# The two order-four conjugacy classes in a quasi-dihedral group

For the semidihedral presentation, elements of order four form exactly two
conjugacy classes. With `r = 2^(n-4)`, representatives are `a^(2*r)` and
`a*b`. The bounded cyclic normal form and fourth-power equation leave only
the first representative and its inverse; conjugation by `b` interchanges
them. The square formula forces an outer element of order four to have odd
exponent, and conjugation by even shifts puts it in the second class.

The cyclic-power classification and outer order-four conjugacy are public
interfaces reused by the quaternion subgroup classification.

The classes are distinct because every conjugate of a cyclic power commutes
with `a`, whereas `a*b` does not. This proves the order-four assertion of
ABG Chapter II, §1, Lemma 1(i), article page 9 in
`refs/latex/alperin-brauer-gorenstein.tex`, directly from the presentation
rather than from a classification result. The parameter is Stellmacher's,
one larger than the article's parameter.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
/-- A bounded cyclic power of order four is the quarter-order power or its inverse. -/
public theorem cyclic_order_four_eq_or_inv (a : G) (q i : ℕ) (_hq : 0 < q)
    (ha : orderOf a = 4*q) (hi : i < 4*q) (hi4 : orderOf (a^i) = 4) :
    a ^ i = a ^ q ∨ a ^ i = (a ^ q)⁻¹ := by
  have hd : 4*q ∣ 4*i := by
    rw [← ha, orderOf_dvd_iff_pow_eq_one, mul_comm 4 i, pow_mul, ← hi4]
    exact pow_orderOf_eq_one _
  have hqi : q ∣ i := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 4)).mp hd
  obtain ⟨j, rfl⟩ := hqi
  have hj : j < 4 := by nlinarith
  interval_cases j
  · simp at hi4
  · exact Or.inl (by simp)
  · have hsq : (a^(q*2))^2 = 1 := by
      rw [← pow_mul, show q*2*2 = 4*q by omega, ← ha, pow_orderOf_eq_one]
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [hi4] at hd
    norm_num at hd
  · right
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, show q*3 + q = 4*q by omega, ← ha, pow_orderOf_eq_one]

private theorem cyclic_four_order (a : G) (q : ℕ) (hq : 0 < q)
    (ha : orderOf a = 4*q) : orderOf (a^q) = 4 := by
  rw [orderOf_pow_of_dvd (by omega) (by rw [ha]; exact dvd_mul_left q 4), ha]
  exact Nat.mul_div_cancel _ hq

private theorem cyclic_four_conj (a b : G) (r : ℕ) (hr : 0 < r)
    (ha : orderOf a = 8*r) (hconj : b*a*b⁻¹ = a^(4*r-1)) :
    IsConj (a^(2*r)) (a^(2*r))⁻¹ := by
  have hc : b * a^(2*r) * b⁻¹ = (a^(2*r))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have hh := congrArg (fun x : G => x ^ (2*r)) hconj
    rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply, ← pow_mul] at hh
    rw [hh, ← pow_add]
    have he : (4*r-1)*(2*r) + 2*r = (8*r)*r := by
      have ht : 4*r-1+1 = 4*r := by omega
      nlinarith
    rw [he, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
  exact isConj_iff.mpr ⟨b, hc⟩
private theorem cyclic_outer_not_conj (a b : G) (k q : ℕ)
    (hnc : ¬ Commute a b) (hconj : b*a*b⁻¹ = a^k)
    (hnf : ∀ x : G, ∃ i : ℕ, x = a^i ∨ x = a^i*b) :
    ¬ IsConj (a^q) (a*b) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨i, rfl | rfl⟩ := hnf c
  · have hh : a^i * a^q * (a^i)⁻¹ = a^q := by
      rw [← pow_add, Nat.add_comm, pow_add, mul_assoc, mul_inv_cancel, mul_one]
    rw [hh] at hc
    have ht : Commute a (a*b) := hc ▸ Commute.self_pow a q
    apply hnc
    apply mul_left_cancel (a := a)
    simpa only [mul_assoc] using ht.eq
  · have hh : (a^i*b) * a^q * (a^i*b)⁻¹ = a^(k*q) := by
      have hbq := congrArg (fun x : G => x^q) hconj
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply, ← pow_mul] at hbq
      calc
        (a^i*b) * a^q * (a^i*b)⁻¹ = a^i * (b*a^q*b⁻¹) * (a^i)⁻¹ := by group
        _ = a^i * a^(k*q) * (a^i)⁻¹ := by rw [hbq]
        _ = a^(k*q) := by
          rw [← pow_add, Nat.add_comm, pow_add, mul_assoc, mul_inv_cancel, mul_one]
    rw [hh] at hc
    have ht : Commute a (a*b) := hc ▸ Commute.self_pow a (k*q)
    apply hnc
    apply mul_left_cancel (a := a)
    simpa only [mul_assoc] using ht.eq
private theorem outer_four_order (a b : G) (H : ℕ) (hH : 0 < H)
    (ha : orderOf a = 2*H) (hs : (a*b)^2 = a^H) :
    orderOf (a*b) = 4 := by
  have hn : (a*b)^2 ≠ 1 := by
    rw [hs]
    exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hf : (a*b)^4 = 1 := by
    rw [show (4:ℕ) = 2*2 by rfl, pow_mul, hs, ← pow_mul,
      Nat.mul_comm H 2, ← ha, pow_orderOf_eq_one]
  exact @orderOf_eq_prime_pow G _ (a*b) 1 2 ⟨Nat.prime_two⟩ hn hf

/-- Every outer element of order four is conjugate to the first outer odd power. -/
public theorem outer_order_four_isConj (a b : G) (H i : ℕ)
    (ha : orderOf a = 2*H) (hs : ∀ i : ℕ, (a^i*b)^2 = a^(H*i))
    (hc : ∀ j t : ℕ, IsConj (a^j*b) (a^(j+2*t)*b))
    (hi : orderOf (a^i*b) = 4) : IsConj (a^i*b) (a*b) := by
  have hi2 : i % 2 = 1 := by
    by_contra hn
    have heven : i % 2 = 0 := by omega
    have hsq : (a^i*b)^2 = 1 := by
      rw [hs, show H*i = (2*H)*(i/2) by
        have he : i = 2*(i/2) := by omega
        calc
          H*i = H*(2*(i/2)) := congrArg (H * ·) he
          _ = (2*H)*(i/2) := by ring, pow_mul, ← ha, pow_orderOf_eq_one, one_pow]
    have hd := orderOf_dvd_of_pow_eq_one hsq
    rw [hi] at hd
    norm_num at hd
  have heq : i = 1 + 2*(i/2) := by omega
  simpa only [pow_one, ← heq] using (hc 1 (i/2)).symm

/-- A quasi-dihedral group has exactly two conjugacy classes of elements of order four. -/
public theorem order_four_conjugacy_classes (hS : Stellmacher.IsSemidihedralGroup G) :
    ∃ x y : G, orderOf x = 4 ∧ orderOf y = 4 ∧ ¬ IsConj x y ∧
      ∀ z : G, orderOf z = 4 → IsConj z x ∨ IsConj z y := by
  obtain ⟨n, a, b, hn, _, ha, hb, hab, _, hnf⟩ := exists_normal_form hS
  let r := 2^(n-4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hm : 2^(n-1) = 8*r := by
    dsimp [r]
    rw [show n-1 = n-4+3 by omega, pow_add]
    ring
  have hh : 2^(n-2) = 4*r := by
    dsimp [r]
    rw [show n-2 = n-4+2 by omega, pow_add]
    ring
  have ha' : orderOf a = 4*(2*r) := by rw [ha, hm]; ring
  have hb4 : orderOf (a*b) = 4 := by
    apply outer_four_order a b (2^(n-2)) (by positivity)
    · rw [ha, hm, hh]; ring
    · simpa only [pow_one, mul_one] using outer_square hn a b hb hab 1
  refine ⟨a^(2*r), a*b, cyclic_four_order a (2*r) (by omega) ha', hb4, ?_, ?_⟩
  · apply cyclic_outer_not_conj a b (2^(n-2)-1) (2*r)
      (generators_not_commute hn ha hab) hab
    intro x
    obtain ⟨i, _, hi⟩ := hnf x
    exact ⟨i, hi⟩
  · intro z hz
    obtain ⟨i, hi, rfl | rfl⟩ := hnf z
    · left
      have hi' : i < 4*(2*r) := by rw [hm] at hi; omega
      rcases cyclic_order_four_eq_or_inv a (2*r) i (by omega) ha' hi' hz with he | he
      · rw [he]
      · rw [he]
        exact (cyclic_four_conj a b r hr (ha.trans hm) (by simpa only [hh] using hab)).symm
    · right
      exact outer_order_four_isConj a b (2^(n-2)) i (by rw [ha, hm, hh]; ring)
        (outer_square hn a b hb hab) (outer_even_shift_isConj hn a b ha hab) hz
end ABG.QuasiDihedral
