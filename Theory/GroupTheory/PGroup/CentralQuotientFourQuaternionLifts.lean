module

public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Quaternion lifts from an odd action on a central quotient of order four

Suppose the central quotient of a finite two-group is elementary of order
four, all involutions are central, and an odd-order automorphism fixes the
center pointwise but acts nontrivially on the quotient. Then the group contains
two elements satisfying the quaternion relations.

A moved quotient element and its image are independent. An odd-order action
cannot exchange them, so its next image is their product. For a lift `x`, put
`y = a x` and write `x*y = a(a x)*z` with `z` central. The actor fixes squares,
and the class-two square identity gives `z² = x²*[x,y]`. Correcting both `x`
and `y` by `z⁻¹` makes their squares equal to the commutator. If this square
were trivial, centrality of involutions would contradict the nontrivial
quotient image. The commutator has square one, giving order four and the
quaternion conjugation relation.

Source motivation: A. R. MacWilliams, *On 2-groups with no normal abelian
subgroups of rank 3, and their occurrence as Sylow 2-subgroups of finite
simple groups*, Trans. Amer. Math. Soc. 150 (1970), §3, pp. 366–374;
`refs/original/n-group-global/odd-core-rank-two-source/macwilliams-1970-ams-wayback.pdf`.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

private theorem four_cases {W : Type*} [Group W] [Finite W] [IsKleinFour W]
    {x y : W} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) (w : W) :
    w = x*y ∨ w = x ∨ w = y ∨ w = 1 := by
  classical
  let _ := Fintype.ofFinite W
  have hm : w ∈ ({x*y,x,y,1} : Finset W) :=
    (IsKleinFour.eq_finset_univ hx hy hxy).symm ▸ Finset.mem_univ w
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

private theorem odd_four_product {W : Type*} [Group W] [Finite W] [IsKleinFour W]
    (b : MulAut W) {q : ℕ} (hq : Odd q) (hb : b ^ q = 1)
    (w : W) (hw : b w ≠ w) : w * b w = b (b w) := by
  have hw1 : w ≠ 1 := by rintro rfl; exact hw (map_one b)
  have hbw1 : b w ≠ 1 := by simpa using hw1
  have hbbw1 : b (b w) ≠ 1 := by simpa using hw1
  have hbbw : b (b w) ≠ b w := fun hh => hw (b.injective hh)
  have hww : b (b w) ≠ w := by
    intro hh
    have hb2 : b ^ 2 = 1 := by
      apply MulEquiv.ext
      intro z
      change b (b z) = z
      rcases four_cases hw1 hbw1 hw.symm z with rfl | rfl | rfl | rfl
      · simp only [map_mul, hh]
      · exact hh
      · exact congrArg b hh
      · simp
    obtain ⟨k, hk⟩ := hq
    have hbe : b = 1 := by
      rw [hk, pow_add, pow_mul, hb2, one_pow, pow_one, one_mul] at hb
      exact hb
    exact hw (by rw [hbe]; rfl)
  exact (IsKleinFour.eq_mul_of_ne_all hw1 hbw1 hw.symm hbbw1 hww hbbw).symm


private theorem square_mul {P : Type*} [Group P]
    (hquot : IsElementaryAbelian 2 (P ⧸ center P)) (x y : P) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
  have hc : ⁅x,y⁆ ∈ center P := hquot.commutator_le_center_of_central_quotient
    (commutator_mem_commutator (mem_top x) (mem_top y))
  symm
  calc
    x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := mem_center_iff.mp hc _
    _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by
      rw [mem_center_iff.mp (hquot.sq_mem_center_of_central_quotient x)]
    _ = (x * y) ^ 2 := by simp only [pow_two]; group

namespace IsPGroup

/-- An odd prime-order actor fixing the center and moving the elementary
central quotient of order four supplies quaternion generators. -/
public theorem exists_quaternion_lifts_of_center_quotient_card_four
    {P : Type*} [Group P] [Finite P]
    (_hP : IsPGroup 2 P) (_hnonab : ¬ IsMulCommutative P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcentral : ∀ x : P, x^2 = 1 → x ∈ center P)
    (hfour : Nat.card (P ⧸ center P) = 4)
    (q : ℕ) (_hq : q.Prime) (hodd : Odd q)
    (a : MulAut P) (ha : orderOf a = q)
    (hfix : ∀ z : center P, a z = z)
    (hmove : quotientAut (center P) a ≠ 1) :
    ∃ c d : P, orderOf c = 4 ∧ d^2 = c^2 ∧ d*c*d⁻¹ = c⁻¹ := by
  classical
  let _ := hquot
  let W := P ⧸ center P
  let π := QuotientGroup.mk' (center P)
  let b := quotientAut (center P) a
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (P ⧸ center P)
    omega)
  let : IsKleinFour W := ⟨hfour, IsElementaryAbelian.exponent_eq_prime⟩
  have hb : b ^ q = 1 := by
    change (quotientAut (center P) a) ^ q = 1
    rw [← map_pow, ← ha, pow_orderOf_eq_one, map_one]
  obtain ⟨w, hw⟩ : ∃ w : W, b w ≠ w := by
    by_contra! hh
    exact hmove (MulEquiv.ext hh)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center P) w
  let y := a x
  have hx1 : π x ≠ 1 := by
    intro hx
    apply hw
    change b (π x) = π x
    rw [hx, map_one]
  have hxy : π (x*y) = π (a (a x)) := by
    simpa only [map_mul, quotientAut_apply_mk, b, π, y] using
      odd_four_product b hodd hb (π x) hw
  have hsq (t : P) := hquot.sq_mem_center_of_central_quotient t
  have hsame (t : P) : (a t)^2 = t^2 := by
    rw [← map_pow]
    exact hfix ⟨t^2, hsq t⟩
  let z : center P := ⟨(a (a x))⁻¹ * (x*y), QuotientGroup.eq.mp hxy.symm⟩
  have hprod : a (a x) * (z : P) = x*y := by simp [z]
  have hz2 : (z : P)^2 = x^2 * ⁅x,y⁆ := by
    have he := (show Commute (a (a x)) (z : P) from mem_center_iff.mp z.property _).mul_pow 2
    rw [hprod, hsame, hsame, square_mul hquot, show y^2 = x^2 from hsame x] at he
    exact mul_left_cancel (by simpa only [mul_assoc] using he.symm)
  let k := ⁅x,y⁆
  have hk2 : k^2 = 1 := hquot.commutatorElement_sq_eq_one_of_central_quotient x y
  have hkZ : k ∈ center P := hquot.commutator_le_center_of_central_quotient
    (commutator_mem_commutator (mem_top x) (mem_top y))
  have hki : k⁻¹ = k := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hk2)
  let c := x * (z : P)⁻¹
  let d := y * (z : P)⁻¹
  have hs (t : P) (ht : t^2 = x^2) : (t * (z : P)⁻¹)^2 = k := by
    rw [(show Commute t (z : P)⁻¹ from mem_center_iff.mp ((center P).inv_mem z.property) t).mul_pow,
      ht, inv_pow, hz2, mul_inv_rev]
    change x^2 * (k⁻¹ * (x^2)⁻¹) = k
    rw [hki, ← mul_assoc, mem_center_iff.mp hkZ (x^2), mul_inv_cancel_right]
  have hc2 : c^2 = k := hs x rfl
  have hd2 : d^2 = k := hs y (hsame x)
  have hπc : π c = π x := by
    change π (x * (z : P)⁻¹) = π x
    have hzπ : π (z : P) = 1 := (QuotientGroup.eq_one_iff _).mpr z.property
    rw [map_mul, map_inv, hzπ, inv_one, mul_one]
  have hkne : k ≠ 1 := by
    intro hk
    have hcZ := hcentral c (hc2.trans hk)
    exact hx1 (hπc.symm.trans ((QuotientGroup.eq_one_iff _).mpr hcZ))
  have hc4 : orderOf c = 4 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one, hc2] using hkne
    · simpa only [show 2^(1+1)=2*2 by decide, pow_mul, hc2] using hk2
  have hcomm : ⁅c,d⁆ = k := by
    have hzcomm (t : P) : ⁅(z : P)⁻¹,t⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr
        (mem_center_iff.mp ((center P).inv_mem z.property) t).symm
    have hzcomm' (t : P) : ⁅t,(z : P)⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr
        (mem_center_iff.mp ((center P).inv_mem z.property) t)
    dsimp [c, d]
    rw [commutatorElement_mul_left_eq_conj_mul, hzcomm]
    simp only [mul_one, mul_inv_cancel, one_mul]
    rw [commutatorElement_mul_right_eq_mul_conj, hzcomm']
    simp only [mul_one, mul_inv_cancel_right]
    rfl
  have hcd2 : (c*d)^2 = k := by
    rw [square_mul hquot, hc2, hd2, hcomm, ← pow_two, hk2, one_mul]
  refine ⟨c, d, hc4, hd2.trans hc2.symm, ?_⟩
  have he : (c*d)*(c*d)=d*d := by rw [← pow_two, ← pow_two, hcd2, hd2]
  have he' : c*d*c=d := mul_right_cancel (by simpa only [mul_assoc] using he)
  calc
    d*c*d⁻¹ = c⁻¹*(c*d*c)*d⁻¹ := by group
    _ = c⁻¹ := by rw [he']; group

end IsPGroup
