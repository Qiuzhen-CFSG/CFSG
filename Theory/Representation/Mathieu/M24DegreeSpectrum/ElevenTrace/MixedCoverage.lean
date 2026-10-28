module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Remaining
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.CyclicFusion
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.MixedCoverage.Centralizers

/-!
# Native cyclic coverage of the mixed orders 15 and 21 in M₂₄

First conjugate the five- or seven-part into the corresponding marked cyclic
subgroup, using Sylow conjugacy in M₂₄. The conjugated element centralizes
that whole prime subgroup. Within its centralizer, the cubic part can then
be conjugated into the cubic subgroup of the same representative: the
centralizer order is not divisible by nine. This second conjugation preserves
the already aligned prime part. The identities `6 + 10 = 16` and
`15 + 7 = 22` recover the original element from its two powers.

Every element and both conjugators lie in the actual Witt-design carrier.
No odd-order spectrum or conjugacy-class table is assumed. This discharges
`MixedOrderCyclicCoverage`, the mixed-order input to
`odd_square_conjugacy_of_calculations` and
`degreeElevenTraceField_of_odd_order_calculations` in `ElevenTrace`.

Source application: Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, M₂₄ paragraph, manuscript p.17; James, The modular characters
of the Mathieu groups, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Sporadic.Mathieu.M24OddCyclic

open Subgroup

private lemma mixed_cyclic_fusion {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {x y : G}
    (hx : orderOf x = 3 * p) (hy : orderOf y = 3 * p)
    (hp : ¬ p * p ∣ Nat.card G)
    (hc : ¬ 9 ∣ Nat.card (centralizer ({y ^ 3} : Set G)))
    (a b : ℕ) (hab : 3 * a + p * b = 3 * p + 1) :
    ∃ n : ℕ, IsConj x (y ^ n) := by
  classical
  have pp : Nat.Prime p := Fact.out
  have hx3 : orderOf (x ^ 3) = p := by
    rw [orderOf_pow_of_dvd (by decide : 3 ≠ 0) (hx ▸ dvd_mul_right 3 p), hx]
    omega
  have hy3 : orderOf (y ^ 3) = p := by
    rw [orderOf_pow_of_dvd (by decide : 3 ≠ 0) (hy ▸ dvd_mul_right 3 p), hy]
    omega
  obtain ⟨n, hn⟩ := IsConj.of_order_eq_prime_power_generator hy3 hx3 hp
  obtain ⟨d, hd⟩ := isConj_iff.mp hn
  let t := MulAut.conj d x
  have ht : orderOf t = 3 * p := (MulAut.conj d).orderOf_eq x |>.trans hx
  have ht3 : t ^ 3 = (y ^ 3) ^ n := by
    change (d * x * d⁻¹) ^ 3 = _
    simpa only [conj_pow] using hd
  have ht3order : orderOf (t ^ 3) = p := by
    rw [orderOf_pow_of_dvd (by decide : 3 ≠ 0) (ht ▸ dvd_mul_right 3 p), ht]
    omega
  let P := zpowers (y ^ 3)
  let u : P := ⟨t ^ 3, by
    change t ^ 3 ∈ zpowers (y ^ 3)
    rw [ht3]
    exact pow_mem (mem_zpowers _) _⟩
  have hu : u ≠ 1 := by
    intro h
    have h' : t ^ 3 = 1 := congrArg Subtype.val h
    have := ht3order.symm.trans (congrArg orderOf h')
    exact pp.ne_one (by simpa using this)
  have hgen : (⟨y ^ 3, mem_zpowers _⟩ : P) ∈ zpowers u :=
    mem_zpowers_of_prime_card ((Nat.card_zpowers _).trans hy3) hu
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hgen
  have hj' : (t ^ 3) ^ j = y ^ 3 := congrArg Subtype.val hj
  have hcomm : Commute t (y ^ 3) := by
    rw [← hj']
    exact ((Commute.refl t).pow_right 3).zpow_right j
  let C := centralizer ({y ^ 3} : Set G)
  have htC : t ∈ C := mem_centralizer_singleton_iff.mpr hcomm.eq
  let v : C := ⟨y ^ p, mem_centralizer_singleton_iff.mpr
    (((Commute.refl y).pow_left p).pow_right 3).eq⟩
  let w : C := ⟨t ^ p, pow_mem htC p⟩
  have hv : orderOf v = 3 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (y ^ p) = 3
    rw [orderOf_pow_of_dvd pp.ne_zero (hy ▸ dvd_mul_left p 3), hy]
    exact Nat.mul_div_cancel 3 pp.pos
  have hw : orderOf w = 3 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (t ^ p) = 3
    rw [orderOf_pow_of_dvd pp.ne_zero (ht ▸ dvd_mul_left p 3), ht]
    exact Nat.mul_div_cancel 3 pp.pos
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨m, hm⟩ := IsConj.of_order_eq_prime_power_generator hv hw hc
  obtain ⟨c, hc'⟩ := isConj_iff.mp hm
  let z := MulAut.conj (c : G) t
  have hz3 : z ^ 3 = (y ^ 3) ^ n := by
    change ((c : G) * t * (c : G)⁻¹) ^ 3 = _
    rw [conj_pow, ht3]
    exact (Commute.pow_right (mem_centralizer_singleton_iff.mp c.property) n).mul_inv_cancel
  have hzp : z ^ p = (y ^ p) ^ m := by
    change ((c : G) * t * (c : G)⁻¹) ^ p = _
    rw [conj_pow]
    exact congrArg Subtype.val hc'
  have hz : orderOf z = 3 * p := (MulAut.conj (c : G)).orderOf_eq t |>.trans ht
  have hzmem : z ∈ zpowers y := by
    have hpow : z ^ (3 * a + p * b) ∈ zpowers y := by
      rw [pow_add, pow_mul, pow_mul, hz3, hzp]
      exact mul_mem (pow_mem (pow_mem (pow_mem (mem_zpowers y) 3) n) a)
        (pow_mem (pow_mem (pow_mem (mem_zpowers y) p) m) b)
    rwa [hab, ← hz, pow_succ, pow_orderOf_eq_one, one_mul] at hpow
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hzmem)
  refine ⟨k, ?_⟩
  have hxt : IsConj x t := isConj_iff.mpr ⟨d, rfl⟩
  have htz : IsConj t z := isConj_iff.mpr ⟨c, rfl⟩
  exact hk.symm ▸ hxt.trans htz

/-- Every native element of order 15 or 21 is conjugate to a power of the
corresponding marked representative. Both Sylow conjugations are native. -/
theorem mixedOrderCyclicCoverage : MixedOrderCyclicCoverage := by
  intro g hg
  rcases hg with h | h
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨n, hn⟩ := mixed_cyclic_fusion (p := 5) h (representative_order 0)
      (by rw [m24_order]; decide) fivePart_centralizer_not_nine 2 2 (by decide)
    exact ⟨0, n, hn⟩
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨n, hn⟩ := mixed_cyclic_fusion (p := 7) h (representative_order 1)
      (by rw [m24_order]; decide) sevenPart_centralizer_not_nine 5 1 (by decide)
    exact ⟨1, n, hn⟩

end Sporadic.Mathieu.M24OddCyclic
