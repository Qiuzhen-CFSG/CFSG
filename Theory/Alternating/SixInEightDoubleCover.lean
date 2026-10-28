module

public import Theory.Alternating.proposition_5_2_4

/-!
# No A₆ subgroup in the Schur double cover of A₈

The central projection is injective on an embedded A₆ because A₆ has trivial
center. In the resulting eight-point action, take the five-cycle `(0 1 2 3 4)`
and the involution `(1 4)(2 3)` inverting it. The image of the five-cycle moves
exactly five points. The involution preserves that odd set, so fixes a point.
A nonidentity even involution on eight points with a fixed point is a double
transposition. Its lifts have nontrivial square, contradicting the square of
the original involution. Thus the argument covers every embedded A₆.

The lift comparison uses the actual Schur central projection, conjugacy inside
the alternating group, and the standard root lift's square calculation.

Sources: GLS3, Theorem 5.2.3 and Proposition 5.2.4(a,b);
Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.23,
printed p.254 (PDF p.265), further-enlargement paragraph.
-/

namespace GLS3.Chapter5.SchurPresentation

open Equiv Equiv.Perm RootFourSubgroup

private theorem fixed_on_five {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.card = 5) (t : Perm α) (ht : t ^ 2 = 1)
    (hst : ∀ x, t x ∈ s ↔ x ∈ s) : ∃ x ∈ s, t x = x := by
  classical
  by_contra h
  push Not at h
  let r : Perm s := t.subtypePerm hst
  have hr : r ^ 2 = 1 := by
    ext x
    exact congrArg (fun p : Perm α => p x.1) ht
  have hsupp : r.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    apply mem_support.mpr
    intro he
    exact h x.1 x.2 (congrArg Subtype.val he)
  have hd := two_dvd_card_support hr
  rw [hsupp, Finset.card_univ, Fintype.card_coe, hs] at hd
  norm_num at hd

/-- An involution inverting a five-cycle preserves its odd support. -/
private theorem inverter_fixed (a t : Perm (Fin 8)) (ha : orderOf a = 5)
    (ht : t ^ 2 = 1) (hconj : t * a * t⁻¹ = a⁻¹) : ∃ x, t x = x := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (ha ▸ Nat.prime_five)
  have hb := a.support.card_le_univ
  have hc : a.support.card = (k + 1) * 5 := by
    rw [← sum_cycleType, hk, ha]
    simp [Nat.add_mul, Nat.add_comm]
  have hk0 : k = 0 := by simp only [Fintype.card_fin] at hb; omega
  have hcard : a.support.card = 5 := by simpa [hk0] using hc
  have hs : a.support.map t.toEmbedding = a.support := by
    have h := congrArg support hconj
    simpa only [support_conj, support_inv] using h
  have hstab (x : Fin 8) : t x ∈ a.support ↔ x ∈ a.support := by
    conv_lhs => rw [← hs]
    simp
  obtain ⟨x, _, hx⟩ := fixed_on_five a.support hcard t ht hstab
  exact ⟨x, hx⟩

private theorem involution_root (t : Perm (Fin 8)) (ht : t ^ 2 = 1)
    (hne : t ≠ 1) (hsign : sign t = 1) (hfix : ∃ x, t x = x) :
    t.cycleType = {2, 2} := by
  obtain ⟨x, hx⟩ := hfix
  have hlt : t.support.card < 8 := by
    have hs : t.support ⊂ Finset.univ := by
      apply Finset.ssubset_univ_iff.mpr
      intro he
      have hm : x ∈ t.support := he ▸ Finset.mem_univ x
      exact mem_support.mp hm hx
    simpa using Finset.card_lt_card hs
  have hct := cycleType_of_pow_prime_eq_one ht
  have hsum : t.support.card = t.cycleType.card * 2 := by
    rw [← sum_cycleType, hct]
    simp
  have hlen : t.cycleType.card < 4 := by omega
  have hs := sign_of_cycleType t
  rw [hct] at hs
  interval_cases h : t.cycleType.card
  · exact (hne (card_cycleType_eq_zero.mp h)).elim
  · norm_num [h] at hs hsign
    have hbad := hsign.symm.trans hs
    norm_num at hbad
  · simpa [h] using hct
  · norm_num [h] at hs hsign
    have hbad := hsign.symm.trans hs
    norm_num at hbad

/-- Compare every root lift with the standard root lift, conjugating in Aₙ. -/
private theorem root_sq_ne_one (n : ℕ) (x : SchurAlternatingGroup n)
    (hx : (schurAlternatingProjection n x).1.cycleType = {2, 2}) : x ^ 2 ≠ 1 := by
  let y : alternatingGroup (Fin (n + 5)) := ⟨rho1 n, rho1_mem_alternating n⟩
  have hy : (schurAlternatingProjection n (u1 n)) = y := by
    apply Subtype.ext
    exact u1_proj n
  have hyct : y.1.cycleType = {2, 2} := by
    apply cycleType_swap_mul_swap_of_nodup
    simp [RootFourSubgroup.p0, RootFourSubgroup.p1,
      RootFourSubgroup.p2, RootFourSubgroup.p3, Fin.ext_iff]
  have hconj : IsConj y (schurAlternatingProjection n x) := by
    apply alternating_involution_isConj_of_card_support_eq
    · simpa [y, pow_two] using rho1_sq n
    · rw [pow_prime_eq_one_iff, hx]
      simp
    · intro h
      simp [h] at hyct
    · rw [← sum_cycleType, ← sum_cycleType, hyct, hx]
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hs := DoubleCoverUniqueness.sq_eq_sq_of_conjugate_images
    (schurAlternatingCovering n) (natCard_ker_schurAlternatingCovering n)
    (x := u1 n) (y := x) (c := c) (by
      change (schurAlternatingProjection n (u1 n)) ^ 2 = 1
      rw [hy]
      apply Subtype.ext
      simpa [y, pow_two] using rho1_sq n) (by
      change c * schurAlternatingProjection n (u1 n) * c⁻¹ =
        schurAlternatingProjection n x
      rwa [hy])
  rw [u1_sq] at hs
  exact fun h => schurAlternatingCentral_ne_one n (hs.trans h)

private def fiveCycle : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, by rw [mem_alternatingGroup]; decide +kernel⟩

private def reverser : alternatingGroup (Fin 6) :=
  ⟨swap 1 4 * swap 2 3, by rw [mem_alternatingGroup]; decide +kernel⟩

private theorem fiveCycle_order : orderOf fiveCycle = 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

private theorem reverser_sq : reverser ^ 2 = 1 := by decide +kernel
private theorem reverser_ne_one : reverser ≠ 1 := by decide +kernel
private theorem reverser_conj : reverser * fiveCycle * reverser⁻¹ = fiveCycle⁻¹ := by
  decide +kernel

private theorem projection_injective (ι : alternatingGroup (Fin 6) →* SchurAlternatingGroup 3)
    (hi : Function.Injective ι) :
    Function.Injective ((schurAlternatingProjection 3).comp ι) := by
  apply ((schurAlternatingProjection 3).comp ι).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  have hker : ι x ∈ (schurAlternatingProjection 3).ker := hx
  have hcentral : ι x ∈ Subgroup.center (SchurAlternatingGroup 3) := by
    rw [schurAlternatingProjection_ker_eq_zpowers] at hker
    exact (Subgroup.zpowers_le.mpr (schurAlternatingCentral_mem_center 3)) hker
  have hxc : x ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hi
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hcentral (ι y)
  rw [alternatingGroup.center_eq_bot (by simp)] at hxc
  exact hxc

/-- The explicit Schur double cover of A₈ contains no subgroup isomorphic to A₆.
The image of the indicated dihedral subgroup of order ten supplies a root
involution for every putative embedding. -/
public theorem not_injective_six_to_schurAlternatingGroup_three (ι : alternatingGroup (Fin 6) →* SchurAlternatingGroup 3) :
    ¬ Function.Injective ι := by
  intro hi
  let f := (schurAlternatingProjection 3).comp ι
  have hf : Function.Injective f := projection_injective ι hi
  let g : alternatingGroup (Fin 6) →* Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp f
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  have ha : orderOf (g fiveCycle) = 5 := (orderOf_injective g hg _).trans fiveCycle_order
  have ht : g reverser ^ 2 = 1 := by rw [← map_pow, reverser_sq, map_one]
  have hne : g reverser ≠ 1 := by
    intro h
    apply reverser_ne_one
    apply hg
    simpa using h
  have hconj : g reverser * g fiveCycle * (g reverser)⁻¹ = (g fiveCycle)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg g reverser_conj
  have hfix := inverter_fixed (g fiveCycle) (g reverser) ha ht hconj
  have hroot := involution_root (g reverser) ht hne (f reverser).2 hfix
  exact root_sq_ne_one 3 (ι reverser) hroot (by rw [← map_pow, reverser_sq, map_one])

end GLS3.Chapter5.SchurPresentation
