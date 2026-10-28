module

public import Theory.GroupTheory.Involution.Dihedral

/-!
# Odd commutators of an isolated involution

This module formalizes the elementary dihedral argument in Lemmas 1–2 of
George Glauberman, *Central elements in core-free groups*, J. Algebra 4
(1966), 403–420, pp. 404–405.  If an involution has no distinct conjugate
commuting with it, its product with every conjugate has odd order; equivalently,
every commutator with it has odd order.

If the product of two distinct involutions had even order, its half-power would
be a central involution in their dihedral subgroup.  Multiplying that
half-power by one reflection produces a conjugate commuting with the
distinguished involution.  The parity of the half exponent determines which
reflection is conjugated, and isolation gives the contradiction.

This is the elementary input to the principal `2`-block proof of Glauberman's
Z-star theorem.  It does not assert that the commutators lie in a common normal
odd-order subgroup; obtaining that global conclusion is the deep part of the
theorem.
-/

namespace Glauberman.ZStar

open BenderSuzuki.PFAppendixIII

universe u

private theorem isInvolution_conjugate
    {G : Type u} [Group G] {t : G} (ht : IsInvolution t) (g : G) :
    IsInvolution (g * t * g⁻¹) := by
  simpa [rightConjugateElem, mul_assoc] using
    (isInvolution_rightConjugateElem (g := g⁻¹) ht)

/-- Product powers conjugate the second reflection to an even reflection. -/
public theorem conjugate_second_by_product_pow
    {G : Type u} [Group G] {u t : G}
    (hu : IsInvolution u) (ht : IsInvolution t) (a : ℕ) :
    (u * t) ^ a * t * ((u * t) ^ a)⁻¹ = (u * t) ^ (2 * a) * t := by
  let w : G := u * t
  have hsem : SemiconjBy t w⁻¹ w := by
    change t * (u * t)⁻¹ = (u * t) * t
    rw [mul_inv_rev, ht.inv_eq_self, hu.inv_eq_self]
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    rw [← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  have hpow := hsem.pow_right a
  change w ^ a * t * (w ^ a)⁻¹ = w ^ (2 * a) * t
  calc
    w ^ a * t * (w ^ a)⁻¹ = w ^ a * (t * (w⁻¹) ^ a) := by
      rw [inv_pow]
      simp only [mul_assoc]
    _ = w ^ a * (w ^ a * t) := by rw [hpow.eq]
    _ = w ^ (a + a) * t := by rw [← mul_assoc, ← pow_add]
    _ = w ^ (2 * a) * t := by
      congr 2
      omega

/-- Product powers conjugate the first reflection to an odd reflection. -/
public theorem conjugate_first_by_product_pow
    {G : Type u} [Group G] {u t : G}
    (hu : IsInvolution u) (ht : IsInvolution t) (a : ℕ) :
    (u * t) ^ a * u * ((u * t) ^ a)⁻¹ = (u * t) ^ (2 * a + 1) * t := by
  let w : G := u * t
  have hu_eq : u = w * t := by
    dsimp [w]
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    rw [mul_assoc, htt, mul_one]
  have hsem : SemiconjBy t w⁻¹ w := by
    change t * (u * t)⁻¹ = (u * t) * t
    rw [mul_inv_rev, ht.inv_eq_self, hu.inv_eq_self]
    have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    rw [← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  have hpow := hsem.pow_right a
  change w ^ a * u * (w ^ a)⁻¹ = w ^ (2 * a + 1) * t
  calc
    w ^ a * u * (w ^ a)⁻¹ = w ^ a * (w * t) * (w⁻¹) ^ a := by
      rw [hu_eq, inv_pow]
    _ = (w ^ a * w) * (t * (w⁻¹) ^ a) := by simp only [mul_assoc]
    _ = (w ^ a * w) * (w ^ a * t) := by rw [hpow.eq]
    _ = w ^ (a + 1 + a) * t := by
      rw [← mul_assoc, ← pow_succ, ← pow_add]
    _ = w ^ (2 * a + 1) * t := by
      congr 2
      omega

/-- If an involution has no distinct conjugate commuting with it, then every
commutator with it has odd order. -/
public theorem orderOf_commutator_odd_of_isolated_involution
    {G : Type u} [Group G] [Finite G] {t : G}
    (ht : IsInvolution t)
    (hisolated : ∀ g : G, Commute (g * t * g⁻¹) t → g * t * g⁻¹ = t)
    (g : G) :
    Odd (orderOf (g * t * g⁻¹ * t⁻¹)) := by
  classical
  let u : G := g * t * g⁻¹
  have hu : IsInvolution u := by
    simpa [u] using isInvolution_conjugate ht g
  have htInv : t⁻¹ = t := ht.inv_eq_self
  suffices Odd (orderOf (u * t)) by
    simpa [u, htInv, mul_assoc] using this
  rw [← Nat.not_even_iff_odd]
  intro heven
  by_cases hut : u = t
  · have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
    have horder : orderOf (u * t) = 1 := by simp [hut, htt]
    rw [horder] at heven
    exact Nat.not_even_one heven
  · rcases heven with ⟨m, hm⟩
    have horder : orderOf (u * t) = 2 * m := by omega
    obtain ⟨hc, _, hct⟩ :=
      BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
        hu ht hut horder
    let c : G := (u * t) ^ m
    let r : G := c * t
    have hc' : IsInvolution c := by simpa [c] using hc
    have hct' : Commute c t := by simpa [c] using hct
    have hrt : Commute r t := by
      rw [commute_iff_eq]
      have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
      dsimp [r]
      calc
        (c * t) * t = c := by rw [mul_assoc, htt, mul_one]
        _ = t * (c * t) := by rw [hct'.eq, ← mul_assoc, htt, one_mul]
    obtain ⟨a, ha | ha⟩ := m.even_or_odd'
    · have hrConj : r = (u * t) ^ a * t * ((u * t) ^ a)⁻¹ := by
        dsimp [r, c]
        rw [ha]
        exact (conjugate_second_by_product_pow hu ht a).symm
      have hrEq : r = t := by
        rw [hrConj]
        exact hisolated ((u * t) ^ a) (by simpa [hrConj] using hrt)
      apply hc'.ne_one
      calc
        c = r * t⁻¹ := by simp [r]
        _ = t * t⁻¹ := by rw [hrEq]
        _ = 1 := mul_inv_cancel t
    · have hrConjU : r = (u * t) ^ a * u * ((u * t) ^ a)⁻¹ := by
        dsimp [r, c]
        rw [ha]
        exact (conjugate_first_by_product_pow hu ht a).symm
      have hrConjT :
          r = ((u * t) ^ a * g) * t * ((u * t) ^ a * g)⁻¹ := by
        rw [hrConjU]
        dsimp [u]
        group
      have hrEq : r = t := by
        rw [hrConjT]
        exact hisolated ((u * t) ^ a * g) (by simpa [hrConjT] using hrt)
      apply hc'.ne_one
      calc
        c = r * t⁻¹ := by simp [r]
        _ = t * t⁻¹ := by rw [hrEq]
        _ = 1 := mul_inv_cancel t

end Glauberman.ZStar
