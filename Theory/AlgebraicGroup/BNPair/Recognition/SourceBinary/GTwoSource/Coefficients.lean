module
public import Mathlib.Algebra.CharP.Two
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Torus normalization of the two undetermined G₂ coefficients

Fong–Seitz II (1974), (9.16)–(9.21), printed pp.216–217, reduces two
root commutators to functions `f` and `g`. This module proves the scalar
step from their additive and torus identities. It does not construct the
root pinnings or the module identifications that give those identities.

For `f`, polarization at `a + 1` replaces the cube-span argument: it forces
linearity in the first variable, then surjectivity of squaring gives
linearity in the second. This includes the exceptional field of order four.
For `g`, the torus weights determine all nonzero values from `g 1 1`;
the additive defect determines that value only when the field has an
element other than zero and one. The binary source branch remains separate.
-/

@[expose] public section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
variable {K : Type*} [Field K] [CharP K 2]

/-- Biadditivity and a single torus scaling determine the bilinear coefficient,
including fields of orders two and four. -/
theorem f_normalization [Finite K] (f : K → K → K)
    (hfirst : ∀ a a' b, f (a + a') b = f a b + f a' b)
    (hsecond : ∀ a b b', f a (b + b') = f a b + f a b')
    (hscale : ∀ t : Kˣ, ∀ a b,
      f ((t : K) * a) ((t : K)⁻¹ ^ 2 * b) = (t : K)⁻¹ * f a b) :
    ∀ a b, f a b = a * b * f 1 1 := by
  have ht (a b : K) : f 1 (a ^ 2 * b) = a * f a b := by
    by_cases ha : a = 0
    · simp [ha, show f 1 0 = 0 by simpa using (hsecond 1 0 0).symm]
    · have h := hscale (Units.mk0 a ha) 1 (a ^ 2 * b)
      simp only [Units.val_mk0, mul_one] at h
      have he : a⁻¹ ^ 2 * (a ^ 2 * b) = b := by field_simp
      rw [he] at h
      calc
        f 1 (a ^ 2 * b) = a * (a⁻¹ * f 1 (a ^ 2 * b)) := by simp [ha]
        _ = a * f a b := by rw [h]
  have hlin (a b : K) : f a b = a * f 1 b := by
    have h := ht (a + 1) b
    rw [CharTwo.add_sq, one_pow, add_mul, one_mul, hsecond, ht, hfirst] at h
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    linear_combination (norm := (ring_nf; simp [h2])) -h
  intro a b
  obtain ⟨c, hc⟩ := Finite.surjective_of_injective CharTwo.sq_injective b
  change c ^ 2 = b at hc
  have h : f 1 b = b * f 1 1 := by
    rw [← hc, ← mul_one (c ^ 2), ht, hlin]
    ring
  rw [hlin, h]
  ring

omit [CharP K 2] in
/-- The two source torus weights determine the cubic coefficient up to one scalar. -/
theorem g_homogeneous (g : K → K → K)
    (hleft : ∀ b, g 0 b = 0) (hright : ∀ a, g a 0 = 0)
    (hscale : ∀ l m : Kˣ, ∀ a b,
      g ((l : K)⁻¹ ^ 2 * m * a) ((l : K) ^ 3 * (m : K)⁻¹ ^ 2 * b) =
        (m : K)⁻¹ * g a b) :
    ∀ a b, g a b = a ^ 3 * b ^ 2 * g 1 1 := by
  intro a b
  by_cases ha : a = 0
  · simp [ha, hleft]
  by_cases hb : b = 0
  · simp [hb, hright]
  let l : Kˣ := (Units.mk0 a ha)⁻¹ ^ 2 * (Units.mk0 b hb)⁻¹
  let m : Kˣ := (Units.mk0 a ha)⁻¹ ^ 3 * (Units.mk0 b hb)⁻¹ ^ 2
  have hl : (l : K) = a⁻¹ ^ 2 * b⁻¹ := by simp [l]
  have hm : (m : K) = a⁻¹ ^ 3 * b⁻¹ ^ 2 := by simp [m]
  have h := hscale l m 1 1
  rw [hl, hm] at h
  have h1 : (a⁻¹ ^ 2 * b⁻¹)⁻¹ ^ 2 * (a⁻¹ ^ 3 * b⁻¹ ^ 2) * 1 = a := by
    field_simp
  have h2 : (a⁻¹ ^ 2 * b⁻¹) ^ 3 * (a⁻¹ ^ 3 * b⁻¹ ^ 2)⁻¹ ^ 2 * 1 = b := by
    field_simp
  have h3 : (a⁻¹ ^ 3 * b⁻¹ ^ 2)⁻¹ = a ^ 3 * b ^ 2 := by simp [mul_comm]
  rwa [h1, h2, h3] at h

/-- The nonadditive part in (9.17)(ii) forces the remaining scalar to be one.
An element outside the prime field is essential to this argument. -/
theorem g_normalization (g : K → K → K)
    (hright : ∀ a, g a 0 = 0)
    (hscale : ∀ l m : Kˣ, ∀ a b,
      g ((l : K)⁻¹ ^ 2 * m * a) ((l : K) ^ 3 * (m : K)⁻¹ ^ 2 * b) =
        (m : K)⁻¹ * g a b)
    (hadd : ∀ a a' b, g (a + a') b =
      g a b + g a' b + a * a' ^ 2 * b ^ 2 + a' * a ^ 2 * b ^ 2)
    (hw : ∃ w : K, w ≠ 0 ∧ w ≠ 1) :
    ∀ a b, g a b = a ^ 3 * b ^ 2 := by
  have hz (b : K) : g 0 b = 0 := by
    simpa using (hadd 0 0 b).symm
  have hg := g_homogeneous g hz hright hscale
  obtain ⟨w, hw0, hw1⟩ := hw
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have he : w + 1 ≠ 0 := by
    intro h
    have : w = 1 := by simpa [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left h)
    exact hw1 this
  have h := hadd w 1 1
  rw [hg (w + 1) 1, hg w 1] at h
  simp only [one_pow, mul_one, one_mul] at h
  have hc : (w * (w + 1)) * (g 1 1 - 1) = 0 := by
    linear_combination (norm := (ring_nf; simp [h2])) h
  have hn : g 1 1 = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left (mul_ne_zero hw0 he))
  intro a b
  rw [hg, hn, mul_one]
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
/-- A field with at least four elements supplies the scalar needed by (9.21). -/
theorem exists_nonprime_element [Fintype K] (hcard : 4 ≤ Fintype.card K) :
    ∃ w : K, w ≠ 0 ∧ w ≠ 1 := by
  by_contra hnone
  have hcases : ∀ w : K, w = 0 ∨ w = 1 := by
    intro w
    by_cases hw : w = 0
    · exact Or.inl hw
    · right
      by_contra hw1
      exact hnone ⟨w, hw, hw1⟩
  obtain ⟨a, b, c, hab, hac, hbc⟩ :=
    Fintype.two_lt_card_iff.mp (lt_of_lt_of_le (by decide) hcard)
  rcases hcases a with rfl | rfl <;>
    rcases hcases b with rfl | rfl <;>
      rcases hcases c with rfl | rfl <;> simp_all

/-- The coefficient conclusion in (9.21), with the source cardinality premise
made explicit. This is the route used for q ≥ 4; it deliberately does not
claim the binary q = 2 case. -/
theorem g_normalization_of_card [Fintype K] (g : K → K → K)
    (hright : ∀ a, g a 0 = 0)
    (hscale : ∀ l m : Kˣ, ∀ a b,
      g ((l : K)⁻¹ ^ 2 * m * a) ((l : K) ^ 3 * (m : K)⁻¹ ^ 2 * b) =
        (m : K)⁻¹ * g a b)
    (hadd : ∀ a a' b, g (a + a') b =
      g a b + g a' b + a * a' ^ 2 * b ^ 2 + a' * a ^ 2 * b ^ 2)
    (hcard : 4 ≤ Fintype.card K) :
    ∀ a b, g a b = a ^ 3 * b ^ 2 := by
  obtain ⟨w, hw0, hw1⟩ := exists_nonprime_element hcard
  exact g_normalization g hright hscale hadd ⟨w, hw0, hw1⟩
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
