module

public import Theory.SpecificGroups.Triality.QuadraticTori.OrthogonalRankOne

/-!
# Concrete quadratic tori and odd Sylow geometry in binary triality

For q = 2ⁿ, n > 0, the faithful orthogonal SL₂(q³) × SL₂(q) subsystem
supplies both the split torus of order (q³−1)(q−1) and the nonsplit torus
of order (q³+1)(q+1). The latter consists of actual quadratic-extension
norm-one units. In each case an element of the carrier normalizes the
torus, inverts its first factor, and fixes its second factor.

For a prime p > 3 dividing q²−1, the appropriate torus has index prime to
p. The two cyclic Sylow factors therefore generate an ambient Sylow
subgroup. Independent inversion supplies the `TorusPair` power exponents
(2m−1, 1), where m is the odd order of the first Sylow factor; the existing
coprimality calculation gives the required `Geometry`. All embedding
premises of `RankOneReduction` are discharged here, including at n = 1.

Source: GLS3 §2.6, Proposition 2.6.2(a,b), for the orthogonal subsystem,
`refs/KGroup/GLS3/chapter2.tex`. The resulting quadratic-prime local
calculation is used in the multiplier argument summarized in GLS3 §6.1,
Theorem 6.1.4 and Tables 6.1.2–3, `refs/KGroup/GLS3/chapter6.tex`.
The final `geometry` theorem supplies precisely the quadratic branch of
`PrimeToTwoCovers.center_isTwoGroup_of_prime_branches`; the other prime
branches belong to the central-cover assembly.
-/

public section

namespace Triality.Standard.QuadraticTori

open Subgroup PerfectCentralCovering.OddSylow

private theorem normalizer_of_factor_inversion
    {G C D : Type*} [Group G] [Group C] [Group D]
    (ι : C × D →* G) (w : G)
    (hl : ∀ c, w * ι (c, 1) * w⁻¹ = ι (c⁻¹, 1))
    (hr : ∀ d, w * ι (1, d) * w⁻¹ = ι (1, d)) :
    w ∈ normalizer (ι.range : Set G) ∧
      ∀ c d, w * ι (c, d) * w⁻¹ = ι (c⁻¹, d) := by
  have hconj (c : C) (d : D) : w * ι (c, d) * w⁻¹ = ι (c⁻¹, d) := by
    calc
      (MulAut.conj w) (ι (c, d)) =
          (MulAut.conj w) (ι (c, 1) * ι (1, d)) := by
        rw [← map_mul]
        simp
      _ = (MulAut.conj w) (ι (c, 1)) * (MulAut.conj w) (ι (1, d)) :=
        (MulAut.conj w).map_mul _ _
      _ = ι (c⁻¹, d) := by
        change (w * ι (c, 1) * w⁻¹) * (w * ι (1, d) * w⁻¹) = _
        rw [hl, hr, ← map_mul]
        simp
  refine ⟨?_, hconj⟩
  apply mem_normalizer_iff_conj_image_eq.mpr
  ext x
  constructor
  · rintro ⟨_, ⟨⟨c, d⟩, rfl⟩, rfl⟩
    exact ⟨(c⁻¹, d), (hconj c d).symm⟩
  · rintro ⟨⟨c, d⟩, rfl⟩
    refine ⟨ι (c⁻¹, d), ⟨(c⁻¹, d), rfl⟩, ?_⟩
    simpa only [MulAut.conj_apply, inv_inv] using hconj c⁻¹ d

/-- The split torus and its independent inverter in the actual binary carrier. -/
theorem exists_split_product (n : ℕ) (hn : 0 < n) :
    ∃ (ι : (GaloisField 2 (3 * n))ˣ × (GaloisField 2 n)ˣ →*
        BinaryCarrier n hn) (w : BinaryCarrier n hn),
      Function.Injective ι ∧
      Nat.card ι.range = ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) ∧
      (∀ c, w * ι (c, 1) * w⁻¹ = ι (c⁻¹, 1)) ∧
      (∀ d, w * ι (1, d) * w⁻¹ = ι (1, d)) :=
  exists_split_product_of_rankOneProduct n hn (rankOneProductEmbedding n hn)
    (rankOneProductEmbedding_injective n hn)

/-- A split torus normalizer with its action on every marked torus element. -/
theorem exists_split_normalizer (n : ℕ) (hn : 0 < n) :
    ∃ (ι : (GaloisField 2 (3 * n))ˣ × (GaloisField 2 n)ˣ →*
        BinaryCarrier n hn) (w : BinaryCarrier n hn),
      Function.Injective ι ∧
      Nat.card ι.range = ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) ∧
      w ∈ normalizer (ι.range : Set (BinaryCarrier n hn)) ∧
      ∀ c d, w * ι (c, d) * w⁻¹ = ι (c⁻¹, d) := by
  obtain ⟨ι, w, hi, hc, hl, hr⟩ := exists_split_product n hn
  exact ⟨ι, w, hi, hc, normalizer_of_factor_inversion ι w hl hr⟩

/-- The genuine norm-one torus normalizer, for every positive binary exponent. -/
theorem exists_nonsplit_normalizer (n : ℕ) (hn : 0 < n) :
    ∃ (ι : NonsplitLeft n × NonsplitRight n →* BinaryCarrier n hn)
      (w : BinaryCarrier n hn), Function.Injective ι ∧
      Nat.card ι.range = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧
      w ∈ normalizer (ι.range : Set (BinaryCarrier n hn)) ∧
      ∀ c d, w * ι (c, d) * w⁻¹ = ι (c⁻¹, d) := by
  obtain ⟨ι, w, hi, hc, hl, hr⟩ := exists_nonsplit_product n hn
  exact ⟨ι, w, hi, hc, normalizer_of_factor_inversion ι w hl hr⟩

/-- Actual commuting generators and coprime power conjugation on an ambient
Sylow subgroup, covering both p ∣ q−1 and p ∣ q+1. -/
theorem exists_torusPair (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 1) :
    ∃ Q : Sylow p (BinaryCarrier n hn),
      Nonempty (TorusPair (Q : Subgroup (BinaryCarrier n hn))) :=
  exists_torusPair_of_rankOneProduct n hn (rankOneProductEmbedding n hn)
    (rankOneProductEmbedding_injective n hn) hp hd

/-- The quadratic-prime input to the perfect-central-cover reduction, with
no remaining model, torus, or embedding hypothesis. -/
theorem geometry (n : ℕ) (hn : 0 < n)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 1) :
    Geometry p (BinaryCarrier n hn) := by
  obtain ⟨Q, ⟨d⟩⟩ := exists_torusPair n hn hp hd
  exact Geometry.torus Q d

end Triality.Standard.QuadraticTori
