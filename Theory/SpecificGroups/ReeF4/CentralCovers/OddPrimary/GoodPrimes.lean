module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Arithmetic
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.TorusTransfer

/-!
# Good odd primes in the Ree central-cover calculation

We reduce the required local geometry to marked tori in the actual fixed-point
model. The rational and norm-one product embeddings have prime-to-p index
by the exact order formula and the cofactor calculations below. The remaining
prime divisors lie in Φ₄, Φ₆ or Φ₁₂; a product torus covers the first case and
cyclic tori cover the last two. All supplied pair actions remain equations
in the actual model, and the cyclic alternative covers every Sylow subgroup.

These are conditional applications: none of the marked torus embeddings is
constructed here yet. The source theorem remains open until the concrete
embeddings and the remaining nonsplit index calculations are supplied. The
order equality is the independent earlier-source input retained by the parent.
The resulting `GoodPrimeGeometry` is the exact premise of the existing
`GoodPrimeGeometry.not_dvd_kernel` and odd-prime section calculation.

Sources: Aschbacher–Smith I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`; GLS3 §6.1, Example 2.6.3 and §4.10 in
`refs/KGroup/GLS3/chapter6.tex`, `chapter2.tex` and `chapter4.tex`.
The parameter q here is the integer field size, not the half-integer level.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary

/-- The split product embedding has the required Sylow size from the Ree order. -/
theorem goodPrimeGeometry_of_split_embedding {m p : ℕ} [Fact p.Prime]
    (hlarge : 3 < p) (hd : p ∣ 2 ^ (2 * m + 1) - 1)
    (horder : Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 *
      ((2 ^ (2 * m + 1)) ^ 6 + 1) * ((2 ^ (2 * m + 1)) ^ 4 - 1) *
      ((2 ^ (2 * m + 1)) ^ 3 + 1) * (2 ^ (2 * m + 1) - 1))
    (T : ProductTorusEmbedding m (2 ^ (2 * m + 1) - 1)) :
    GoodPrimeGeometry m p := by
  let q := 2 ^ (2 * m + 1)
  have hq : 2 ≤ q := by
    dsimp [q]
    rw [pow_succ]
    have := Nat.one_le_pow (2 * m) 2 (by decide)
    omega
  apply T.goodPrimeGeometry (c := q ^ 12 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 *
    (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)) (by change 0 < q - 1; omega)
  · change Nat.card (Model m) = (q - 1) ^ 2 * _
    change Nat.card (Model m) = q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) *
      (q ^ 3 + 1) * (q - 1) at horder
    rw [horder, order_factorization q (by omega)]
    ring
  · exact not_dvd_split_cofactor (by omega) Fact.out hlarge hd

/-- The norm-one product embedding has the required Sylow size away from three. -/
theorem goodPrimeGeometry_of_normOne_embedding {m p : ℕ} [Fact p.Prime]
    (hlarge : 3 < p) (hd : p ∣ 2 ^ (2 * m + 1) + 1)
    (horder : Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 *
      ((2 ^ (2 * m + 1)) ^ 6 + 1) * ((2 ^ (2 * m + 1)) ^ 4 - 1) *
      ((2 ^ (2 * m + 1)) ^ 3 + 1) * (2 ^ (2 * m + 1) - 1))
    (T : ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)) :
    GoodPrimeGeometry m p := by
  let q := 2 ^ (2 * m + 1)
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by decide)
  apply T.goodPrimeGeometry (c := q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 *
    (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)) (by omega)
  · change Nat.card (Model m) = (q + 1) ^ 2 * _
    change Nat.card (Model m) = q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) *
      (q ^ 3 + 1) * (q - 1) at horder
    rw [horder, order_factorization q hq]
    ring
  · exact not_dvd_normOne_cofactor hq Fact.out hlarge hd

/-- Every prime in the exact order is covered by these concrete torus inputs.
The nonsplit image indices and all embedding witnesses remain explicit. -/
theorem goodPrimeGeometry_of_torus_cases {m p : ℕ} [Fact p.Prime]
    (hlarge : 3 < p) (hd : p ∣ Nat.card (Model m))
    (horder : Nat.card (Model m) = (2 ^ (2 * m + 1)) ^ 12 *
      ((2 ^ (2 * m + 1)) ^ 6 + 1) * ((2 ^ (2 * m + 1)) ^ 4 - 1) *
      ((2 ^ (2 * m + 1)) ^ 3 + 1) * (2 ^ (2 * m + 1) - 1))
    (hsplit : Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) - 1)))
    (hnorm : Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)))
    (hsuzuki : p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 →
      ∃ n, 0 < n ∧ ∃ T : ProductTorusEmbedding m n, ¬ p ∣ T.map.range.index)
    (hcyclic : p ∣ (2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1 ∨
      p ∣ (2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1 →
      ∃ n, 0 < n ∧ ∃ T : CyclicTorusEmbedding m n, ¬ p ∣ T.map.range.index) :
    GoodPrimeGeometry m p := by
  have hfactors := prime_dvd_order_factors (m := m) (Fact.out : p.Prime) hlarge
    (horder ▸ hd)
  rcases hfactors with hsplit' | hnorm' | hsuzuki' | hcyclic' | hcyclic'
  · obtain ⟨T⟩ := hsplit
    exact goodPrimeGeometry_of_split_embedding hlarge hsplit' horder T
  · obtain ⟨T⟩ := hnorm
    exact goodPrimeGeometry_of_normOne_embedding hlarge hnorm' horder T
  · obtain ⟨n, hn, T, hi⟩ := hsuzuki hsuzuki'
    have : NeZero n := ⟨hn.ne'⟩
    exact goodPrimeGeometry_of_cyclic_product T.map T.injective hi T.reverses
  · obtain ⟨n, hn, T, hi⟩ := hcyclic (Or.inl hcyclic')
    have : NeZero n := ⟨hn.ne'⟩
    exact goodPrimeGeometry_of_cyclic_torus T.map T.injective hi
  · obtain ⟨n, hn, T, hi⟩ := hcyclic (Or.inr hcyclic')
    have : NeZero n := ⟨hn.ne'⟩
    exact goodPrimeGeometry_of_cyclic_torus T.map T.injective hi

end ReeF4.CentralCovers.OddPrimary
