module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.SourceArithmetic
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Split
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Suzuki
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Cyclotomic
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Order

/-!
# The complete good-prime torus cofactor calculation

The exact Ree order and the nonsplit cofactor identities show that each
prime greater than three lies in a torus with prime-to-p index. Split,
Suzuki and twelfth-cyclotomic torus embeddings are already constructed.
Only the norm-one product and Singer embeddings supplied by the unitary
subsystem are retained as inputs. Every Sylow and cofactor premise is
proved here for the literal model and its actual homomorphisms.

Source: GLS3 §4.10 and Aschbacher–Smith I.1.1–4, pp.407–408.
-/

public section
namespace ReeF4.CentralCovers.OddPrimary
open GoodPrimeArithmetic

private theorem geometry_phi4_pair {m p a b : ℕ} [Fact p.Prime]
    (hlarge : 3 < p) (hd : p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1)
    (ha : 0 < a) (hb : 0 < b)
    (hprod : a * b = (2 ^ (2 * m + 1)) ^ 2 + 1)
    (hsep : ¬ (p ∣ a ∧ p ∣ b))
    (Ta : ProductTorusEmbedding m a) (Tb : ProductTorusEmbedding m b) :
    GoodPrimeGeometry m p := by
  let q := 2 ^ (2 * m + 1)
  let c := q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
    (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by decide)
  have hc : ¬ p ∣ c := not_dvd_phi4_cofactor hq hlarge hd
  have ho : Nat.card (Model m) = (a * b) ^ 2 * c := by
    rw [Order.card_model, order_factorization _ hq, hprod]
    dsimp [q, c]
    ring
  rcases (Fact.out : p.Prime).dvd_mul.mp (hprod ▸ hd) with h | h
  · apply Ta.goodPrimeGeometry ha (c := b ^ 2 * c)
    · rw [ho]; ring
    · exact (Fact.out : p.Prime).not_dvd_mul
        (fun ht => hsep ⟨h, (Fact.out : p.Prime).dvd_of_dvd_pow ht⟩) hc
  · apply Tb.goodPrimeGeometry hb (c := a ^ 2 * c)
    · rw [ho]; ring
    · exact (Fact.out : p.Prime).not_dvd_mul
        (fun ht => hsep ⟨(Fact.out : p.Prime).dvd_of_dvd_pow ht, h⟩) hc

private theorem geometry_phi12_pair {m p a b : ℕ} [Fact p.Prime]
    (hlarge : 3 < p) (hd : p ∣ (2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1)
    (ha : 0 < a) (hb : 0 < b)
    (hprod : a * b = (2 ^ (2 * m + 1)) ^ 4 - (2 ^ (2 * m + 1)) ^ 2 + 1)
    (hsep : ¬ (p ∣ a ∧ p ∣ b))
    (Ta : CyclicTorusEmbedding m a) (Tb : CyclicTorusEmbedding m b) :
    GoodPrimeGeometry m p := by
  let q := 2 ^ (2 * m + 1)
  let c := q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
    (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1)
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by decide)
  have hc : ¬ p ∣ c := not_dvd_phi12_cofactor hq hlarge hd
  have ho : Nat.card (Model m) = (a * b) * c := by
    rw [Order.card_model, order_factorization _ hq, hprod]
    dsimp [q, c]
    ring
  rcases (Fact.out : p.Prime).dvd_mul.mp (hprod ▸ hd) with h | h
  · apply Ta.goodPrimeGeometry ha (c := b * c)
    · rw [ho]; ring
    · exact (Fact.out : p.Prime).not_dvd_mul (fun ht => hsep ⟨h, ht⟩) hc
  · apply Tb.goodPrimeGeometry hb (c := a * c)
    · rw [ho]; ring
    · exact (Fact.out : p.Prime).not_dvd_mul (fun ht => hsep ⟨ht, h⟩) hc

theorem goodPrimeGeometry_of_unitary_tori (m : ℕ) (hm : 1 ≤ m)
    (hnorm : Nonempty (ProductTorusEmbedding m (2 ^ (2 * m + 1) + 1)))
    (hsinger : Nonempty (CyclicTorusEmbedding m
      ((2 ^ (2 * m + 1)) ^ 2 - 2 ^ (2 * m + 1) + 1)))
    {p : ℕ} [Fact p.Prime] (hlarge : 3 < p) (hd : p ∣ Nat.card (Model m)) :
    GoodPrimeGeometry m p := by
  have hf := prime_dvd_order_factors (m := m) (Fact.out : p.Prime) hlarge
    ((Order.card_model m) ▸ hd)
  rcases hf with h | h | h | h | h
  · exact goodPrimeGeometry_of_split_embedding hlarge h (Order.card_model m) (Split.embedding hm)
  · exact goodPrimeGeometry_of_normOne_embedding hlarge h (Order.card_model m) hnorm.some
  · exact geometry_phi4_pair hlarge h (Nat.succ_pos _) (Nat.succ_pos _)
      (suzuki_factorization m) (suzuki_not_both hlarge)
      (exists_suzuki_minus_productTorusEmbedding m hm).some
      (exists_suzuki_plus_productTorusEmbedding m hm).some
  · let q := 2 ^ (2 * m + 1)
    have hq : 1 ≤ q := Nat.one_le_pow _ _ (by decide)
    apply hsinger.some.goodPrimeGeometry (Nat.succ_pos _)
      (c := q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 *
        (q ^ 2 + 1) ^ 2 * (q ^ 4 - q ^ 2 + 1))
    · rw [Order.card_model, order_factorization _ hq]
      dsimp [q]
      ring
    · exact not_dvd_phi6_cofactor hq hlarge h
  · exact geometry_phi12_pair hlarge h (Cyclotomic.minusOrder_pos m)
      (Cyclotomic.plusOrder_pos m) (cyclotomic_factorization m)
      (cyclotomic_not_both hlarge) (Cyclotomic.minus_embedding m hm).some
      (Cyclotomic.plus_embedding m hm).some
end ReeF4.CentralCovers.OddPrimary
