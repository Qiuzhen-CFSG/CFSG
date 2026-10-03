module

public import Mathlib.GroupTheory.Sylow

/-!
# Nonfusion in a Sylow centralizer

If the normalizer of a Sylow subgroup centralizes an element z, every
ambient conjugate of z that centralizes that Sylow subgroup equals z.
This follows from Sylow conjugacy inside element centralizers, as expressed
by Mathlib's normalizer control of fusion in the Sylow centralizer.
-/

open Subgroup

/-- Normalizer control makes z weakly closed in the Sylow centralizer. -/
public theorem Sylow.eq_of_isConj_of_normalizer_le_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (z y : G)
    (hz : z ∈ centralizer (P : Set G))
    (hy : y ∈ centralizer (P : Set G))
    (hN : normalizer (P : Set G) ≤ centralizer ({z} : Set G))
    (hconj : IsConj z y) : y = z := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  have hy' : (g⁻¹)⁻¹ * z * g⁻¹ ∈ centralizer (P : Set G) := by
    simpa only [inv_inv] using hy
  obtain ⟨n, hn, heq⟩ := P.conj_eq_normalizer_conj_of_mem_centralizer z g⁻¹ hz hy'
  have hnz : z * n = n * z := mem_centralizer_iff.mp (hN hn) z (Set.mem_singleton z)
  calc
    _ = n⁻¹ * z * n := by simpa only [inv_inv] using heq
    _ = z := by rw [mul_assoc, hnz, inv_mul_cancel_left]
