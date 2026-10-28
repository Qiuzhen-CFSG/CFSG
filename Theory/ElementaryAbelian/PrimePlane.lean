module
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The elementary abelian plane

A finite elementary abelian p-group of order p² is isomorphic to the
product of two copies of the additive group of ZMod p. Its cardinality
computes its dimension, and an equivalence of vector spaces supplies
the group isomorphism. In particular this applies at prime rank two.
-/

namespace IsElementaryAbelian
open scoped IsMulCommutative
variable {p : ℕ} [Fact p.Prime]
variable {G : Type*} [Group G] [Finite G] [IsElementaryAbelian p G]

/-- Recognize the elementary abelian plane by an actual group equivalence. -/
public theorem nonempty_mulEquiv_plane_of_card (hcard : Nat.card G = p ^ 2) :
    Nonempty (G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) := by
  have hc : Nat.card G = p ^ Module.finrank (ZMod p) (Additive G) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive G)
  have hdim : Module.finrank (ZMod p) (Additive G) = 2 :=
    (Nat.pow_right_injective (Fact.out : p.Prime).two_le) (hc.symm.trans hcard)
  let e : Additive G ≃ₗ[ZMod p] (ZMod p × ZMod p) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [hdim, Module.finrank_prod])
  exact ⟨e.toAddEquiv.toMultiplicativeRight.trans (MulEquiv.prodMultiplicative (ZMod p) (ZMod p))⟩

/-- Prime rank two fixes the order of an elementary abelian group. -/
public theorem card_eq_prime_sq_of_primeRank_two (hrank : primeRank p G = 2) :
    Nat.card G = p ^ 2 := by
  have hc : Nat.card G ≤ p ^ 2 := by
    have ht := (primeRank_le_iff_elementary_card_le G).mp hrank.le (⊤ : Subgroup G)
    have htE : IsElementaryAbelian p (⊤ : Subgroup G) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p G) x.val) }
    simpa using ht htE
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p G).exists_card_eq
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hn ▸ hc)
  have hneq : n = 2 := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have hcard1 : Nat.card G ≤ p ^ 1 := by
      rw [hn]
      exact pow_le_pow_right' (Fact.out : p.Prime).one_lt.le hn1
    have := IsElementaryAbelian.primeRank_le_of_card_le G hcard1
    omega
  simpa [hneq] using hn

/-- An elementary abelian group of prime rank two is the concrete plane. -/
public theorem nonempty_mulEquiv_plane_of_primeRank_two (hrank : primeRank p G = 2) :
    Nonempty (G ≃* (Multiplicative (ZMod p) × Multiplicative (ZMod p))) :=
  nonempty_mulEquiv_plane_of_card (card_eq_prime_sq_of_primeRank_two hrank)

end IsElementaryAbelian
