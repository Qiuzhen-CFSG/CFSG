module

public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.PairedFive
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# The rank obstruction for an orthogonal sum of two four-spaces

A nontrivial subgroup of a group of order eight leaves a quotient of binary
dimension at most two. In the paired orthogonal module, total isotropy bounds
the other summand of the source rank equation by four. Consequently the rank
sum seven forces the quotient kernel to be trivial.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.8.13(7), printed p.856, using the rank equation in 12.8.11(5).
-/

public section

open Module
open scoped IsMulCommutative
namespace BinaryPermutation.TerminalOrthogonal

lemma quotient_finrank_le_two {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (N : Subgroup A) (hA : Nat.card A = 8) (hN : N ≠ ⊥) :
    finrank (ZMod 2) (Additive (A ⧸ N)) ≤ 2 := by
  have hc := N.card_mul_index
  rw [hA, N.index_eq_card] at hc
  have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (A ⧸ N))
  change Nat.card (A ⧸ N) = _ at hd
  simp only [Nat.card_zmod] at hd
  rw [hd] at hc
  have hn := N.one_lt_card_iff_ne_bot.mpr hN
  have hle : 2 ^ finrank (ZMod 2) (Additive (A ⧸ N)) < 2 ^ 3 := by
    nlinarith [Nat.pow_pos (n := finrank (ZMod 2) (Additive (A ⧸ N))) (show 0 < 2 by decide)]
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hle
  omega

lemma rank_balance_forces_bot {A : Type*} [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (N : Subgroup A) (hA : Nat.card A = 8)
    (E : Submodule (ZMod 2) PairedFive.Space)
    (hE : ∀ v ∈ E, ∀ w ∈ E, PairedFive.form.polarBilin v w = 0)
    (hbalance : finrank (ZMod 2) E + finrank (ZMod 2) (Additive (A ⧸ N)) = 7) :
    N = ⊥ := by
  by_contra hN
  have hq := quotient_finrank_le_two N hA hN
  have he := PairedFive.isotropic_finrank_le E hE
  omega

end BinaryPermutation.TerminalOrthogonal
