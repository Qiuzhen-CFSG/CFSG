module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.LocalModel
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Odd index of the orthogonal subgroup in G₂(p)

An actual map from `(SL₂(p) × SL₂(p)) ⋊ C₂` with diagonal scalar kernel
has image of order `p²(p² − 1)²`. The checked octonion group order therefore
gives index `p⁴(p⁴ + p² + 1)`, which is odd. No centralizer equality or
Sylow classification is needed for this index calculation.

This supplies the transfer hypothesis for the two-primary multiplier
calculation of Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and
GLS III §6.1. Group orders use the licensed ATLAS ports imported above;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open Subgroup

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

/-- The exact diagonal kernel determines the local image order and index. -/
theorem index_of_diagonal_kernel (hF : Nat.card F = p) (hp : 3 < p)
    (φ : C2 →* MulAut (RankOne p × RankOne p))
    (j : (RankOne p × RankOne p) ⋊[φ] C2 →* Model F)
    (hj : ∀ x, j x = 1 ↔ x = 1 ∨ x = SemidirectProduct.inl (-1, -1)) :
    j.range.index = p ^ 4 * (p ^ 4 + p ^ 2 + 1) := by
  let D := (RankOne p × RankOne p) ⋊[φ] C2
  let d : D := SemidirectProduct.inl (-1, -1)
  have hd : j d = 1 := (hj d).mpr (Or.inr rfl)
  have hdn : d ≠ 1 := fun h => rankOne_neg_one_ne_one hp
    (congrArg (fun x : D => x.left.1) h)
  have hk : Nat.card j.ker = 2 := by
    apply (Nat.card_eq_two_iff' (1 : j.ker)).mpr
    refine ⟨⟨d, hd⟩, fun h => hdn (congrArg Subtype.val h), ?_⟩
    intro x hx
    rcases (hj x).mp x.property with h | h
    · exact (hx (Subtype.ext h)).elim
    · exact Subtype.ext h
  have hC2 : Nat.card C2 = 2 := by
    simp [C2, Nat.card_eq_fintype_card]
  have hD : Nat.card D = 2 * (p ^ 2 * (p ^ 2 - 1) ^ 2) := by
    rw [SemidirectProduct.card, Nat.card_prod, Atlas.card_sl_two, hC2]
    simp only [Nat.card_eq_fintype_card, ZMod.card]
    ring
  have hlocal : Nat.card j.range = p ^ 2 * (p ^ 2 - 1) ^ 2 := by
    have he := j.ker.card_mul_index
    rw [index_ker, hk, hD] at he
    omega
  have h2 : 1 ≤ p ^ 2 := by nlinarith
  have hp0 : 0 < p := by omega
  have h6 : 1 ≤ p ^ 6 := by have := pow_pos hp0 6; omega
  have hfactor : p ^ 6 - 1 = (p ^ 2 - 1) * (p ^ 4 + p ^ 2 + 1) := by
    have he2 := Nat.sub_add_cancel h2
    have he6 := Nat.sub_add_cancel h6
    nlinarith [show p ^ 6 = p ^ 2 * p ^ 4 by ring]
  have he := j.range.card_mul_index
  rw [hlocal, card_Model, hF, hfactor] at he
  have hn : 0 < p ^ 2 * (p ^ 2 - 1) ^ 2 := by
    have : 1 < p ^ 2 := by nlinarith
    have : 0 < p ^ 2 - 1 := by omega
    positivity
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    (p ^ 2 * (p ^ 2 - 1) ^ 2) * j.range.index =
      p ^ 6 * ((p ^ 2 - 1) * (p ^ 4 + p ^ 2 + 1)) * (p ^ 2 - 1) := he
    _ = (p ^ 2 * (p ^ 2 - 1) ^ 2) * (p ^ 4 * (p ^ 4 + p ^ 2 + 1)) := by ring

/-- Only the homomorphism and its exact diagonal kernel remain geometric
obligations; the required odd index follows from the actual group orders. -/
theorem odd_index_of_diagonal_kernel (hF : Nat.card F = p) (hp : 3 < p)
    (φ : C2 →* MulAut (RankOne p × RankOne p))
    (j : (RankOne p × RankOne p) ⋊[φ] C2 →* Model F)
    (hj : ∀ x, j x = 1 ↔ x = 1 ∨ x = SemidirectProduct.inl (-1, -1)) :
    Odd j.range.index := by
  rw [index_of_diagonal_kernel hF hp φ j hj]
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have h4 : Odd (p ^ 4) := ho.pow
  have h2 : Odd (p ^ 2) := ho.pow
  exact h4.mul ((h4.add_odd h2).add_odd odd_one)

end Atlas.G2.MultiplierOrdinary.OddTwoPrimary

end
