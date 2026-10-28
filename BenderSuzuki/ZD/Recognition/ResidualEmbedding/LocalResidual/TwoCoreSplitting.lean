module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Intersection

/-!
# The order endpoint of the two-core splitting

GLS, Volume 4, Chapter 2, Proposition 17.6 finishes by comparing the
order of the two-core with the square index of the two-point stabilizer.
The inverter first gives trivial intersection. If the core order is a
power of `q` and exceeds `q`, the resulting upper bound `q²` forces
its order to equal the index, proving the actual internal complement.

The construction of `TwoCoreCountingData` (Lemmas 17.1–17.5 and the
inverter consequence of 17.2) and the core-growth premises (the last
paragraph of Proposition 17.6) remain explicit obligations. This module
does not yet assert the splitting from the minimal-counterexample inputs.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly of the genuine product and intersection clauses.
Both numerical core-growth hypotheses must be discharged by the source
argument before claiming Proposition 17.6. -/
public theorem TwoCoreCountingData.isComplement_of_core_growth
    {Z : Set G} {M : Subgroup G} (d : TwoCoreCountingData Z M)
    (h : IsProductDisconnected Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (hlarge : d.q < Nat.card (pCore 2 M))
    (hpower : ∃ k : ℕ, Nat.card (pCore 2 M) = d.q ^ k) :
    (residualPairIn M d.t).IsComplement' (pCore 2 M) := by
  let D := residualPairIn M d.t
  have hdis := d.disjoint_twoCore h hlocal
  have hq := d.one_lt
  have hindex := d.pair_index
  have hbound : Nat.card D * Nat.card (pCore 2 M) ≤ Nat.card M := by
    have hh := Nat.card_le_card_of_injective _ (Subgroup.mul_injective_of_disjoint hdis)
    simpa only [Nat.card_prod] using hh
  have hindexBound : Nat.card (pCore 2 M) ≤ d.q ^ 2 := by
    rw [← D.card_mul_index, hindex] at hbound
    exact Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α := D))
  obtain ⟨k, hk⟩ := hpower
  have hk2 : k ≤ 2 := (pow_le_pow_iff_right₀ hq).mp (hk ▸ hindexBound)
  have hk1 : 1 < k := (pow_lt_pow_iff_right₀ hq).mp (by simpa only [pow_one, ← hk] using hlarge)
  have hcard : Nat.card (pCore 2 M) = D.index := by
    rw [hk, hindex, show k = 2 by omega]
  exact Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hcard]; exact D.card_mul_index) hdis

end BenderSuzuki.ZD
