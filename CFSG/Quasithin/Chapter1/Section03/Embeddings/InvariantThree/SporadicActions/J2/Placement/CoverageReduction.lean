module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.CarrierBound
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.Representatives
public import Mathlib.GroupTheory.Index

/-!
# Reducing J₂ double-coset coverage to a distinct-coset certificate

A lower bound of 128 on the fixed subgroup and the normal-form upper bound
604800 on the carrier leave at most 4725 cosets. Thus 4725 distinct cosets
exhaust the coset space. If their representatives are left `Seed.s` multiples
of the proposed 72 words, exhaustion supplies the required double-coset cover.
The distinctness and subgroup lower bound remain explicit proof obligations.

Source: the elementary coset-counting argument applied to the retained ATLAS
degree-100 representation; Aschbacher–Smith, printed p.511, GLS3 Table 5.3g.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- The fixed-subgroup lower bound suffices to bound its coset space. -/
theorem card_cosets_le (hs : 128 ≤ Nat.card Seed.s) :
    Nat.card (Carrier ⧸ Seed.s) ≤ 4725 := by
  have hm := Nat.mul_le_mul_right Seed.s.index hs
  rw [Seed.s.card_mul_index] at hm
  have hc := card_carrier_le
  rw [Subgroup.index_eq_card] at hm
  omega

/-- Distinct cosets, with factorizations through the fixed words, certify
exhaustiveness. No exact group order or subgroup normality is required. -/
theorem covers_of_transversal (hs : 128 ≤ Nat.card Seed.s)
    (transversal : Fin 4725 → Carrier)
    (hfactor : ∀ j, ∃ (i : Fin 72) (a : Carrier),
      a ∈ Seed.s ∧ transversal j = a * representative i)
    (hinj : Function.Injective (fun j : Fin 4725 =>
      (QuotientGroup.mk (transversal j) : Carrier ⧸ Seed.s))) : Covers := by
  have hsurj := (hinj.bijective_of_nat_card_le
    (by simpa only [Nat.card_fin] using card_cosets_le hs)).surjective
  intro x
  obtain ⟨j, hj⟩ := hsurj (QuotientGroup.mk x)
  have hb : (transversal j)⁻¹ * x ∈ Seed.s := QuotientGroup.eq.mp hj
  obtain ⟨i, a, ha, hja⟩ := hfactor j
  refine ⟨i, a, (transversal j)⁻¹ * x, ha, hb, ?_⟩
  rw [← hja, mul_inv_cancel_left]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement
