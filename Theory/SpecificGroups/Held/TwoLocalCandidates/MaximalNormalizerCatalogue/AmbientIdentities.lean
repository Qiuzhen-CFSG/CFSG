module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Lower
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.Max5Upper
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankFourKernel
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.AmbientIdentities.RankSixUpper
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.PairBound
public import Theory.GroupTheory.CharacteristicCentralizerFusion

import Mathlib.Tactic.FinCases

/-!
# Ambient identities for the five distinguished Held rows

The lower inclusion for every row is a checked calculation with the literal
candidate generators. Row zero's normalizer is the centralizer of the common
involution. The rank-four normalizers centralize this involution by their
short-orbit kernels, so the first three rows reduce to a single centralizer
upper bound: their conjugated candidates have equal cardinalities because they
are all conjugates of max5. The last two rows have separate sextet-stabilizer
bounds.

The finite certificates in the imported upper-bound modules discharge all
three bounds. Intrinsic candidate normality or maximality is not substituted
for an ambient normalizer calculation, and no ambient Held order is assumed.

Source: Aschbacher–Smith, condition E, printed pp.3–4 and 481–482;
GLS3 Table 5.3p; the literal ATLAS degree-2058 carrier and max3/max4/max5 words.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- The first actual ambient normalizer is an involution centralizer. -/
public theorem normalizer_ambient_zero_eq_centralizer :
    normalizer (ambient 0 : Set He) = centralizer ({centralWord} : Set He) := by
  rw [ambient_zero_eq_zpowers,
    normalizer_zpowers_eq_centralizer_of_order_two _ centralWord_order]

private theorem max5_candidate_eq (k : Fin 5) (hk : k.val < 3) : candidate k = 2 := by
  fin_cases k <;> simp_all [candidate]

private theorem card_conjugate (K : Subgroup He) (g : He) :
    Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card K :=
  card_map_of_injective (K := K) (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective

/-- The three max5 rows and the two elementary-order-64 rows assemble from
three independent ambient bounds. -/
public theorem normalizer_identities_of_ambient_bounds
    (hc : centralizer ({centralWord} : Set He) ≤
      (subgroup (candidate 0)).map (MulAut.conj (conjugator 0)).toMonoidHom)
    (hrankFour : ∀ k : Fin 5, k.val < 3 →
      normalizer (ambient (distinguished k) : Set He) ≤
        centralizer ({centralWord} : Set He))
    (hrankSix : ∀ k : Fin 5, 3 ≤ k.val →
      normalizer (ambient (distinguished k) : Set He) ≤
        (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom) :
    ∀ k : Fin 5, normalizer (ambient (distinguished k) : Set He) =
      (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom := by
  intro k
  by_cases hk : k.val < 3
  · apply Eq.symm
    apply eq_of_le_of_card_ge (conjugated_candidate_le_normalizer k)
    have hle := (hrankFour k hk).trans hc
    have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    simpa only [card_conjugate,
      max5_candidate_eq k hk, max5_candidate_eq 0 (by decide)] using hcard
  · exact le_antisymm (hrankSix k (by omega)) (conjugated_candidate_le_normalizer k)

/-- The five actual ambient normalizers in the degree-2058 Held carrier.

Rows `0`, `9`, and `11` are the common max5 normalizer, while rows `20` and
`21` are the published max4 and max3 conjugates. The proof uses the checked
centralizer, short-orbit-kernel, and sextet certificates from the three
descendant modules together with the unconditional lower inclusions.
-/
public theorem normalizer_identities
    (hp : IsPGroup 2 representative)
    (hgraph : permutationGroup ≤ NormalizerGraph.preservingGroup)
    (_hpair : Nat.card Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups.pairStabilizer ∣
      2 ^ 11 * 3 ^ 2) :
    ∀ k : Fin 5, normalizer (ambient (distinguished k) : Set He) =
      (subgroup (candidate k)).map (MulAut.conj (conjugator k)).toMonoidHom := by
  intro k
  exact normalizer_identities_of_ambient_bounds
    (centralWord_centralizer_le hp)
    rankFour_normalizer_le_centralizer
    (fun k hk => normalizer_le_conjugated_candidate_of_rankSix hp hgraph k hk)
    k

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue
