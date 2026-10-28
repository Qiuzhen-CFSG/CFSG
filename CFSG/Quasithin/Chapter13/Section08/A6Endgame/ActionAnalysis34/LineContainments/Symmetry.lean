module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Geometry

/-!
# Exchange of the two line conditions in 13.8.34

The geodesic reversal uses its actual transporter, including the first and
last stabilizer adjustments. It exchanges the two line containments and the
two relative kernel indices. Thus, when both indices are two, a failed line
condition has the required orientation at one of two genuine critical pairs.
No actor or contradictory action is assumed in this reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.8.34(1), printed p.968, and Remark F.9.17, printed p.324.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
open CriticalGeometry CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G : Type*} [Group G] {L T H V : Subgroup G}

/-- The given star rank and the genuine F.9 kernel/comparison hypotheses
give index two at both ends, with the corrected strict inclusion D_H<U_H. -/
theorem indices_of_star_rank_one [Finite G]
    (H U Uγ A Z : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (hγH : Uγ ≤ H) (hrank : rank (Source.starImage H Uγ) = 1)
    (hkernel : Source.Dgamma Uγ U Z = Uγ ⊓ Source.QH H)
    (hproper : Source.DH U Uγ A < U)
    (hcomparison : (Source.DH U Uγ A).relIndex U ≤ (Source.Dgamma Uγ U Z).relIndex Uγ) :
    (Source.Dgamma Uγ U Z).relIndex Uγ = 2 ∧ (Source.DH U Uγ A).relIndex U = 2 := by
  have hn : Source.starImage H Uγ ≠ ⊥ := by
    intro he
    rw [he] at hrank
    norm_num [rank] at hrank
  have he : IsElementaryTwo (Source.starImage H Uγ) :=
    ⟨hn, starImage_isElementaryAbelian H Uγ hγH⟩
  have hc : Nat.card (Source.starImage H Uγ) = 2 := by
    simpa only [hrank, pow_one] using he.card_eq_two_pow_rank
  have hi : (Source.Dgamma Uγ U Z).relIndex Uγ = 2 := by
    rw [hkernel, inf_relIndex_left, ← starImage_card H Uγ hγH, hc]
  exact ⟨hi, corrected_13_8_10_index U Uγ A Z hproper hcomparison hi⟩

/-- Both line conditions are exchanged by the specified graph reversal. -/
theorem reversal_lines (c : CriticalPair L T H V) (r : Reversal c)
    (V₃ Z : Subgroup G) (hZ : H ≤ normalizer (Z : Set G)) :
    (r.pair.Aone Z ≤ Source.UH H V₃ ↔ Z ≤ c.Ugamma V₃) ∧
      (Z ≤ r.pair.Ugamma V₃ ↔ c.Aone Z ≤ Source.UH H V₃) := by
  have hU := le_normalizer_conjugateSpanBy V₃ H
  have hUret := return_map r (Source.UH H V₃) hU
  have hZret := return_map r Z hZ
  have hUend := endpoint_map r (Source.UH H V₃) hU
  have hZend := endpoint_map r Z hZ
  change (c.Ugamma V₃).map _ = Source.UH H V₃ at hUret
  change (c.Aone Z).map _ = Z at hZret
  change r.pair.Ugamma V₃ = _ at hUend
  change r.pair.Aone Z = _ at hZend
  constructor
  · rw [hZend, ← hUret]
    exact map_le_map_iff_of_injective (MulAut.conj (transporter r : G)).injective
  · conv_lhs => rw [hUend, ← hZret]
    exact map_le_map_iff_of_injective (MulAut.conj (transporter r : G)).injective

/-- Reversal preserves the rank-one situation by exchanging the literal
indices, rather than postulating a second rank-one star image. -/
theorem reversal_indices (c : CriticalPair L T H V) (r : Reversal c)
    (V₃ Z : Subgroup G) (hZ : H ≤ normalizer (Z : Set G))
    (hγH : c.Ugamma V₃ ≤ H)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z : Set G)) :
    (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone Z)).relIndex
        (Source.UH H V₃) =
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z).relIndex (c.Ugamma V₃) ∧
    (Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) Z).relIndex (r.pair.Ugamma V₃) =
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).relIndex (Source.UH H V₃) := by
  obtain ⟨hD, hDγ⟩ := denominators r V₃ Z hZ hγH hUA
  have hUret := return_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H)
  have hUend := endpoint_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H)
  change (c.Ugamma V₃).map _ = Source.UH H V₃ at hUret
  change r.pair.Ugamma V₃ = _ at hUend
  constructor
  · rw [hD, ← hUret]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj (transporter r : G)).injective
  · rw [hDγ, hUend]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj (transporter r : G)).injective

/-- A failure of either source line condition is oriented by an actual
reversed critical pair. The two index-two hypotheses are retained. -/
theorem exists_oriented_failure (c : CriticalPair L T H V)
    (V₃ Z : Subgroup G) (hZ : H ≤ normalizer (Z : Set G))
    (hb : 3 ≤ c.path.length) (hV₃ : V₃ ≤ V) (hVH : c.Vgamma ≤ H)
    (hF915 : c.Vgamma ⊓ firstKernel L T H (base L T H true) =
      Source.Egamma c.Vgamma (Source.UH H V₃) Z)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone Z : Set G))
    (hstrict : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z < c.Ugamma V₃)
    (hγ : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z).relIndex (c.Ugamma V₃) = 2)
    (hH : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)).relIndex
      (Source.UH H V₃) = 2)
    (hfail : ¬ (c.Aone Z ≤ Source.UH H V₃ ∧ Z ≤ c.Ugamma V₃)) :
    ∃ d : CriticalPair L T H V,
      (d = c ∨ ∃ r : Reversal c, d = r.pair) ∧
      ¬ d.Aone Z ≤ Source.UH H V₃ ∧
      (Source.Dgamma (d.Ugamma V₃) (Source.UH H V₃) Z).relIndex (d.Ugamma V₃) = 2 ∧
      (Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone Z)).relIndex
        (Source.UH H V₃) = 2 := by
  by_cases hA : c.Aone Z ≤ Source.UH H V₃
  · obtain ⟨r⟩ := exists_reversal_of_strict c V₃ Z hb hV₃ hVH hZ hF915 hstrict
    have hi := reversal_indices c r V₃ Z hZ
      ((map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hVH) hUA
    exact ⟨r.pair, Or.inr ⟨r, rfl⟩,
      fun ha => hfail ⟨hA, (reversal_lines c r V₃ Z hZ).1.mp ha⟩,
      hi.2.trans hH, hi.1.trans hγ⟩
  · exact ⟨c, Or.inl rfl, hA, hγ, hH⟩

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
