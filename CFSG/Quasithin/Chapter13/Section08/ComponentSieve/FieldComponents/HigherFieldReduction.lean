module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalIndex
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalLayers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.NaturalBranches
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SourceAssembly
public import Theory.Representation.InvertedCubicTensor
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.Representation.BinaryPermutation.FiveTensorQuadratic

/-!
# Higher-field Borel reduction and exceptional outer action

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 13.8.20, printed pp.954–955 (combined manuscript, 1 March 2004).

The residual module constructs the genuine lift of a Borel in K*, proves
its residual transport and records the source quotient-centralizer convention.
The tensor module proves the marked S₅ × S₃ quadratic obstruction.
The external-index module proves the even-degree index-three deduction
under its explicit placement and normalization hypotheses.

Here a seed centralizer bound propagates to U_H = ⟨V₃^H⟩ by normalizing the
commutator preimage. The genuine action-kernel identity then forces a
component into O₂(H), contradicting its nontrivial star image. Also an
external centralizing subgroup of order three consumes one of the two
available independent three-ranks.

`SourceAssembly.source_reduction` now proves alternative (b) after excluding
external X in both source local cases. It constructs the marked inverter,
aligns the actual Borel and component Sylow, and proves Borel centralization
through the full product. The external source family supplies generation,
the natural and moved tensor contradictions, and critical-pair placement.
All seven higher-field models and the same exceptional carriers and outer
actor are retained. The exact earlier source and representation results
remain explicit; the parent owns the subsequent exceptional exclusions.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction
variable {G : Type*} [Group G]

/-- The external cubic subgroup in case (a) leaves at most three-rank one in K*. -/
theorem threeRank_le_one_of_external_cubic [Finite G]
    (H K X : Subgroup G)
    (hc : Nat.card (Source.starImage H X) = 3)
    (hne : ¬ Source.starImage H X ≤ Source.starImage H K)
    (hcent : Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hr : primeRank 3 (Source.Hstar H) ≤ 2) :
    primeRank 3 (Source.starImage H K) ≤ 1 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A := Source.starImage H X
  let B := Source.starImage H K
  change Nat.card A = 3 at hc
  change primeRank 3 B ≤ 1
  have hd : Disjoint A B := by
    have hdvd : Nat.card (A ⊓ B : Subgroup (Source.Hstar H)) ∣ 3 := by
      rw [← hc]
      exact card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have he : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by omega)
      exact (hne (he.symm.le.trans inf_le_right)).elim
  have hpos : 0 < primeRank 3 A := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact PrimeRank.eq_zero_iff_not_dvd_card.mp hz (by rw [show Nat.card A = 3 from hc])
  have hsum := A.primeRank_sup_eq_add_of_disjoint_commuting B hd hcent 3
  have hle := Theory.GroupTheory.primeRank_le_of_injective 3
    (A ⊔ B).subtype (A ⊔ B).subtype_injective
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction

end
