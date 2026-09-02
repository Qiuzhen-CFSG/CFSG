module

public import Stellmacher.SectionTwo.LemmaTwoThree


namespace Stellmacher.SectionTwo

universe u

/-! **Stellmacher (2.4).**  The two hypotheses are written out explicitly:
`characteristic` says that no nontrivial characteristic subgroup of `S` is
normal in the ambient group, and `unique_maximal` is the asserted uniqueness
of a maximal overgroup of `S`. -/
public theorem lemma_two_four
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic :
      ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
        ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique :
      IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G)) :
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ vSubgroup S := by
  sorry

end Stellmacher.SectionTwo
