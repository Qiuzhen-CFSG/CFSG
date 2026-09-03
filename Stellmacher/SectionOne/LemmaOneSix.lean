module

public import Stellmacher.SectionsOneToFourDefs


open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u

/-! **Stellmacher (1.6).**  The four alternatives are packaged in
`LemmaOneSixConclusion`; all hypotheses from the source are explicit here. -/

public theorem lemma_one_six
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y) :
    LemmaOneSixConclusion (G := G) (V := V) (S : Subgroup G) := by
  sorry

end Stellmacher.SectionOne
