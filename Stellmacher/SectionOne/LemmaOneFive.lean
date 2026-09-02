module

public import Stellmacher.SectionsOneToFourDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u

public structure LemmaOneFiveConclusion
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S U : Subgroup G) : Prop where
  part_a :
    subgroupQuotientCard
        (FixedPoints.subgroup U V)
        (FixedPoints.subgroup S V) =
      m (G := G) (V := V) S * (m (G := G) (V := V) U)⁻¹ *
        (indexWithin S U : ℚ)
  part_b :
    IsElementaryAbelian 2 S →
      S = ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧ Nat.card A = 2},
        (A : Subgroup G)
  part_c :
    IsElementaryAbelian 2 S →
      oddCore G =
        ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧
          Nat.card S = 2 * Nat.card A},
          oddCore G ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
  part_d :
    IsElementaryAbelian 2 S → Nat.card S ≥ 4 →
      oddCore G =
        ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧ Nat.card A = 2},
          oddCore G ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
  part_e : IsElementaryAbelian 2 S → m (G := G) (V := V) S ≥ 1

/-- **Stellmacher (1.5).**  The fixed-point quotient formula and, for
elementary abelian `S`, the four generation and lower-bound assertions. -/
public theorem lemma_one_five
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (U : Subgroup G) (hU : U ≤ (S : Subgroup G)) :
    LemmaOneFiveConclusion (G := G) (V := V) (S : Subgroup G) U := by
  sorry

end Stellmacher.SectionOne
