module

public import Stellmacher.SectionOne.Defs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u v

/-- The four conclusions of Stellmacher's Lemma 1.1.

The suprema in parts (b) and (c) are the generated subgroups denoted by
angle brackets in the source.  Fixed-point subgroups of `W` under
conjugation are written as intersections with ambient centralizers.

Source: `refs/latex/stellmacher-n-group.tex`, lines 270--280. -/
public structure LemmaOneOneConclusion
    (G : Type u) (V : Type v) [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V] (S : Sylow 2 G) : Prop where
  part_a :
    oddCore G =
      ⁅oddCore G, (S : Subgroup G)⁆ ⊔
        (oddCore G ⊓ Subgroup.centralizer (S : Set G))
  part_b :
    ¬ IsCyclic S → IsMulCommutative S →
      oddCore G =
        ⨆ (a : S) (_ : (a : G) ≠ 1),
          oddCore G ⊓
            Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G)
  part_c :
    IsElementaryAbelian 2 S →
      oddCore G =
        ⨆ (S0 : Subgroup S) (_ : Nat.card S = 2 * Nat.card S0),
          oddCore G ⊓
            Subgroup.centralizer
              ((S0.map (S : Subgroup G).subtype : Subgroup G) : Set G)
  part_d : IsQuadraticAction S V → IsElementaryAbelian 2 S

/-- **Stellmacher (1.1).** The standard coprime-action facts used throughout
the paper. -/
public theorem lemma_one_one
    {G : Type u} {V : Type v} [Group G] [Group V]
    [Finite G] [Finite V] [IsElementaryAbelian 2 V]
    [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    LemmaOneOneConclusion G V S := by
  aesop

end Stellmacher.SectionOne
