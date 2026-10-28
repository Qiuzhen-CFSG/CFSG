module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Cardinality
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.GenericNumerics
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.GenericSL2

/-!
# Generic alternatives in Stellmacher (1.6)

The proved generic numerical dichotomy, quadraticity, omega product and support-one SL2 product give exactly alternatives (c) and (d). The exceptional branch is assembled separately.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- The complete generic branch of Stellmacher (1.6): support size two gives
the omega-product alternative (c), while support size one gives the
`SL₂(2)`-product alternative (d). -/
public theorem generic_rank_one_three_group_alternatives
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : 4 ≤ Nat.card (S : Subgroup G))
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    (hWthree : IsPGroup 3 (oddCore G))
    (hmin : ∀ Y : Subgroup G, Y ≤ (S : Subgroup G) → Y ≠ ⊥ →
      m (G := G) (V := V) (S : Subgroup G) ≤ m (G := G) (V := V) Y)
    (hlocal : RankOneAssemblyLocalHypothesis
      (G := G) (V := V) (S : Subgroup G))
    (hgeneric : RankOneAssemblyGenericHypothesis
      (G := G) (V := V) (S : Subgroup G)) :
    ((∃ F : Finset (Subgroup G),
          (∀ X : Subgroup G, X ∈ F → oneOmega (G := G) (V := V) X) ∧
          IsInternalDirectProduct (oddCore G) F) ∧
        commutatorAction₂ (S : Subgroup G) V = ⊥ ∧
        fixedQuotientCard (G := G) (V := V) (S : Subgroup G)
          (commutatorAction (oddCore G) V) =
            (2 * Nat.card (S : Subgroup G) : ℚ)) ∨
      ((∃ F : Finset (Subgroup G),
          (∀ E : Subgroup G, E ∈ F →
            IsSL2Two (↑E) ∧
              oneOmega (G := G) (V := V)
                ((commutator (↑E)).map E.subtype)) ∧
          IsInternalDirectProduct (oddCore G ⊔ (S : Subgroup G)) F) ∧
        commutatorAction₂ (S : Subgroup G) V = ⊥ ∧
        fixedQuotientCard (G := G) (V := V) (S : Subgroup G)
          (commutatorAction (oddCore G) V) =
            (Nat.card (S : Subgroup G) : ℚ)) := by
  have hnumeric := generic_fixedQuotientCard_eq_card_or_twice
    h S hS hScard hW hWthree hmin hlocal hgeneric
  have hquad := generic_commutatorAction₂_eq_bot
    h S hS hScard hW hWthree hmin hlocal hgeneric
  rcases hnumeric with hfixed | htwice
  · right
    exact ⟨generic_sl2_product_of_fixedQuotientCard_eq_card
      h S hS hScard hW hWthree hmin hlocal hgeneric hfixed,
      hquad, hfixed⟩
  · left
    exact ⟨omega_product_of_all_local_factors_generic
      h S hS hScard hW hWthree hlocal hgeneric,
      hquad, htwice⟩

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
