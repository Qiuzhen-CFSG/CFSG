module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SmallSylowSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.ComponentProductSource

/-!
# Assembly of the completed initial F.6.18 source branches

The original SQTK quotient supplies the common Sylow and all core hypotheses.
The noncyclic three-core and common Sylow of order at most four already give
literal numbered alternatives. In the remaining cyclic case, the genuine
component reduction gives a quasisimple residual or an oriented component
containing exactly one local residual. If either vertex is exceptional, the
latter case is the fully proved product row, including the actual outer actions.

The remaining output isolates the large quasisimple branch and the both-
characteristic-two single-component branch. These are mathematical reduction
outputs, not assumed classification conclusions. Their source model and
amalgam producers retain the final assembly obligation.
Source: Aschbacher–Smith, F.6.16–18, printed pp.308–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- All completed initial cases, retaining the two genuine large source
branches in the original group and its original local labeling. -/
theorem source_alternative_or_large_cyclic
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂) :
    ∃ S : Sylow 2 G, G₁ ⊓ G₂ = (S : Subgroup G) ∧
      ((Alternative G₁ G₂ S ∨ Alternative G₂ G₁ S) ∨
        IsCyclic (pCore 3 G) ∧ 4 < Nat.card S ∧
          ((pResidual 2 G = generalizedFitting G ∧ IsQuasisimple (pResidual 2 G)) ∨
            (generalizedFitting G₁ = pCore 2 G₁ ∧ generalizedFitting G₂ = pCore 2 G₂ ∧
              (Nonempty (ChapterF.SourceAssembly.SingleResidualComponent G₁ G₂) ∨
                Nonempty (ChapterF.SourceAssembly.SingleResidualComponent G₂ G₁))))) := by
  obtain ⟨S, hS⟩ := h.intersection_sylow
  refine ⟨S, hS, ?_⟩
  by_cases hc : IsCyclic (pCore 3 G)
  swap
  · exact Or.inl (Or.inl (noncyclic_source q h S hS hc))
  by_cases hsmall : Nat.card S ≤ 4
  · exact Or.inl (Or.inl (small_sylow_source hA hC q h S hS hsmall))
  have hlarge : 4 < Nat.card S := by omega
  let := q.coverGroup
  let := q.coverFinite
  rcases ChapterF.SourceAssembly.source_F_6_17_reduction
      (hA _) q.sqtk q.equiv.symm h hc with hq | hd | hd
  · exact Or.inr ⟨hc, hlarge, Or.inl hq⟩
  · by_cases hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨
        generalizedFitting G₂ ≠ pCore 2 G₂
    · obtain ⟨d⟩ := hd
      exact Or.inl (Or.inl (component_product_of_either_exceptional hA hC q d h S hS hbad))
    · have hgood := not_or.mp hbad
      exact Or.inr ⟨hc, hlarge, Or.inr
        ⟨Classical.not_not.mp hgood.1, Classical.not_not.mp hgood.2, Or.inl hd⟩⟩
  · by_cases hbad : generalizedFitting G₂ ≠ pCore 2 G₂ ∨
        generalizedFitting G₁ ≠ pCore 2 G₁
    · obtain ⟨d⟩ := hd
      exact Or.inl (Or.inr (component_product_of_either_exceptional hA hC q d h.symm S
        ((inf_comm _ _).trans hS) hbad))
    · have hgood := not_or.mp hbad
      exact Or.inr ⟨hc, hlarge, Or.inr
        ⟨Classical.not_not.mp hgood.2, Classical.not_not.mp hgood.1, Or.inr hd⟩⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
