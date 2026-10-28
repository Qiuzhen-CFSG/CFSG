module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.ComponentProductSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.NoncyclicSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.EightSingle

/-!
# Source reduction at common Sylow order eight

The component-product case at order eight automatically has an exceptional
vertex, so the proved prime-component source sieve and literal product theorem
apply. Only the actual quasisimple residual case remains for the dihedral model
classification. The noncyclic three-core branch is also discharged from its
source theorem. No general good-good rigidity or assumed model is required.
Source: Aschbacher–Smith, F.6.16–18, printed pp.308–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The original order-eight source triple gives a numbered alternative
or its actual quasisimple two-residual, with every product premise discharged. -/
theorem eight_source_reduction
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G)) (hcard : Nat.card S = 8) :
    (Alternative G₁ G₂ S ∨ Alternative G₂ G₁ S) ∨
      (pResidual 2 G = generalizedFitting G ∧ IsQuasisimple (pResidual 2 G)) := by
  by_cases hc : IsCyclic (pCore 3 G)
  swap
  · exact Or.inl (Or.inl (noncyclic_source q h S hS hc))
  let := q.coverGroup
  let := q.coverFinite
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (ChapterF.twoCore_le_primeToThreeCore.trans
      (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient q.equiv.symm).le)
  have hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 8 := hS ▸ hcard
  rcases ChapterF.SourceAssembly.source_F_6_17_reduction
      (hA _) q.sqtk q.equiv.symm h hc with hq | hd | hd
  · exact Or.inr hq
  · obtain ⟨d⟩ := hd
    exact Or.inl (Or.inl (component_product_of_either_exceptional hA hC q d h S hS
      (Or.inl (d.left_exceptional_of_intersection_eight h hcore hT))))
  · obtain ⟨d⟩ := hd
    exact Or.inl (Or.inr (component_product_of_either_exceptional hA hC q d h.symm S
      ((inf_comm _ _).trans hS) (Or.inl
        (d.left_exceptional_of_intersection_eight h.symm hcore
          (by simpa only [inf_comm] using hT)))))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
