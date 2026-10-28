module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SmallEightSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.ComponentProductSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Complete

/-!
# Complete initial source reduction for F.6.18

The proved F.6.13 normal-subgroup rigidity forces the single-residual component
branch to have an exceptional vertex. Its actual model, cubic complement and
outer actions are therefore the completed product row. The noncyclic and all
small-Sylow branches are already proved. Thus every remaining original source
configuration has common Sylow order greater than eight and quasisimple
O²(G)=F*(G). No rigidity, exceptional-vertex or component-recognition output
is an input to this reduction.
Source: Aschbacher–Smith F.6.13, F.6.16–18, printed pp.307–310.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- The actual product row with its earlier rigidity premise discharged. -/
theorem component_product_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G)
    (d : ChapterF.SourceAssembly.SingleResidualComponent G₁ G₂)
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G)) : Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (ChapterF.twoCore_le_primeToThreeCore.trans
      (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient q.equiv.symm).le)
  exact component_product_of_either_exceptional hA hC q d h S hS
    (Or.inl (d.left_not_characteristic_two h hcore))

/-- Every original source configuration is already a proved alternative or
has a large quasisimple residual. There is no remaining both-good product case. -/
theorem source_alternative_or_large_quasisimple
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂) :
    ∃ S : Sylow 2 G, G₁ ⊓ G₂ = (S : Subgroup G) ∧
      ((SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S) ∨
        (8 < Nat.card S ∧ pResidual 2 G = generalizedFitting G ∧
          IsQuasisimple (pResidual 2 G))) := by
  obtain ⟨S,hS⟩ := h.intersection_sylow
  refine ⟨S,hS,?_⟩
  by_cases hsmall : Nat.card S ≤ 8
  · rcases small_sylow_eight_source hA hC q h S hS hsmall with ha | ha
    · exact Or.inl (Or.inl (Or.inl ha))
    · exact Or.inl (Or.inr (Or.inl ha))
  have hlarge : 8 < Nat.card S := by omega
  by_cases hc : IsCyclic (pCore 3 G)
  swap
  · exact Or.inl (Or.inl (Or.inl (Or.inl (noncyclic_source q h S hS hc))))
  let := q.coverGroup
  let := q.coverFinite
  rcases ChapterF.SourceAssembly.source_F_6_17_reduction
    (hA _) q.sqtk q.equiv.symm h hc with hq | hd | hd
  · exact Or.inr ⟨hlarge,hq⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl
      (component_product_source hA hC q hd.some h S hS))))
  · exact Or.inl (Or.inr (Or.inl (Or.inl
      (component_product_source hA hC q hd.some h.symm S ((inf_comm _ _).trans hS)))))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
