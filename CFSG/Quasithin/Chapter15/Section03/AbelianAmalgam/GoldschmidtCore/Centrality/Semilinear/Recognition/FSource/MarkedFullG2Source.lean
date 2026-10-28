module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.FullG2Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.CompleteReduction

/-!
# F.6.18 from the original marked full binary G₂ amalgam

The complete initial reduction constructs the quasisimple residual unless an
alternative already holds. In the remaining branch the full binary G₂ source
theorem supplies every field, graph action and local extension in row eleven.
Thus the marked source branch requires no residual, component, Sylow-invariant
or local-recognition output premise.

Source: Aschbacher–Smith F.1.12(I)(3), F.6.5 and F.6.18(11), pp.262,305,310.
The original marked-amalgam enumeration and universal A/C source theorems
retain their separate assembly owners.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- The literal row-eleven constructor from the original full G₂ marking. -/
theorem eleven_of_marked_full_g2
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (hM : ChapterF.GreenBook.ExceptionalModels.G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  have hqF : IsQuasisimple (generalizedFitting G) := by
    let : IsQuasisimple (pResidual 2 G) := hq
    exact IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hF)
  have hK : IsComponent G (generalizedFitting G) :=
    ⟨(inferInstance : (generalizedFitting G).Normal).isSubnormal,hqF⟩
  exact eleven_of_full_g2_source (hA _) (hC _) q.sqtk q.equiv.symm hK hF h hM S hS

/-- Only the genuine marked source branch and original A/C hypotheses remain. -/
theorem source_of_marked_full_g2
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hM : ChapterF.GreenBook.ExceptionalModels.G2.IsFullAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  obtain ⟨T,hT,ha⟩ := source_alternative_or_large_quasisimple hA hC q h
  have he : T = S := Sylow.ext (hT.symm.trans hS)
  subst T
  rcases ha with ha | ⟨_,hF,hq⟩
  · exact ha
  · exact Or.inl (Or.inl (Or.inl (eleven_of_marked_full_g2 hA hC q h S hS hF hq hM)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
