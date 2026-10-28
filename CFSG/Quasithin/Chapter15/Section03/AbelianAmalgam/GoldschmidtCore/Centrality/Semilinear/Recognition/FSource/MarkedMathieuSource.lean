module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.CompleteReduction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.InnerCase
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.Mathieu.OuterCase

/-!
# Both marked Mathieu families in the complete F source interface

The lower marked-amalgam theorems identify the actual ambient group, component,
Sylow kernel and both local extensions. Their original common Sylow is exactly
the chosen source Sylow, so they construct the unchanged rows twelve and thirteen.
The completed initial reduction also discharges the residual and quasisimple
premises. Only the original A/C, SQTK quotient and marked F.1.12 case remain.

Source: Aschbacher–Smith F.1.12(I)(12–13), F.6.18(12–13), pp.263 and 310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.SourceAssembly.Mathieu
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- Every row-twelve field on the original vertices and chosen common Sylow. -/
theorem twelve_of_marked_mathieu
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (hM : ChapterF.GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  obtain ⟨T,hT,hm,hqF,hSyl,hleft,hright⟩ :=
    source_twelve_of_marked_mathieu (hA _) (hC _) q.sqtk q.equiv.symm h hF hq hM
  have he : T = S := Sylow.ext (hT.symm.trans hS)
  subst T
  exact .twelve hm.some hqF hSyl hleft hright

/-- Every row-thirteen field, including the literal component and nested extension. -/
theorem thirteen_of_marked_aut_mathieu
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (hM : ChapterF.GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  obtain ⟨T,hT,hm,hcomp,hqF,hSyl,hleft,hright⟩ :=
    source_thirteen_of_marked_aut_mathieu (hA _) (hC _) q.sqtk q.equiv.symm h hF hq hM
  have he : T = S := Sylow.ext (hT.symm.trans hS)
  subst T
  exact .thirteen hm.some hcomp.some hqF hSyl hleft hright

/-- The actual inner Mathieu marked case, with the residual reduction discharged. -/
theorem source_of_marked_mathieu
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hM : ChapterF.GreenBook.MathieuTwelve.IsM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  obtain ⟨T,hT,ha⟩ := source_alternative_or_large_quasisimple hA hC q h
  have he : T = S := Sylow.ext (hT.symm.trans hS)
  subst T
  rcases ha with ha | ⟨_,hF,hq⟩
  · exact ha
  · exact Or.inl (Or.inl (Or.inl (twelve_of_marked_mathieu hA hC q h S hS hF hq hM)))

/-- The actual outer Mathieu marked case, with the residual reduction discharged. -/
theorem source_of_marked_aut_mathieu
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hM : ChapterF.GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  obtain ⟨T,hT,ha⟩ := source_alternative_or_large_quasisimple hA hC q h
  have he : T = S := Sylow.ext (hT.symm.trans hS)
  subst T
  rcases ha with ha | ⟨_,hF,hq⟩
  · exact ha
  · exact Or.inl (Or.inl (Or.inl (thirteen_of_marked_aut_mathieu hA hC q h S hS hF hq hM)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
