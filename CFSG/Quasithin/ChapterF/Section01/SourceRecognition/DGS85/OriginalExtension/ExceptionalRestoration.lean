module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoParabolics
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.BinaryExceptional

/-!
# Exceptional restoration with the proper Hall–Janko branch retained

For an actual reduced parabolic comparison, combine the six binary-Borel
restorations with the J₂ core/index argument. Full Aut(J₂) is excluded as
a reduced row. All original models are restored except a proper J₂
enlargement, whose original Sylow and full Borel orders are 256 and 768.
The latter branch still requires the source outer-generator relations to
construct its Aut(J₂) parabolic equivalence. It is not identified by order.

The input is a genuine comparison of three groups. Binary Ree type-only
data is not converted to a parabolic comparison by this theorem. The six
rigid rows retain both commuting squares; J₂ retains parabolic equivalence.

Source: DGS, Groups and Graphs (1985), (15.3), printed pp.228–231;
Aschbacher–Smith F.1.11–12, printed pp.262–264.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open GreenBook GreenBook.ExceptionalModels SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Original exceptional restoration, with precisely the remaining proper
Hall–Janko enlargement separated from the recognized original models. -/
theorem original_exceptional_models_or_j2_outer
    (h : HypothesisF11 L S) {c : Case}
    (he : ParabolicModel c (reducedAmalgam L S) ∨
      ParabolicModel c (reducedAmalgam L S).reverse) :
    (IsModel c (originalAmalgam L S) ∨ IsModel c (originalAmalgam L S).reverse) ∨
      (c = .j2 ∧ Nat.card S = 256 ∧ Nat.card (commonBorel L S) = 768) := by
  by_cases hj : c = .j2
  · subst c
    rcases JankoTwo.original_parabolicModels_or_outer_sizes h he with hr | hs
    · exact Or.inl hr
    · exact Or.inr ⟨rfl, hs⟩
  · by_cases ha : c = .autJ2
    · subst c
      exact False.elim (JankoTwo.not_reduced_autJ2_parabolicModels h he)
    · exact Or.inl (BinaryExceptional.original_models h hj ha he)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
