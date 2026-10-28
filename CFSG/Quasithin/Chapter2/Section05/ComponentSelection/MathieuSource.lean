module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MathieuTwentyTwoSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MathieuTwentyThreeSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.BinaryAmbient.Escape
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.QuarticSylowSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions

/-! All original sporadic component alternatives under empty Gamma-even.
The M22 center is exhausted by the actual trivial, binary and quartic
kernel cases. The original M23 intersection is excluded by its invariant
local subgroup. The earlier concrete block calculations exclude the other
sporadics, leaving the literal M11 component with its two-kernel eliminated.
Source: Aschbacher--Smith 2.3.9(7)(f), 2.5.2, pp.525--526,551. -/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem mathieu_twentyTwo_quotient_false {C : GroupClass}
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (d : SporadicQuotientInput L z .m22) : False := by
  let h := c.localSetup hG structural115Input sourceC
  rcases h.mathieuTwentyTwo_core_card_cases d.quotientIso with hk | hk | hk
  · exact mathieu_twentyTwo_quotient_false_of_core_eq_bot c hG sourceC hempty d hk
  · exact BinaryAmbient.source_false c hG sourceC hempty d hk
  · exact h.mathieuTwentyTwo_quartic_false d hk

theorem sporadic_model_of_emptyGamma {C : GroupClass}
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    {name : ClassificationModels.SporadicName} (hn : name ≠ .j3)
    (d : SporadicQuotientInput L z name) : Nonempty (L ≃* Sporadic.Mathieu.M11) := by
  rcases (c.localSetup hG structural115Input sourceC).sporadic_name_cases d hn with rfl | rfl | rfl
  · obtain ⟨_,e,_⟩ := c.mathieuEleven_intersection hG structural115Input sourceC d
    exact ⟨e⟩
  · exact (mathieu_twentyTwo_quotient_false c hG sourceC hempty d).elim
  · exact (mathieu_twentyThree_quotient_false c hG sourceC hempty d).elim

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
