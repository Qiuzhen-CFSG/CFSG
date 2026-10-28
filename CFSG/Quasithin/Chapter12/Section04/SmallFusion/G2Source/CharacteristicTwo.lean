module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.CharacteristicTwoLocal
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplaneCubicAction

/-!
# The characteristic-two case of 12.4.8 for the binary G₂ cover

The actual hyperplane stabilizer supplies a faithful cubic subgroup. The
E.6.7 single-block selection and local C.5.7 index calculation then contradict
the original G₂ hyperplane-normalizer indices 36 and 28. Thus an escaping
hyperplane centralizer cannot have characteristic two; no block-selection,
local-index, or cubic-action premise remains.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815, applying E.6.14,
printed p.251.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource Atlas.G2.Natural ChapterE
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V U : Subgroup G}

/-- The source characteristic-two exclusion on the literal escaping G₂ hyperplane. -/
theorem cover_not_characteristicTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    ¬ HasCharacteristicTwo (centralizer (U : Set G)) :=
  cover_not_characteristicTwo_of_faithful_three h D structural e hne hUV hcor hescape
    (cover_faithful_three h D structural e hne hUV hcor hescape)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
