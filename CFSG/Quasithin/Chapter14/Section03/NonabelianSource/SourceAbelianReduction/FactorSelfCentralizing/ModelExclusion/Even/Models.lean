module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCentralizerNineFree
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Even

/-!
# The intrinsic even-model bound in the marked 14.3.20 exclusion

The family dispatcher proves the published numerical contract using genuine
model equivalences. Substitution in the existing marked-point reduction
removes that obligation from the even exclusion. The compatible faithful
action, quaternion extension and sporadic branch keep their independent
source hypotheses; none is inferred from this numerical calculation.

Source: Aschbacher--Smith 14.3.20, printed p.998, and 1.1.5(3)(a--b).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The full characteristic-two model list satisfies the exact intrinsic
contract used by `MarkedPoint.evenComponent_false_of_centralizer_inputs`. -/
theorem evenModelCentralizerBounds : EvenModelCentralizerBounds.{u} := by
  intro X _ _ _ hm x hx hS h480 hc
  exact ChapterA.Section03.SourceEmbeddings.EvenCentralizerNineFree.not_nine_dvd
    hm x hx hS h480 hc

/-- Applying the numerical theorem to the literal marked component quotient
leaves only its compatible faithful centralizer action to be supplied. -/
theorem evenExclusionSource_of_centralizer_action
    (F : InvariantFlag T V 2) (L : Subgroup G)
    (haction : EvenCentralizerActionSource F L) : EvenExclusionSource F L :=
  evenExclusionSource_of_centralizer_inputs F L evenModelCentralizerBounds haction

/-- The existing model-exclusion consumer with its intrinsic model calculation
discharged; the three independent local-source inputs remain explicit. -/
theorem modelExclusionSource_of_even_centralizer_action
    (F : InvariantFlag T V 2) (L : Subgroup G)
    (hlocal : QuotientCentralizerSource F L)
    (hsporadic : SporadicExclusionSource F L)
    (haction : EvenCentralizerActionSource F L) : ModelExclusionSource F L :=
  modelExclusionSource_of_even_centralizer_inputs F L hlocal hsporadic
    evenModelCentralizerBounds haction

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
