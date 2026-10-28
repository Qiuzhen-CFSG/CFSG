module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Source
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound

/-!
# The natural lower bound when the source parameter exceeds two

The completed E.6.3 theorem, including its Held-cover input, applies to the
literal chosen module. The proved full-automizer calculation identifies its
local minimum with the source parameter. Thus all central extensions in these
rows satisfy the required lower bound; no hyperplane-stabilizer assumption is
needed. The G₂ parameter is always in this range.

Source: Aschbacher--Smith, 11.2.2, printed p.767, using E.6.3, p.245.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The source's E.6.3 step retains the full original central cover. -/
theorem lower_bound_of_parameter_gt_two (c : Coordinates D S.field)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hm : 2 < naturalParameter D S c) :
    (naturalParameter D S c : ℕ∞) ≤ globalR V := by
  let := D.elementary
  have he := localM_eq_naturalParameter D S c
  have h := FrobeniusReduction.lower_bound_knownSimple hE (he ▸ hm)
  simpa only [he] using h.1

/-- Every hyperplane is controlled in the same range, including those
complementing a nontrivial order-two central kernel. -/
theorem hyperplane_centralizer_of_parameter_gt_two (c : Coordinates D S.field)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hm : 2 < naturalParameter D S c)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hr := lower_bound_of_parameter_gt_two D S c hE hm
  have hsmall : (subgroupCorank V U : ℕ∞) < globalR V := by
    apply lt_of_lt_of_le _ hr
    exact_mod_cast (show subgroupCorank V U < naturalParameter D S c by omega)
  exact (centralizer_le_normalizer_of_corank_lt_globalR hUV hsmall).trans hE.normalizer_le

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
