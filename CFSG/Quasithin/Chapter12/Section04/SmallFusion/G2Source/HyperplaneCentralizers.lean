module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Components.Exclusion
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.CharacteristicTwo
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.OddCore.Layer
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.Parameters
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter

/-!
# The binary G₂ ambient hyperplane-centralizer assembly

The actual escaping hyperplane centralizer cannot have characteristic two.
The uniform ordinary-component exclusion and the proved odd-core argument
make its odd core trivial. The generalized Fitting centralizer bound then
forces characteristic two, a contradiction. The same literal hyperplanes
supply the global-rank parameter needed by the fixed-module endgame.

The final source theorem discharges all three branches on the original chosen module.
Source: Aschbacher--Smith, Lemma 12.4.8, printed pp.815--816.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterE ChapterB.QuasisimpleSource Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The source ambient inclusion after the independent ordinary-component branch. -/
theorem cover_hyperplane_centralizers_of_no_components
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (components : OddCore.ComponentsExcluded V)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  by_contra hescape
  have hnc := components U hUV hcor hescape
  have ho := OddCore.oddCore_eq_bot h D structural e hne hUV hcor hescape components
  apply cover_not_characteristicTwo h D structural e hne hUV hcor hescape
  let H := centralizer (U : Set G)
  have hnc' : ∀ J : Subgroup H, ¬ IsComponent H J := by
    intro J hJ
    apply hnc (J.map H.subtype)
    refine ⟨map_subtype_le J, ?_⟩
    have he : (J.map H.subtype).subgroupOf H = J :=
      comap_map_eq_self_of_injective H.subtype_injective J
    rwa [he]
  have hh := centralizer_core_product_le_of_no_components 2 hnc'
  change pPrimeCore 2 H = ⊥ at ho
  simpa only [HasCharacteristicTwo, ho, sup_bot_eq] using hh

/-- The literal numerical parameter input of the G₂ fixed-module endgame. -/
theorem globalS_gt_one_of_no_components
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (components : OddCore.ComponentsExcluded V) : letI := D.elementary; 1 < globalS V := by
  exact globalS_gt_one_of_hyperplanes h D structural e hne
    (fun _ hUV hcor => cover_hyperplane_centralizers_of_no_components
      h D structural e hne components hUV hcor)

/-- Original 12.4.8: every ambient hyperplane centralizer normalizes the
chosen seven-dimensional cover. All three source branches are discharged. -/
theorem cover_hyperplane_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ normalizer (V : Set G) :=
  cover_hyperplane_centralizers_of_no_components h D structural e hne
    (Components.cover_components_excluded h D structural e hne) hUV hcor

/-- The numerical G₂ parameter bound with original source hypotheses only. -/
theorem globalS_gt_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥) : letI := D.elementary; 1 < globalS V :=
  globalS_gt_one_of_no_components h D structural e hne
    (Components.cover_components_excluded h D structural e hne)


end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
