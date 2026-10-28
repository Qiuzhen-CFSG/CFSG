module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.OriginalSetup

/-!
# Original core movement in the centralizer partner

Apply the faithful quotient-action consequence of the empty local family
to the actual partner Mc. The original 15.3.48 theorem supplies its intrinsic
span, Frattini and kernel clauses. The resulting nontrivial commutator is
bounded by the order-two central line, so it equals that line.

Source: Aschbacher--Smith, 15.3.49(2), combined manuscript (1 March 2004),
printed p.1142. The parent supplies the original 15.3.45 centralizer bound.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49
open OriginalSetup OriginalSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 15.3.49(2) at the literal centralizer partner, before choosing
an ordinary or extraspecial residual alternative. -/
theorem core_movement_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M) :
    ⁅d.ZS, d.Mc.pCoreIn 2⁆ = d.Z := by
  have hel := partner_eligible hG d hempty hM hu hmany
  have hTH : (d.T : Subgroup G) ≤ d.Mc := le_sup_right.trans hel.1.2
  have h := source_hypothesis hG d hempty hM hu hmany hfixed d.Mc hTH le_rfl hel.2
    (fun _ => centralizer_le_of_eligible d d.Mc hel)
  have h48 := uniform_48 hG d hempty hM hu hmany hfixed d.Mc hel le_rfl
  exact FittingFaithfulness.lemma_15_3_49_2 d.T d.M d.Mc d.ZS
    hTH d.sylow_le hel.2 h.plus_le_H (source_seed_geometry d).2.1.le
    (d.action.card_centralInvolutions d.T d.sylow_le)
    (source_partner_eq hG d hempty hM hu hmany)
    (local_characteristic hG d hu d.Mc hTH le_rfl) hempty
    h48.1 h48.2.1 h48.2.2.1

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49
