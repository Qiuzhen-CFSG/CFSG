module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.OriginalSetup

/-!
# Original residual centralizer bound

The original factorization of M intersect Mc by the module centralizer
and the Sylow subgroup bounds the two-residual of M intersect H for
every H contained in Mc. This is the literal local input used in the
final rank-one selection.

Source: Aschbacher--Smith, 15.3.49(1), combined manuscript (1 March 2004),
printed p.1142.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49
open OriginalSetup OriginalSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 15.3.49(1) for every subgroup of the centralizer partner. -/
theorem intersection_residual_centralizes_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {H : Subgroup G} (hHMc : H ≤ d.Mc) :
    Stellmacher.twoResidualAmbient (d.M ⊓ H) ≤ centralizer (d.V : Set G) := by
  have hfactor := centralizer_factorization hG d hempty hM hu hmany
  have hMc := source_partner_eq hG d hempty hM hu hmany
  have hf : ∀ x ∈ d.M ⊓ d.Mc,
      ∃ c ∈ d.M ⊓ centralizer (d.V : Set G), ∃ t ∈ (d.T : Subgroup G), c * t = x := by
    simpa only [hMc] using hfactor
  exact (lemma_15_3_49_1 d.M d.Mc H d.V d.T d.action.normalizes
    d.sylow_le hHMc hf).trans inf_le_right

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49
