module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.Original
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly.OriginalGeometry

/-!
# The original fixed-plane normalizer at the terminal contradiction

Apply the original 15.3.49(5) conclusion on the actual LocalData fixed
plane and Sylow subgroup. The parent constructs EarlierData using the
proved ordinary kernel and supplies the genuine earlier amalgam theorem.
Source: Aschbacher--Smith, 15.3.49 and the terminal 15.3 argument.
-/

public section
open Subgroup Theory.GroupTheory CFSG.Quasithin.ChapterA.Section05To06
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The terminal theorem consumes original 15.3.49(5) for the same natural
module, fixed plane and Sylow subgroup. The earlier-data construction can
use `Source49.ordinary_from_original` for its residual-kernel field. -/
theorem terminal_contradiction_knownSimple_from_original_local
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    {E : Subgroup G} (earlier : LocalStructure.EarlierData d.T d.M d.Mc d.V₁ E)
    (classificationF : Semilinear.Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) : False := by
  exact terminal_contradiction_knownSimple_from_original_bounds earlier hG hfixed
    (FusionCore.CosetSetup.Source49.normalizer_three_prime_from_original
      hG d hempty hM hu hmany hfixed) classificationF

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
