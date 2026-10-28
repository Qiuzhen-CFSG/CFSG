module

public import CFSG.Quasithin.Chapter15.SourceMarkedRecognition
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete

/-!
# Original Theorem E applications of the complete marked recognition

Apply the proved F.6 classification to the original final contradiction
in §15.3 and the many-centralizer-overgroups branch in §15.4. The former
retains only its earlier local geometry and bounds. The latter now follows
directly from the original ambient hypotheses.

Source: Aschbacher--Smith F.6.18, the final proof of15.3.1 and §15.4.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15
universe u
variable {G : Type u} [Group G] [Finite G]

namespace Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
open Semilinear

/-- The original terminal contradiction with source F.6 fully discharged. -/
theorem terminal_contradiction_knownSimple_original
    {T : Sylow 2 G} {M Mc P E : Subgroup G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G)))) : False :=
  terminal_contradiction_knownSimple_from_original_bounds earlier hG hfixed hZ
    Recognition.FSource.sourceClassification_knownSimple_complete

end Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly

namespace Section04.InitialSource.KnownSimpleSource
open Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition

/-- The many-centralizer-overgroups branch under its original hypotheses. -/
theorem source_many_theoremE_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hmany : 1 < (maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).ncard) :
    ClassificationModels.IsTheoremEModel G :=
  source_many_theoremE_from_f_source FSource.sourceClassification_knownSimple_complete
    hG T hempty hmany

end Section04.InitialSource.KnownSimpleSource
end CFSG.Quasithin.Chapter15
