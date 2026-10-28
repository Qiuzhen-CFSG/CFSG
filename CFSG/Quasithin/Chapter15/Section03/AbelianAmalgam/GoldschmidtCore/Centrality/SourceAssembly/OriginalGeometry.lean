module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.OriginalGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly.DoubledNatural
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.PreDescentSource
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!+# The terminal contradiction with the original geometry constructed

The earlier local structure and proved descent construct the conjugating
element and all four noncentrality clauses of 15.3.68. The existing source
centrality argument, with B.5 and C.1.37 discharged, then applies to that same
configuration. Thus this terminal consumer requires no supplied terminal
configuration or conjugating element.

The final specializations also construct descent using the proved B.5 source
classification and the fusion setup using the proved 15.3.2(4) dichotomy.
The earlier local data, the actual centralizer and normalizer bounds from
15.3.45(3) and 15.3.49(5), and corrected F.6 classification remain explicit
obligations of the original Chapter 15 assembly.

Source: Aschbacher--Smith, 15.3.68 and final proof of 15.3.1,
printed pp.1154--1155.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
open Semilinear
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual final contradiction with the entire terminal geometry produced
from the earlier local structure and descent. -/
theorem terminal_contradiction_knownSimple_from_original_geometry
    {T : Sylow 2 G} {M Mc P E : Subgroup G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (descent : Descent.Inputs M (residualY M Mc) T (localModule T M) E)
    (fusion : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (classificationF : Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) : False := by
  obtain ⟨s, hs, hsE, c⟩ := exists_terminal_configuration_from_original earlier descent
  exact terminal_contradiction_knownSimple_from_f_source
    earlier descent hs hsE c fusion hG classificationF

/-- Construct both descent and terminal geometry. The only extra earlier local
bound is the original 15.3.49(5) statement for the actual fixed plane. -/
theorem terminal_contradiction_knownSimple_from_normalizer_bound
    {T : Sylow 2 G} {M Mc P E : Subgroup G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (fusion : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))))
    (classificationF : Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) : False :=
  terminal_contradiction_knownSimple_from_original_geometry earlier
    (PreDescentSource.descentInputs earlier hG hZ
      ChapterB.SourceInduction.adequateClassification_knownSimple)
    fusion hG classificationF

/-- The original terminal consumer requires only the two genuine earlier
normalizer/centralizer bounds beyond the earlier local data and corrected F.6. -/
theorem terminal_contradiction_knownSimple_from_original_bounds
    {T : Sylow 2 G} {M Mc P E : Subgroup G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))))
    (classificationF : Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) : False :=
  terminal_contradiction_knownSimple_from_normalizer_bound earlier
    (earlierFusionInputs_of_fixed_centralizer earlier hfixed) hG hZ classificationF

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
