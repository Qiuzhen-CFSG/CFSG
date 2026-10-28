module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly

/-!
# Original terminal centrality and contradiction with proved B.5

The corrected F.6 alternatives now pass through the rank-one action,
15.3.68(2) centrality and the terminal definite-plane contradiction.
Instantiate the existing B.5 producer on the same actor and module.
The original earlier line structure, I₀ descent, terminal configuration,
enumerated fusion input, corrected F enumeration and doubled-natural
C.1.37 implication remain explicit genuine source prerequisites.

Source: Aschbacher--Smith 15.3.68 and the final proof of 15.3.1,
printed pp.1154--1155.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
open Semilinear
open CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G} {s : G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (descent : Descent.Inputs M (residualY M Mc) T (localModule T M) E)
    (hs : s ∈ planeStabilizer T P) (hsE : s ∉ lineT T E)
    (c : TerminalConfiguration T M (residualY M Mc) (localModule T M)
      E (otherLine E s) earlier.natural)
    (fusion : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (classificationF : Recognition.FSource.SourceClassificationInput.{u} KnownSimple.IsKnownSimple)
    (doubled : PushingUp.DoubledNaturalSource.{u} KnownSimple.IsKnownSimple)

include earlier descent hs hsE c fusion hG classificationF doubled

/-- The original 68(2) two-core centrality with B.5 discharged. -/
theorem core_centralizes_knownSimple :
    twoCoreAmbient (OriginalSource.sourceGroup T M Mc E s) ≤
      centralizer (localModule T M : Set G) :=
  FullSource.core_centralizes_of_source earlier descent hs hsE c fusion hG
    classificationF FFAlternatives.SourceB5.classification.general doubled

/-- The original source terminal consumer with corrected F.6 and proved B.5. -/
theorem terminal_contradiction_knownSimple : False :=
  FullSource.terminal_contradiction_of_source earlier descent hs hsE c fusion hG
    classificationF FFAlternatives.SourceB5.classification.general doubled

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
