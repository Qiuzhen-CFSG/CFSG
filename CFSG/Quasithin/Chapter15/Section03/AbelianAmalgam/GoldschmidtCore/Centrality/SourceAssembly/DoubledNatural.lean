module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly.KnownSimple
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp.Source

/-!
# Original terminal source with C.1.37 discharged

The proved doubled-natural C.1.37 specialization supplies the character
kernel's pushing-up control. Together with the proved B.5 source input,
this completes the original 68(2) centrality and final definite-plane
contradiction from the original earlier geometry, descent and fusion data
and the corrected F.6 source classification. No doubled-natural source
implication or terminal SQTK premise remains in this consumer.

Source: Aschbacher--Smith, 15.3.68(2) and final proof of 15.3.1,
printed pp.1154--1155.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
open Semilinear
open CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
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

include earlier descent hs hsE c fusion hG classificationF

/-- Original 68(2) centrality with the B.5 and doubled-natural C.1.37
source inputs discharged on the same groups and actions. -/
theorem core_centralizes_knownSimple_from_f_source :
    twoCoreAmbient (OriginalSource.sourceGroup T M Mc E s) ≤
      centralizer (localModule T M : Set G) :=
  core_centralizes_knownSimple earlier descent hs hsE c fusion hG classificationF
    (PushingUp.doubledNaturalSource KnownSimple.IsKnownSimple)

/-- The actual terminal contradiction retains only the genuine earlier
local inputs and corrected F.6 classification. -/
theorem terminal_contradiction_knownSimple_from_f_source : False :=
  terminal_contradiction_knownSimple earlier descent hs hsE c fusion hG classificationF
    (PushingUp.doubledNaturalSource KnownSimple.IsKnownSimple)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
