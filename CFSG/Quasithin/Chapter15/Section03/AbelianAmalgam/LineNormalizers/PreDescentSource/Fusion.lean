module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.NormalizerPrime
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly.OriginalGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.Complete

/-!
# The fixed-plane normalizer bound from the earlier fusion inputs

The fusion record already contains the original 15.3.45(3) centralizer
bound. Together with the ordinary residual kernel in EarlierData, the
proved normalizer calculation gives 15.3.49(5) for the same fixed plane
Z_S = C_V(N_T(P)). No additional normalizer premise is needed at descent.

The terminal application also supplies the proved corrected F.6
classification. It retains only the original earlier local structure,
fusion inputs and ambient simple-QTKE hypothesis.

Source: Aschbacher--Smith, 15.3.45(3), 15.3.49(5), and the final proof of
15.3.1, printed pp.1140--1143 and 1154--1155; corrected F.6.18, pp.309--310.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

/-- Original 15.3.49(5) on the literal fixed plane, using the preceding
centralizer bound already present in the terminal consumer's fusion record. -/
theorem PreDescentSource.normalizer_three_prime_from_fusion
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (fusion : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))) :=
  NormalizerPrime.normalizer_three_prime_from_earlier earlier hG
    fusion.plane_fixed_centralizer

namespace GoldschmidtCore.Centrality.SourceAssembly

/-- The original terminal contradiction with 15.3.49(5) and corrected F.6
discharged from their proved source producers. -/
theorem terminal_contradiction_knownSimple_from_earlier_fusion
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (fusion : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) : False :=
  terminal_contradiction_knownSimple_from_normalizer_bound earlier fusion hG
    (PreDescentSource.normalizer_three_prime_from_fusion earlier fusion hG)
    Semilinear.Recognition.FSource.sourceClassification_knownSimple_complete

end GoldschmidtCore.Centrality.SourceAssembly
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
