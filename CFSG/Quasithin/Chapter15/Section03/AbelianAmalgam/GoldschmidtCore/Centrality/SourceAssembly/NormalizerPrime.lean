module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.NormalizerPrime
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly.OriginalGeometry

/-!
# Applying the derived normalizer bound to the original terminal consumer

The ordinary kernel in EarlierData and the original fixed-line centralizer
bound now supply the prime-to-three normalizer premise of the terminal
contradiction. The genuine earlier amalgam classification remains explicit.
Source: Aschbacher--Smith, 15.3.49(5) and the terminal 15.3 argument.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

/-- The original terminal contradiction with the normalizer's prime-to-three
bound derived from its actual earlier local data. The residual kernel in
`EarlierData` remains the original ordinary-case input. -/
theorem terminal_contradiction_knownSimple_from_fixed_centralizer
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M)
    (classificationF : Semilinear.Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) : False := by
  exact terminal_contradiction_knownSimple_from_original_bounds earlier hG hfixed
    (NormalizerPrime.normalizer_three_prime_from_earlier earlier hG hfixed) classificationF

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
