module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.PairGeneration.Coverage.Soundness

/-!
# A measured sample of actual factorization certificates

All 144 products in point-orbit row 31 are checked in the kernel.
This small sample validates the certificate representation before the full
finite families are compiled. It does not assert full double-coset coverage.

Source: the primary ATLAS generators and the fixed representative codes;
see `source/README.md` for measurements and conventions.
-/

namespace Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
open Atlas1600OrderCertificate

set_option maxRecDepth 20000 in
public theorem factorRow31_checked : ∀ j : Fin 144, factorTest 31 j = true := by
  apply allFin
  decide +kernel

/-- The sample applies to the actual fixed group words and normalizer factors. -/
public theorem factorRow31 (j : Fin 144) :
    orbitRep 31 * stabilizerRep j =
      normalWord (factorLeft 31 j) *
      representative (factorRep 31 j) *
      normalWord (factorRight 31 j) :=
  factorTest_sound _ _ (factorRow31_checked j)

end Tits.MinimumIndexThirteen.PairGeneration.CoverageCertificate
