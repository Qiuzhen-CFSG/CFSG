module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorGeometry
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorOrbits.Checks

/-!
# Coverage of the Rudvalis seed orbit by 76 sectors

The finite family contains the exact 28-point seed and is closed under the
actual standard generators. Every row descends along candidate-generator
edges to an inverse sector image. The exhaustive checks are kernel proofs
over the explicit tables; finiteness and generation then give coverage for
every element of the actual model. Candidate normal-form completeness turns
the resulting candidate element into an index below 16384.

The inverse sector action is essential. Neither the full seed stabilizer nor
max4's order is used. Source application: Aschbacher--Smith, printed p.511
(PDF p.528), citing Aschbacher (1986), no.343. The witness producer and preserved
ATLAS action convention are documented in `SectorOrbits/source/Generate.py`.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
open scoped Pointwise

/-- Every translate of the exact seed is a candidate normal translate of a sector. -/
public theorem seed_orbit_covered :
    ∀ x : Model, ∃ (s : Fin 76) (n : Fin 16384), x • seed = normalTranslate s n :=
  SectorOrbitCertificate.cover_of_checks
    SectorOrbitCertificate.all_closureChecks SectorOrbitCertificate.all_forestChecks

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover
