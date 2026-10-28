module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarCandidates
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticCertificateData

/-!
# A block of the exhaustive scalar-pair certificate

Each row fixes one scalar quadratic code of weight ten and checks all 168
possible partner codes. When their truth tables cover the fifteen nonzero
vectors, the reconstructed coefficient code must occur in the witness list.
All checks use kernel reduction. Splitting the rows bounds checking cost.

Source: MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.QuadraticCertificate

@[expose] public def scalarRowCheck (a : Fin 1024) : Bool :=
  scalarCandidates.all fun b =>
    if (scalarTable a ||| scalarTable b) = 65534#16 then
      unitaryWitnesses.any fun r => decide (r.1 = pairedCode a b)
    else true

end MacWilliamsSylow.QuadraticCertificate

