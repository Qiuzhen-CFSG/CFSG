module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticValidity
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticCertificateData
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarCandidates
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticScalarPairs

/-!
# Reduction of exhaustive balanced unitary coverage to scalar pairs

Balanced nonzero fibres force both scalar projections to have weight ten, so
the exhaustive scalar certificate restricts each projection to 168 codes.
Anisotropy forces the union of their truth tables to contain all fifteen
nonzero vectors. The finite pair certificate checks the admissible pairs
against the listed witnesses. Reconstruction identifies their packed code with
the original ten-coefficient code.

Source: MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3, cited in Janko--Thompson
Theorem 1.3(b), p.386.
-/

namespace MacWilliamsSylow.QuadraticCertificate

/-- Assemble coverage from the reduced scalar-pair certificate. -/
public theorem witnesses_cover_of_scalar_pairs
    (hpairs : ∀ a : Fin 1024, a ∈ scalarCandidates →
      ∀ b : Fin 1024, b ∈ scalarCandidates →
      (scalarTable a ||| scalarTable b) = 65534#16 →
      (unitaryWitnesses.any fun r => decide (r.1 = pairedCode a b)) = true) :
    ∀ n : Fin 1048576, anisotropic n = true → balanced n = true →
      (unitaryWitnesses.any fun r => decide (r.1 = n)) = true := by
  intro n ha hb
  have h0 := scalar_candidates_cover (scalarCode (coefficients n) 0)
    (scalarWeight_of_balanced n hb 0)
  have h1 := scalar_candidates_cover (scalarCode (coefficients n) 1)
    (scalarWeight_of_balanced n hb 1)
  have hp := hpairs _ h0 _ h1 (scalar_union_of_anisotropic n ha)
  simpa only [pairedCode_scalarCode] using hp

/-- Every balanced anisotropic coefficient code occurs in the witness list. -/
public theorem witnesses_cover :
    ∀ n : Fin 1048576, anisotropic n = true → balanced n = true →
      (unitaryWitnesses.any fun r => decide (r.1 = n)) = true :=
  witnesses_cover_of_scalar_pairs scalar_pairs_cover

end MacWilliamsSylow.QuadraticCertificate
