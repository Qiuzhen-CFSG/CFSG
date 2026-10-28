module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticWitness
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticValidity
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticCoverage
public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticWitnessSoundness

/-!
# Assembly of the finite balanced unitary quadratic certificate

The encoding is surjective on all ten-coefficient polynomials, and the finite
anisotropy and fibre-count tests follow from the mathematical hypotheses.
Coverage selects a listed frame; soundness supplies all six-generator table
equations and both subgroup-generation requirements. The kernel-checked coverage
and soundness certificates discharge the two finite premises, giving the balanced
anisotropic normal form for every ten-coefficient polynomial.

The normal form is the unitary alternative of MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3, cited in Janko–Thompson Theorem 1.3(b), p.386.
-/

namespace MacWilliamsSylow

/-- Assemble a coordinate frame from separately certified coverage and soundness. -/
public theorem coordinate_unitaryQuadraticFrame_of_certificate
    (hcoverage : ∀ n : Fin 1048576,
      QuadraticCertificate.anisotropic n = true → QuadraticCertificate.balanced n = true →
      (unitaryWitnesses.any fun r => decide (r.1 = n)) = true)
    (hsound : (unitaryWitnesses.all QuadraticCertificate.rowChecks) = true)
    (c : QuadraticCoefficients)
    (ha : ∀ x, coordinateSquare c x = 1 → x = 1)
    (hb : ∀ z : BinaryCoordinates 2, z ≠ 1 →
      Nat.card {v : BinaryCoordinates 4 // coordinateSquare c v = z} = 5) :
    Nonempty (UnitaryQuadraticFrame (coordinateSquare c) (coordinatePolar c)) := by
  obtain ⟨n, rfl⟩ := QuadraticCertificate.coefficients_surjective c
  have hcov := hcoverage n
    (QuadraticCertificate.anisotropic_of_hypothesis n ha)
    (QuadraticCertificate.balanced_of_hypothesis n hb)
  obtain ⟨r, hr, he⟩ := List.any_eq_true.mp hcov
  have hcode : r.1 = n := of_decide_eq_true he
  have hf := QuadraticCertificate.frame_of_rowChecks r
    (List.all_eq_true.mp hsound r hr)
  simpa only [hcode] using hf

/-- Every balanced anisotropic coordinate quadratic map admits the unitary frame,
including all table equations and generation of both coordinate groups. -/
public theorem coordinate_unitaryQuadraticFrame (c : QuadraticCoefficients)
    (ha : ∀ x, coordinateSquare c x = 1 → x = 1)
    (hb : ∀ z : BinaryCoordinates 2, z ≠ 1 →
      Nat.card {v : BinaryCoordinates 4 // coordinateSquare c v = z} = 5) :
    Nonempty (UnitaryQuadraticFrame (coordinateSquare c) (coordinatePolar c)) :=
  coordinate_unitaryQuadraticFrame_of_certificate
    QuadraticCertificate.witnesses_cover QuadraticCertificate.witnesses_sound c ha hb

end MacWilliamsSylow
