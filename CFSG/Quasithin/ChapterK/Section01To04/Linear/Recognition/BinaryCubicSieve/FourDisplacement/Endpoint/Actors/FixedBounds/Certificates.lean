module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CertificateBound

/-!
# Checked displacement certificates for the sixty candidate representatives

First check the selected rows against the actual conjugation/graph matrices,
then check their right inverses. Both computations use kernel reduction.
The resulting bounds apply to the literal normalizer subgroups defined in
`Catalogue`, through the proved quotient-coordinate equivalence.

This proves the numerical bounds for the listed groups. Exhaustive coverage
of elementary subgroups is a separate obligation.

Source: Guralnick–Malle Lemma 4.5 and Proposition 4.8 step 3A.
-/

public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds

/-- Each supplied displacement row agrees with the actual quotient action. -/
theorem displacement_table_check : ∀ i : Fin 60,
    displacementMatrix i = tableDisplacementMatrix i := by
  decide +kernel

/-- Each listed displacement table has the supplied right inverse. -/
theorem right_inverse_check : ∀ i : Fin 60,
    tableDisplacementMatrix i * rightInverse i = 1 := by
  decide +kernel

/-- The literal displacement equations are independent. -/
theorem certificate_check (i : Fin 60) : displacementMatrix i * rightInverse i = 1 := by
  rw [displacement_table_check]
  exact right_inverse_check i

/-- Every listed subgroup has more than twice its listed generator count in
common-fixed-space codimension. -/
theorem catalogue_gap (i : Fin 60) :
    2 * (catalogueGenerators i).length <
      fixedCodim (normalizerRepresentation adjoint) (catalogueSubgroup i) :=
  catalogue_gap_of_certificate i (certificate_check i)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
