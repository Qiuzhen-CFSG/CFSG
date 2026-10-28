module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore.Crossed

/-!
# A small integral action certificate for the literal HS core

This interface separates two independent obligations: constructing the three
normalizer actors with their literal conjugation action and quotient relations,
and normalizing arbitrary crossed homomorphisms using that data. Neither the
existence of this data nor the cohomology calculation is asserted here.

The column-action matrices use exactly `CoreGeometry.coreCoordinates`, hence
its specified `rootWord` basis. The four relations are modulo the actual Q;
the actors need not satisfy them in N. Generation likewise includes Q.

Source: GLS3 Table 5.3m and Aschbacher–Smith I.2.2(5), printed p.412.
The untrusted discovery of the small relations is retained in
`Scratch/HSIntegralCore/short_certificate.py`; consumers must check them.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Sporadic.LeechRelated.HS BlockNormalizer

/-- The three marked integral basis vectors in the actual two-core. -/
@[expose] def integralBasis (j : Fin 3) : pCore 2 baseNormalizer :=
  CoreGeometry.coreCoordinates (.ofAdd (Pi.single j 1))

/-- Column-action matrices in the marked fourth-root coordinates. -/
@[expose] def integralMatrices : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod 4) :=
  ![!![3, 1, 2; 0, 1, 0; 0, 2, 3],
    !![3, 2, 3; 0, 1, 1; 0, 0, 3],
    !![3, 2, 3; 1, 1, 2; 2, 1, 2]]

/-- The image prescribed by column j of the ith matrix. -/
@[expose] def integralMatrixImage (i j : Fin 3) : pCore 2 baseNormalizer :=
  integralBasis 0 ^ (integralMatrices i 0 j).val *
    integralBasis 1 ^ (integralMatrices i 1 j).val *
    integralBasis 2 ^ (integralMatrices i 2 j).val

/-- Literal action, generation, and the four quotient relations used in the
six-coordinate calculation. Its construction is a separate obligation. -/
structure IntegralActionData where
  actor : Fin 3 → baseNormalizer
  generation : closure (Set.range actor ∪ (pCore 2 baseNormalizer : Set baseNormalizer)) = ⊤
  on_basis : ∀ i j, MulAut.conjNormal (actor i) (integralBasis j) = integralMatrixImage i j
  square_zero : actor 0 ^ 2 ∈ pCore 2 baseNormalizer
  square_one : actor 1 ^ 2 ∈ pCore 2 baseNormalizer
  conjugation_relation : (actor 2 * actor 0) / (actor 1 * actor 2) ∈ pCore 2 baseNormalizer
  long_relation : (actor 0 * actor 1 * actor 2 * actor 1 * actor 0) /
    (actor 1 * actor 2 ^ 3) ∈ pCore 2 baseNormalizer

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
