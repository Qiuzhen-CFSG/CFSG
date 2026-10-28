module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Graph.ConjugationData

/-!
# Checked generator conjugation certificates

The signed word inverses and their inverse-adjoint realifications are checked
first. The final two integer identities verify the graph swap on the actual
two rational generators. Clearing the common denominators leaves only integer
products, checked sequentially in one declaration. `Conjugation` transports
them to the retained integral Leech group and the literal modular quotient.
Source conventions and numerical provenance are those of `ConjugationData`.
-/

@[expose] public section
open Matrix Atlas.Algebra
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
open Block Block.Realization

theorem inverseCertificates :
    (-rawAMatrix) * imageAInverse = 1 ∧
    (-rawBMatrix) * imageBInverse = 1 := by
  constructor <;> decide +kernel

theorem actionSpecifications :
    realification imageAInverse.conjTranspose = (1/2 : ℚ) • integerMatrix imageANumerator ∧
    realification imageBInverse.conjTranspose = (1/2 : ℚ) • integerMatrix imageBNumerator := by
  constructor <;> decide +kernel

theorem conjugationCertificates :
    numerator * actionANumerator = imageANumerator * numerator ∧
    numerator * actionBNumerator = imageBNumerator * numerator := by
  constructor <;> decide +kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Graph
