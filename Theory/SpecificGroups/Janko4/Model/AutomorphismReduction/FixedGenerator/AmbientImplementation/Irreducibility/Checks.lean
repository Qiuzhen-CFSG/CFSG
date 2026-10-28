module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Coordinates
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Products
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.AmbientImplementation.Irreducibility.Orbits

/-!
# The kernel reconstruction identity

The checked elimination product differs from the identity by one outer
product. This bounds the kernel of the test matrix by the line through
`rightSeed`. Together with the orbit and inverse certificates, it supplies
the cyclic-kernel criterion. Source motivation: GLS3 Table 5.3i; literal
ATLAS data attribution is in `Model/Data.lean`.
-/

public section
namespace Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
open GeneratorCertificates Matrix

set_option maxRecDepth 10000 in
theorem reconstruction : decodeRows eliminationRows * decodeRows testRows +
    vecMulVec (vector rightSeed) (Pi.single (111 : Fin 112) 1) = 1 := by
  rw [← decode_packedMul, elimination_product]
  have h : ∀ i j : Fin 112, decodeRows projectionRows i j +
      vector rightSeed i * (Pi.single (111 : Fin 112) 1 : Vec) j =
      (1 : BinaryMatrix) i j := by
    simp only [Pi.single_apply, Matrix.one_apply]
    decide +kernel
  exact funext fun i => funext fun j => h i j


end Janko4.OuterReduction.FixedGenerator.IrreducibilityCertificate
