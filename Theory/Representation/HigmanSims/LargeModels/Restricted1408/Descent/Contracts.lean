module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Matrices
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Presentation

/-!
# The finite matrix input to marked HS descent

This contract isolates invertibility and the thirteen source-word identities
on the literal degree-1408 matrices. The certificate producer can import it
without importing the final descent assembly. No action of the HS carrier
or irreducibility assumption is included.

Sources: ATLAS HSG1-P1.M and HSd2G1-f2r1408B0 restricted by HSd2G1-max1W1.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Restricted1408

open Sporadic.LeechRelated.HS

/-- A finite collection of matrix identities, including invertibility.
The witnesses have the literal matrix entries and obey all thirteen words
of the sourced presentation. No action of HS is part of this contract. -/
def MatrixRelations : Prop :=
  ∃ a b : Matˣ, (a : Mat) = matrixA ∧ (b : Mat) = matrixB ∧
    ∀ i, AtlasPresentation.word a b i = 1

end Representation.HigmanSims.LargeModels.Restricted1408
