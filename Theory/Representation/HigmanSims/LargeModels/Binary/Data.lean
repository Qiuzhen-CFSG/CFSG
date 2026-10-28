module

public import Theory.Representation.HigmanSims.LargeModels.Inputs
public import Theory.Representation.HigmanSims.LargeModels.Binary.Data56
public import Theory.Representation.HigmanSims.LargeModels.Binary.Data132
public import Theory.Representation.HigmanSims.LargeModels.Binary.Data518
public import Theory.Representation.HigmanSims.LargeModels.Binary.Data1000

/-!
# The four binary HS candidates in their published bases

The coordinate dimensions are exactly `binaryDegree`. Each matrix retains the
published ATLAS rows, with no inverse or transpose. The HS permutation carrier
instead inverts the published right permutations, so the two conventions
preserve the same abstract words. A homomorphism from that literal carrier is
still required; the matrices alone do not supply it.

Source: ATLAS HSG1-f2r56B0, HSG1-f2r132B0, HSG1-f2r518B0 and
HSG1-f2r1000B0. See `source/README.md` for attribution and original files.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.Binary

def aRows : Fin 4 → Array ℕ := ![D56.aRows, D132.aRows, D518.aRows, D1000.aRows]
def bRows : Fin 4 → Array ℕ := ![D56.bRows, D132.bRows, D518.bRows, D1000.bRows]

abbrev Vector (i : Fin 4) := Fin (binaryDegree i) → ZMod 2
abbrev Mat (i : Fin 4) := Matrix (Fin (binaryDegree i)) (Fin (binaryDegree i)) (ZMod 2)

def aMatrix (i : Fin 4) : Mat i := Thompson.BinaryMatrix.decode (binaryDegree i) (aRows i)
def bMatrix (i : Fin 4) : Mat i := Thompson.BinaryMatrix.decode (binaryDegree i) (bRows i)

end Representation.HigmanSims.LargeModels.Binary
