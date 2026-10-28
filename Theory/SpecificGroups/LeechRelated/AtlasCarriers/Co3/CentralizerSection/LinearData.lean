module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.Tables
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Data.ZMod.Basic

/-!
# Three binary symplectic matrices for the Co₃ quotient comparison

These explicit matrices preserve Mathlib's standard alternating form, as checked
in the kernel. Their proposed correspondence with the three degree-36 generators
is separate from this membership theorem, as is full-group generation.

The matrices were discovered by GAP from the fixed ATLAS action; its isomorphism
search is not trusted. The retained raw matrix witness uses the anti-diagonal
basis, reordered here as (1,2,3,6,5,4) to the standard hyperbolic basis.
Source motivation: GLS3 Table 5.3j; numerical provenance and reproduction are in
`CentralizerSection/source/`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Co3.CentralizerSection.LinearData

abbrev K := ZMod 2
abbrev Index := Fin 3 ⊕ Fin 3
/-- The underlying matrix group is definitionally the ATLAS `Sp 3 K` carrier. -/
abbrev Sp := ↥(Matrix.symplecticGroup (Fin 3) K)

def coordinate : Index → Fin 6 := Sum.elim (fun i => i.castAdd 3) (fun i => i.natAdd 3)

def entries0 : Matrix (Fin 6) (Fin 6) K :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 0], ![1, 1, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1]]

def entries1 : Matrix (Fin 6) (Fin 6) K :=
  ![![1, 1, 1, 1, 0, 1], ![1, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 1, 1], ![1, 0, 0, 1, 0, 1], ![0, 1, 1, 1, 0, 0], ![0, 1, 0, 0, 1, 1]]

def entries2 : Matrix (Fin 6) (Fin 6) K :=
  ![![1, 1, 1, 0, 1, 0], ![1, 1, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 1], ![0, 1, 1, 0, 1, 1], ![1, 0, 1, 1, 1, 0], ![0, 1, 1, 1, 0, 0]]

def entries : Fin 3 → Matrix (Fin 6) (Fin 6) K := ![entries0, entries1, entries2]

def matrix (i : Fin 3) : Matrix Index Index K :=
  (entries i).submatrix coordinate coordinate

set_option maxRecDepth 20000 in
theorem matrix_preserves : ∀ i,
    (matrix i).transpose * Matrix.J (Fin 3) K * matrix i = Matrix.J (Fin 3) K := by
  apply Tables.allFin
  decide +kernel

/-- Three genuine elements of the full binary symplectic matrix group. -/
def generator (i : Fin 3) : Sp :=
  ⟨matrix i, SymplecticGroup.mem_iff'.mpr (matrix_preserves i)⟩

end Sporadic.LeechRelated.Co3.CentralizerSection.LinearData
