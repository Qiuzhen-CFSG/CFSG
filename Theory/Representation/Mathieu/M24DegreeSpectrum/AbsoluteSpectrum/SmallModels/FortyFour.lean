module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.Inputs
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.Coordinates
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.DualSeparation

/-!
# Two native absolutely irreducible binary degree-forty-four modules

The code exterior contraction kernel and its dual give two actual actions on
44 coordinates, with literal native exterior-section maps. A checked density
certificate compared with the native kernel proves absolute irreducibility;
the traces of a native element and its inverse distinguish the two actions.
Duality and coordinate transport then give `binaryFortyFourModelsExist`, with
no exhaustivity or representation-classification premise.

Source context: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02, Proposition 5.1, manuscript p.17.
-/

@[expose] public section
noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
open Sporadic.Mathieu MathieuM24Degree44.FiveSpace
open FortyFour

/-- The two native exterior sections in the fixed 44-dimensional coordinate space. -/
def binaryFortyFourModels : Fin 2 → Representation (ZMod 2) M24 (Fin 44 → ZMod 2) :=
  ![codeModel, cocodeModel]

/-- Literal native section maps, available independently of simplicity. -/
theorem binaryFortyFourModels_sections (i : Fin 2) :
    IsSectionOf (binaryFortyFourModels i) codeExterior ∨
      IsSectionOf (binaryFortyFourModels i) cocodeExterior := by
  fin_cases i
  · exact Or.inl codeModel_isSectionOf
  · exact Or.inr cocodeModel_isSectionOf

theorem binaryFortyFourModels_absolute
    (h : IsAbsolutelyIrreducible kernelRepresentation) (i : Fin 2) :
    IsAbsolutelyIrreducible (binaryFortyFourModels i) := by
  fin_cases i
  · exact codeModel_absolute h
  · exact cocodeModel_absolute h

theorem binaryFortyFourModels_inequivalent
    (h : IsEmpty (kernelRepresentation.Equiv dualKernelRepresentation)) :
    Pairwise fun i j => IsEmpty ((binaryFortyFourModels i).Equiv (binaryFortyFourModels j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact codeModel_cocodeModel_inequivalent h
  · exact ⟨fun e => (codeModel_cocodeModel_inequivalent h).false e.symm⟩
  · exact (hij rfl).elim

/-- The final binary contract from the two remaining properties of the native kernel. -/
theorem binaryFortyFourModelsExist_of_native_kernel
    (habs : IsAbsolutelyIrreducible kernelRepresentation)
    (hneq : IsEmpty (kernelRepresentation.Equiv dualKernelRepresentation)) :
    BinaryFortyFourModelsExist :=
  ⟨binaryFortyFourModels, binaryFortyFourModels_absolute habs,
    binaryFortyFourModels_inequivalent hneq⟩

/-- Two inequivalent absolutely irreducible binary degree-44 representations of
the native Witt-design M24, constructed from the Golay exterior kernel and its dual. -/
theorem binaryFortyFourModelsExist : BinaryFortyFourModelsExist :=
  binaryFortyFourModelsExist_of_native_kernel
    kernel_isAbsolutelyIrreducible kernel_dual_inequivalent

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
