module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.Contraction
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute.Data

/-!
# Native elements for the exterior-kernel matrix comparison

This interface fixes the two actual M24 permutations used by the binary
certificate. The independent comparison producer can import it without
importing the density proof or the absolute-irreducibility assembly.

Source context: James (1973), pp.57--111; GM02 Proposition 5.1, p.17.
-/

@[expose] public section
open Sporadic.Mathieu
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute

/-- The two literal native elements, in the same order as `Data.matrix`. -/
def nativeGenerator (j : Fin 2) : M24 :=
  ![⟨m24GeneratorA, m24GeneratorA_mem⟩, ⟨m24GeneratorB, m24GeneratorB_mem⟩] j

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour.KernelAbsolute
