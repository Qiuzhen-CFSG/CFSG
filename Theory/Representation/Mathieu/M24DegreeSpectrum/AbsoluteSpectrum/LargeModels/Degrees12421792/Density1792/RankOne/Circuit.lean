module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.Projector
/-!
# A ten-action circuit for the singular matrix

Distributing the four published summands and collecting equal left actions
expresses their value on any column using ten applications of the original
ATLAS generators. `KernelReduction` applies this identity to the fixed nucleus.
No generator relation, kernel, density, or invertibility is assumed here.
See `../source/README.md` for the exact singular expression and attribution.
-/

@[expose] public section
open Matrix
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792

theorem singular_action_circuit (u : Fin 1792 → ZMod 2) :
    singular.mulVec u =
      let x1 := Data1792.second.mulVec u
      let x2 := Data1792.second.mulVec x1
      let x3 := Data1792.first.mulVec x2
      let x4 := Data1792.first.mulVec x1
      let x5 := Data1792.second.mulVec x4
      let x6 := Data1792.second.mulVec x5
      let x7 := Data1792.second.mulVec (x3 + x1)
      let x8 := Data1792.first.mulVec (x4 + x5 + x6)
      let x9 := Data1792.first.mulVec (x3 + x1 + x7 + x4 + x6)
      let x10 := Data1792.second.mulVec (x3 + x1 + x7 + x8)
      x4 + x5 + x9 + x10 := by
  dsimp only
  simp only [singular, add_mulVec, ← mulVec_mulVec, mulVec_add, one_mulVec]
  abel
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
