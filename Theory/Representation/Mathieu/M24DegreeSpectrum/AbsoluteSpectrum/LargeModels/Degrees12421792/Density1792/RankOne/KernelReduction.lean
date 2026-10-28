module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.Circuit
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.KernelData

/-!
# Reducing the right kernel to ten literal column actions

The proposed columns are concrete data. Their final XOR is checked here;
the ten original-generator actions remain explicit Boolean hypotheses.
Soundness of each action and the distributive circuit identity then prove
`singular.mulVec nucleus = 0`. This is a conditional numerical reduction,
not an unconditional kernel certificate. See `source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open Matrix RankOneCertificate

set_option maxRecDepth 8192 in
private theorem circuit_cancels : x4 ^^^ x5 ^^^ x9 ^^^ x10 = 0 := by decide +kernel

/-- Exact generator-action obligations for the published nucleus. -/
theorem singular_right_kernel_of_action_checks
    (h1 : checkAction (x0) x1 Data1792.secondRows.toList = true)
    (h2 : checkAction (x1) x2 Data1792.secondRows.toList = true)
    (h3 : checkAction (x2) x3 Data1792.firstRows.toList = true)
    (h4 : checkAction (x1) x4 Data1792.firstRows.toList = true)
    (h5 : checkAction (x4) x5 Data1792.secondRows.toList = true)
    (h6 : checkAction (x5) x6 Data1792.secondRows.toList = true)
    (h7 : checkAction (x3 ^^^ x1) x7 Data1792.secondRows.toList = true)
    (h8 : checkAction (x4 ^^^ x5 ^^^ x6) x8 Data1792.firstRows.toList = true)
    (h9 : checkAction (x3 ^^^ x1 ^^^ x7 ^^^ x4 ^^^ x6) x9 Data1792.firstRows.toList = true)
    (h10 : checkAction (x3 ^^^ x1 ^^^ x7 ^^^ x8) x10 Data1792.secondRows.toList = true)
    : singular.mulVec nucleus = 0 := by
  have hA : Data1792.firstRows.size = 1792 := by decide +kernel
  have hB : Data1792.secondRows.size = 1792 := by decide +kernel
  have a1 : Data1792.second.mulVec (vector (x0)) = vector x1 :=
    action_sound Data1792.secondRows hB _ _ h1
  have a2 : Data1792.second.mulVec (vector (x1)) = vector x2 :=
    action_sound Data1792.secondRows hB _ _ h2
  have a3 : Data1792.first.mulVec (vector (x2)) = vector x3 :=
    action_sound Data1792.firstRows hA _ _ h3
  have a4 : Data1792.first.mulVec (vector (x1)) = vector x4 :=
    action_sound Data1792.firstRows hA _ _ h4
  have a5 : Data1792.second.mulVec (vector (x4)) = vector x5 :=
    action_sound Data1792.secondRows hB _ _ h5
  have a6 : Data1792.second.mulVec (vector (x5)) = vector x6 :=
    action_sound Data1792.secondRows hB _ _ h6
  have a7 : Data1792.second.mulVec (vector (x3 ^^^ x1)) = vector x7 :=
    action_sound Data1792.secondRows hB _ _ h7
  have a8 : Data1792.first.mulVec (vector (x4 ^^^ x5 ^^^ x6)) = vector x8 :=
    action_sound Data1792.firstRows hA _ _ h8
  have a9 : Data1792.first.mulVec (vector (x3 ^^^ x1 ^^^ x7 ^^^ x4 ^^^ x6)) = vector x9 :=
    action_sound Data1792.firstRows hA _ _ h9
  have a10 : Data1792.second.mulVec (vector (x3 ^^^ x1 ^^^ x7 ^^^ x8)) = vector x10 :=
    action_sound Data1792.secondRows hB _ _ h10
  change singular.mulVec (vector x0) = 0
  rw [singular_action_circuit]
  simp only [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ← vector_xor]
  rw [circuit_cancels, vector_zero]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
