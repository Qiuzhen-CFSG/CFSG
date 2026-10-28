module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData

/-! Kernel-checked evaluation of nine pair constraints, using simultaneous
binary matrix evaluation. The conjunction keeps these calculations sequential.
See `Packed.lean` for the interpretation and `Certificate.lean` for the source. -/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate

set_option maxRecDepth 4096 in
theorem checks3 :
    forbidden numericalRelations 4 6 = 57894277771382669026783943598368903097936407724419015673104114806406774554602 ∧
    forbidden numericalRelations 4 7 = 57894277771572519115010934830157976883991565422949932639417672049969521786858 ∧
    forbidden numericalRelations 4 8 = 114774385328003845848863750104194166945335105788295433159210988412608154949055 ∧
    forbidden numericalRelations 5 6 = 57894277768012675699471055931912165604119375729267457361434342499528430419946 ∧
    forbidden numericalRelations 5 7 = 57894277771586325926809713438728130263003461219083482283830473482168633819114 ∧
    forbidden numericalRelations 5 8 = 114774371524511149254727341512467454680987092237649275240334085067331440973119 ∧
    forbidden numericalRelations 6 7 = 57894263941140650154292895635961578428582915648663276935432039321980353986688 ∧
    forbidden numericalRelations 6 8 = 114774371524511149254727341512099224776268954588336237460216115322144692344127 ∧
    forbidden numericalRelations 7 8 = 85600203143509987390493614332104390684573785132513464129615913244668419102143 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
