module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData

/-! Kernel-checked evaluation of nine pair constraints, using simultaneous
binary matrix evaluation. The conjunction keeps these calculations sequential.
See `Packed.lean` for the interpretation and `Certificate.lean` for the source. -/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate

set_option maxRecDepth 4096 in
theorem checks0 :
    forbidden numericalRelations 0 1 = 57894277741256771591199800683155615405777573674193836970428181219060213383146 ∧
    forbidden numericalRelations 0 2 = 57893832608953951128947262384176091895566523685589509215706049247826958762112 ∧
    forbidden numericalRelations 0 3 = 57893832608743301041696755793953046274164939226611494368014295452049800527850 ∧
    forbidden numericalRelations 0 4 = 57894263941140653368168984902230968000153966314796228593842518761794369847274 ∧
    forbidden numericalRelations 0 5 = 57893836032867178064222873587801010191469907498017292080412892431800332150976 ∧
    forbidden numericalRelations 0 6 = 57780757820721361467129542547385233501738810879304214535859412429106115995840 ∧
    forbidden numericalRelations 0 7 = 57894277744633372660305269412176195921099528982989403443088874736880795484138 ∧
    forbidden numericalRelations 0 8 = 114773943616237651453648609823884801058523732456068095996343096102325063767487 ∧
    forbidden numericalRelations 1 2 = 57894277771593319327455909206843211008119164848923406400457075748480734936938 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
