module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData

/-! Kernel-checked evaluation of nine pair constraints, using simultaneous
binary matrix evaluation. The conjunction keeps these calculations sequential.
See `Packed.lean` for the interpretation and `Certificate.lean` for the source. -/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate

set_option maxRecDepth 4096 in
theorem checks1 :
    forbidden numericalRelations 1 3 = 57894277771593319327455909206843211008119164848923406400457075748480734936938 ∧
    forbidden numericalRelations 1 4 = 47759643008024506605821757461667828157007494355367790694187739674019354263680 ∧
    forbidden numericalRelations 1 5 = 57894277744633372660305269412176195921099528982989403443088874736880795467626 ∧
    forbidden numericalRelations 1 6 = 57894277744633372654028167675327991218847355744033970986162769120863402754026 ∧
    forbidden numericalRelations 1 7 = 57894277771593293616447199566409707641227165538939745723729637712563317604330 ∧
    forbidden numericalRelations 1 8 = 114774385328003846049731005648259986788153353941040207359019078407405527094719 ∧
    forbidden numericalRelations 2 3 = 57893836059827124731373513382468025278489543363951295037781093443400271626218 ∧
    forbidden numericalRelations 2 4 = 56989500155127236809951802649905003514371505105572021390083020553959853877440 ∧
    forbidden numericalRelations 2 5 = 57894274293753205663509924382617386495312978913743125961313333891012774215808 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
