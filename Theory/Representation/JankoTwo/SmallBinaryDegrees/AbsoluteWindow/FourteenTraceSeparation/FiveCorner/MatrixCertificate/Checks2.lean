module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.MatrixCertificate.NumericalData

/-! Kernel-checked evaluation of nine pair constraints, using simultaneous
binary matrix evaluation. The conjunction keeps these calculations sequential.
See `Packed.lean` for the interpretation and `Certificate.lean` for the source. -/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate

set_option maxRecDepth 4096 in
theorem checks2 :
    forbidden numericalRelations 2 6 = 57894274293760199265023375694798264782501732165704682742029753503760741525696 ∧
    forbidden numericalRelations 2 7 = 57894269791448694368016326509404153401836458194027248142132731409214834638826 ∧
    forbidden numericalRelations 2 8 = 114774368073637979073321537061370331095501993765545972485441039235116464837951 ∧
    forbidden numericalRelations 3 4 = 57894263941140679079177694542664471367045965624779889270569956797711787190464 ∧
    forbidden numericalRelations 3 5 = 56876570384447849891183396334370343717385101441104326061591247903253138980992 ∧
    forbidden numericalRelations 3 6 = 57781196081614382667930044654750717997488773196304642977594243246253273999552 ∧
    forbidden numericalRelations 3 7 = 57894277771593290402571110300140318069656114872806794065319158272749301754048 ∧
    forbidden numericalRelations 3 8 = 114774368073427351276059293564385979043554487410293135247294725111898387240383 ∧
    forbidden numericalRelations 4 5 = 57894277771593319327455909206474981103401027199610368620339106003293986308224 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.MatrixCertificate
