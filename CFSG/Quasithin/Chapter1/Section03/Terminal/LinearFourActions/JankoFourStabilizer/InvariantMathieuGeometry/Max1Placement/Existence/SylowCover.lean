module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Branches

/-!
# Assembling the maximal J₄ Sylow cover from normal elementary subgroups

The order-two and order-2048 normal elementary branches now give actual max2
and max1 isomorphisms, respectively. A separate order-eight recognition input
supplies max4. This proves the desired cover conditionally on the structural
existence theorem and the order-eight recognition theorem, and connects it
to the original candidate-existence consumer with its literal quotient map.

The two remaining contracts are not asserted here. In particular this is not
the unconditional `maximalSylowCover` theorem. Final assembly must discharge
both, without adding ambient simplicity or replacing the concrete carriers.

Source: Aschbacher–Smith A.3.12 and its Sylow-overgroup proof, printed
pp.47–48, and the proof of 1.3.9, p.514; Aschbacher, *Overgroups of Sylow
subgroups in sporadic groups*, Memoirs AMS 60 (1986), no.343.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open SylowCover Janko4.LocalStructure.SymmetricLinear

/-- The central and large elementary branches are discharged by the concrete
certificates. The two displayed source inputs still require proofs. -/
theorem maximalSylowCover_of_normalElementaryStructure
    (hstructure : NormalElementaryStructure) (height : NormalEightRecognition) :
    MaximalSylowCover := by
  intro S M hM hSM
  obtain ⟨E, hEnormal, hEelementary, hEcard⟩ := hstructure S M hM hSM
  let := hEnormal
  let := hEelementary
  rcases hEcard with htwo | heightCard | hlarge
  · exact Or.inr (Or.inl (normal_two_recognition S M hM hSM E htwo))
  · exact Or.inr (Or.inr (height S M hM hSM E hEnormal hEelementary heightCard))
  · exact Or.inl (normal_large_recognition S M hM hSM E hlarge.ge)

/-- Application to the original local L₄(2) candidate-existence contract.
The max2 exclusion and max4 quotient remain with their existing producers. -/
theorem concreteCandidateExistence_of_normalElementaryStructure
    (hstructure : NormalElementaryStructure) (height : NormalEightRecognition)
    (hmax2 : Max2LocalExclusion)
    (e4 : (max4Subgroup ⧸ pCore 2 max4Subgroup) ≃* QuotientModel) :
    ConcreteCandidateExistenceTheorem :=
  concreteCandidateExistence_of_maximal_cover
    (maximalSylowCover_of_normalElementaryStructure hstructure height) hmax2 e4

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
