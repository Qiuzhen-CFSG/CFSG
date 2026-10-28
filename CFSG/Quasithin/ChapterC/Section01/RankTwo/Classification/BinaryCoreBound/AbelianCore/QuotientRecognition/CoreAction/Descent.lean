module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.IntrinsicKernel

/-!
# Descent of the elementary binary MS core action

For elementary D=[O₂(J),L], the genuine MS hypotheses make the component
action image centerless, so the intrinsic O₂(L) centralizes D. A maximum
elementary subgroup of R supplies a best offender in the ambient action;
transfer across its commuting two-group kernel gives a component offender.
Transport through the marked component projection then gives an offender
for the canonical action of the specified SL₃(2) on the whole core.

The elementary-core hypothesis is explicit. Establishing it from abelianity
and assembling the unconditional whole-core action belong to CoreAction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31–34,
printed pp.135–137.
-/

public section

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]

/-- The elementary whole MS core centralizes O₂(L), and its canonical action
of the specified SL₃(2) quotient has an offender. -/
theorem Input.abelianCore_exists_descendedOffender :
    ∃ hz : commutatorCore L ≤ Subgroup.centralizer ((pCore 2 L).map L.subtype : Set J),
      Representation.BinaryOffender.IsFFModule
        (AbelianCore.QuotientRecognition.linearAction h hz) := by
  let hz := h.elementaryCore_componentCore_centralizes
  exact ⟨hz, h.descendedOffender_of_componentOffender hz
    (h.coreComponentRepresentation_isFFModule_of_centralizes hz)⟩

end CFSG.Quasithin.ChapterC.BinaryMS
