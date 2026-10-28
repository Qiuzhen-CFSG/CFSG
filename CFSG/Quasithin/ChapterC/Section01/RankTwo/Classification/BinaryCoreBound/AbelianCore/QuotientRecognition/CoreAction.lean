module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.CentralizerQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Exponent
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent

/-!
# Toward the whole-core binary MS action

The ambient-action reduction proves C_J(D)≤O₂(J) and constructs a faithful
FF-action on D when D is elementary. Its acting group is the actual
conjugation image J/C_J(D).

The final theorem combines the exponent-two argument for the abelian MS core
with descent of a genuine offender to the specified SL₃(2) quotient. The
resulting `Input.exists_abelianCore_coreFFAction` packages the canonical
whole-core action and its FF-module assertion.

Source: Aschbacher–Smith C.1.31–34, combined manuscript (1 March 2004),
printed pp.135–137.
-/


public section

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterC.BinaryMS

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

/-- The whole abelian binary MS core is elementary and carries the canonical
FF-action of the marked binary component quotient. -/
theorem Input.exists_abelianCore_coreFFAction
    (hc : IsMulCommutative (commutatorCore L)) :
    ∃ he : IsElementaryAbelian 2 (commutatorCore L),
      letI := he
      Nonempty (AbelianCore.QuotientRecognition.CoreFFAction h) := by
  let he : IsElementaryAbelian 2 (commutatorCore L) := h.abelianCore_elementary hc
  let _ : IsElementaryAbelian 2 (commutatorCore L) := he
  obtain ⟨hz, hFF⟩ := h.abelianCore_exists_descendedOffender
  exact ⟨he, ⟨AbelianCore.QuotientRecognition.coreFFAction h hz hFF⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS
