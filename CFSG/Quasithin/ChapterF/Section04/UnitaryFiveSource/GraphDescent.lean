module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.Reduction
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphConjugate

/-!
# Constructing graph conjugators from unitary graph-twist representatives

For an involution in the specified extension, a unitary graph-twist formula
supplies a concrete matrix norm. Five-dimensional descent constructs its
unitary conjugator, hence the literal graph equation on the original PSU
carrier. The scalar kernel of order five is retained during the norm step.

Source: F.4.29(2) and F.4.37, printed pp.289,293 of refs/quasithin.pdf.
Representability of the selected abstract automorphism and its marked flag
compatibility remain required source steps. This theorem discharges the
matrix cocycle and graph-conjugator premises once that formula is proved.
-/

public noncomputable section
open Theory.SpecificGroups.UnitaryFive
open Descent GraphFixed
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
variable (U : GreenBook.UnitaryFive.Model 4) (E : FiveExtension U)

/-- Construct the graph conjugator for an actual unitary graph-twist
involution, without assuming either a cocycle or a conjugacy witness. -/
theorem exists_graph_conjugator_of_unitary_twist (f : E.carrier) (hf2 : f^2=1)
    (u : U.form.unitarySubgroup)
    (hf : f.val=unitaryConj U.form u*projectiveAut U.form U.matrix) :
    ∃ v : U.form.unitarySubgroup,
      f.val=unitaryConj U.form v*projectiveAut U.form U.matrix*(unitaryConj U.form v)⁻¹ := by
  have hσ : U.form.conj ≠ 1 := by
    intro he
    obtain ⟨c,hc⟩ := U.exists_lineTraceOne
    have hfix : U.form.conj c=c := by rw [he]; rfl
    rw [hfix,CharTwo.add_self_eq_zero] at hc
    exact zero_ne_one hc
  have hu : (unitaryConj U.form u*projectiveAut U.form U.matrix)^2=1 := by
    rw [←hf]
    exact congrArg Subtype.val hf2
  obtain ⟨v,hv⟩ := conjugate_graph_of_twist_sq U.form U.matrix hσ U.conjugation
    (by simpa using U.card) u hu
  exact ⟨v,hf.trans hv⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
