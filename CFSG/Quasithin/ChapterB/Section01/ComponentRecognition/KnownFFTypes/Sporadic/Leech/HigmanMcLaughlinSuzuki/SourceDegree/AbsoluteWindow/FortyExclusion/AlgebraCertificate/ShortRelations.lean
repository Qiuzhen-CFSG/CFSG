module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.MarkedNorm
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup

/-!
# Short word relations in the actual HS norm algebra

The thirteen words in ATLAS HSG1-P1 are checked on the literal degree-100
permutations. Only the validity of these relations is used; no presentation
completeness assertion is needed. Their algebra images are equal to one,
so they can be used in a finite reduction modulo the literal norm ideal.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HSG1-P1 .
The source file and diagnostic transcription are retained in `source/`.
-/

@[expose] public section
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate
namespace ShortRelations
open Theory.GroupTheory _root_.Sporadic.LeechRelated.HS

/-- Alphabet A, B, B inverse, on the literal catalogue carrier. -/
noncomputable def letter (s : Fin 3) : KnownSimple.SporadicName.hs.Carrier :=
  if s = 0 then generatorAElement else if s = 1 then generatorBElement
  else generatorBElement⁻¹

/-- The ATLAS defining and redundant relation words; A inverse is replaced
by A, which is valid on these actual permutations. -/
def relatorWord (i : Fin 13) : List (Fin 3) :=
  match i.val with
  | 0 => [0, 0]
  | 1 => [1, 1, 1, 1, 1]
  | 2 => [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  | 3 => [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
  | 4 => [0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]
  | 5 => [0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1]
  | 6 => [0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1]
  | 7 => [0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 2, 0, 1, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2]
  | 8 => [0, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 1]
  | 9 => [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2, 2]
  | 10 => [0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 2, 0, 1, 0, 1, 0, 2]
  | 11 => [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 2]
  | _ => [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 1, 1]

private def packedLetter (s : Fin 3) : _root_.Sporadic.LeechRelated.HS.Carrier :=
  if s = 0 then FiveSubgroup.a else if s = 1 then FiveSubgroup.b else FiveSubgroup.b⁻¹

private theorem packedLetter_eq : packedLetter = letter := by
  have ha : FiveSubgroup.a = generatorAElement := by
    apply Subtype.ext
    exact FiveSubgroup.aPerm_eq_generator
  have hb : FiveSubgroup.b = generatorBElement := by
    apply Subtype.ext
    exact FiveSubgroup.bPerm_eq_generator
  funext s
  simp only [packedLetter, letter, ha, hb]
  rfl

private theorem relation0 : evalWord packedLetter (relatorWord 0) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation1 : evalWord packedLetter (relatorWord 1) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation2 : evalWord packedLetter (relatorWord 2) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation3 : evalWord packedLetter (relatorWord 3) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation4 : evalWord packedLetter (relatorWord 4) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation5 : evalWord packedLetter (relatorWord 5) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation6 : evalWord packedLetter (relatorWord 6) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation7 : evalWord packedLetter (relatorWord 7) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation8 : evalWord packedLetter (relatorWord 8) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation9 : evalWord packedLetter (relatorWord 9) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation10 : evalWord packedLetter (relatorWord 10) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation11 : evalWord packedLetter (relatorWord 11) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

private theorem relation12 : evalWord packedLetter (relatorWord 12) = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply FiveSubgroup.allFin
  decide +kernel

/-- Each relation holds in the actual group, independently of any presentation. -/
theorem relator_valid (i : Fin 13) : evalWord letter (relatorWord i) = 1 := by
  rw [← packedLetter_eq]
  fin_cases i
  · exact relation0
  · exact relation1
  · exact relation2
  · exact relation3
  · exact relation4
  · exact relation5
  · exact relation6
  · exact relation7
  · exact relation8
  · exact relation9
  · exact relation10
  · exact relation11
  · exact relation12

/-- The actual binary algebra image of a word. -/
noncomputable def algebraWord (w : List (Fin 3)) : BinaryAlgebra :=
  MonoidAlgebra.single (evalWord letter w) 1

/-- Word concatenation has the exact group-algebra product convention. -/
theorem algebraWord_append (u v : List (Fin 3)) :
    algebraWord (u ++ v) = algebraWord u * algebraWord v := by
  simp only [algebraWord, evalWord_append, MonoidAlgebra.single_mul_single, one_mul]

/-- Universal algebra relations available to the finite norm calculation. -/
theorem algebraRelator_eq_one (i : Fin 13) : algebraWord (relatorWord i) = 1 := by
  rw [algebraWord, relator_valid, ← MonoidAlgebra.one_def]

/-- A literal ideal-membership consumer of all thirteen checked identities. -/
theorem algebraRelator_sub_one_mem (i : Fin 13) :
    algebraWord (relatorWord i) - 1 ∈ fiveNormIdeal := by
  rw [algebraRelator_eq_one, sub_self]
  exact fiveNormIdeal.zero_mem

end ShortRelations
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate
