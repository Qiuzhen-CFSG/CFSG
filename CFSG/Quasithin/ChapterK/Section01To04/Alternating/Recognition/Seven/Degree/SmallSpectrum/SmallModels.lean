module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Degree.SmallSpectrum.Inputs
public import Theory.Representation.AlternatingSevenBinarySmallModels

/-!
# The binary A₇ four- and six-dimensional spectrum candidates

The actual restricted A₈ natural four-space and its odd conjugate are absolutely
irreducible and inequivalent over F₂. The deleted permutation module, expressed
in a basis, supplies the absolutely irreducible six-space. This discharges the
small-model construction input to the separate spectrum-exhaustion argument.

Source: Aschbacher–Smith, K.1.2, printed p.452/PDF p.463, citing
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3.
-/

public section

open Representation
namespace CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum
open Representation.AlternatingSevenBinarySmallModels

/-- Two inequivalent absolutely irreducible binary four-spaces and the natural
absolutely irreducible six-space for the actual alternating group on seven letters. -/
theorem smallModelsExist : SmallModelsExist := by
  let ρ₄ := ![AlternatingSevenConjugatePair.Model.natural,
    AlternatingSevenConjugatePair.Model.outerNatural]
  refine ⟨ρ₄, six, ?_, six_absolute, ?_⟩
  · intro i
    fin_cases i
    · exact four_absolute
    · exact outerFour_absolute
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact ⟨fun e => AlternatingSevenConjugatePair.Model.natural_not_equiv_outerNatural ⟨e⟩⟩
    · exact ⟨fun e => AlternatingSevenConjugatePair.Model.natural_not_equiv_outerNatural ⟨e.symm⟩⟩
    · exact (hij rfl).elim

end CFSG.Quasithin.ChapterK.Alternating.SevenSmallSpectrum
