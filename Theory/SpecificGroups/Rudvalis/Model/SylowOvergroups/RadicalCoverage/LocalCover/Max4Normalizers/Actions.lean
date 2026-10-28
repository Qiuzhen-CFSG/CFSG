module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter0
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter1
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter2
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter3
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter4
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter5
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter6
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Letter7
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Element0
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Element1
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Element2
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Element3
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Element4
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers.Actions.Element5
import Mathlib.Tactic.FinCases

/-!
# Certified point actions of the fixed Rudvalis local words

Each finite point equation is kernel-checked against the preserved ATLAS words.
The bounded blocks cover all 4060 points. See `Max4Normalizers/source/actions.py`
and `SylowOvergroups.Definitions` for witness generation and ATLAS attribution.
These are point-action comparisons, independent of any subgroup order.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers

set_option maxRecDepth 30000
set_option Elab.async false

public theorem letterMap_eq (i : Fin 8) (x : Fin 4060) :
    letterMap i x = localLetter i • x := by
  have h : letterMap i x = tableLocalLetter i x := by
    fin_cases i
    · exact letter0_eq x
    · exact letter1_eq x
    · exact letter2_eq x
    · exact letter3_eq x
    · exact letter4_eq x
    · exact letter5_eq x
    · exact letter6_eq x
    · exact letter7_eq x
  rw [tableLocalLetter_eq] at h
  exact h

public theorem wordMap_eq (w : List (Fin 8)) (x : Fin 4060) :
    wordMap w x = localWord w • x := by
  induction w with
  | nil => exact (one_smul _ _).symm
  | cons i w ih =>
    change letterMap i (wordMap w x) = (localLetter i * localWord w) • x
    rw [letterMap_eq, ih, mul_smul]

public theorem elementMap_eq (i : Fin 6) (x : Fin 4060) :
    elementMap i x = elementaryGenerator i • x := by
  have h : elementMap i x = wordMap (elementaryWords i) x := by
    fin_cases i
    · exact element0_eq x
    · exact element1_eq x
    · exact element2_eq x
    · exact element3_eq x
    · exact element4_eq x
    · exact element5_eq x
  exact h.trans (wordMap_eq _ _)

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
