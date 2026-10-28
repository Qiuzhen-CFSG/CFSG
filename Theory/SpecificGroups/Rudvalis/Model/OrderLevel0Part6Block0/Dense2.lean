module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row50
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row51
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row52
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row53
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row54
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row55
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row56
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row57
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row58
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row59
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row60
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row61
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row62
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row63
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row64
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row65
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row66
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row67
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row68
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row69
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row70
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row71
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row72
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row73
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense2.Row74
import Mathlib.Tactic.FinCases

/-!
# Rudvalis block-0 dense transitions 50–74

The row certificates verify each transition at all 4060 points through the
certified factor maps and the 203-by-20 slice transfer. The words are decoded
from the ATLAS witnesses in `OrderLevel0Data` and `FactorWords`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense2
set_option Elab.async false

/-- The third quarter of the dense block-0 transition certificates. -/
public theorem checked (k : Fin 25) :
    stepCheck (FactorWords.row ⟨k.val + 50, by omega⟩).1
      (FactorWords.row ⟨k.val + 50, by omega⟩).2 := by
  fin_cases k
  · exact Row50.checked
  · exact Row51.checked
  · exact Row52.checked
  · exact Row53.checked
  · exact Row54.checked
  · exact Row55.checked
  · exact Row56.checked
  · exact Row57.checked
  · exact Row58.checked
  · exact Row59.checked
  · exact Row60.checked
  · exact Row61.checked
  · exact Row62.checked
  · exact Row63.checked
  · exact Row64.checked
  · exact Row65.checked
  · exact Row66.checked
  · exact Row67.checked
  · exact Row68.checked
  · exact Row69.checked
  · exact Row70.checked
  · exact Row71.checked
  · exact Row72.checked
  · exact Row73.checked
  · exact Row74.checked

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense2
