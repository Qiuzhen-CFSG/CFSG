module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.Checks


/-!
# Injectivity of the checked binary coefficient system

Each packed row represents a linear form in the 400 matrix entries. The checked
left inverse recovers every entry from the selected equations, so the two matrix
sums are jointly injective over every field of characteristic two. This theorem
is a coefficient calculation; `Injectivity` connects it to actual Bruhat actors
under the explicit coordinate hypothesis.

Source of the equations: Huppert II.10.12; witness provenance is in `source/README.md`.
-/

@[expose] public section

open scoped BigOperators Matrix
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.Certificate
open Data
variable {K : Type*} [Field K] [CharP K 2]

def system (X : Matrix (Fin 20) (Fin 20) K) (s : Fin 2) : Matrix (Fin 20) (Fin 20) K :=
  ∑ t : Fin 5, matrix (leftRows s t) * X * matrix (rightRows s t)

theorem evaluate_systemRow (X : Matrix (Fin 20) (Fin 20) K)
    (s : Fin 2) (r c : Fin 20) :
    evaluate X (systemRow s r c) = system X s r c := by
  simp only [systemRow, evaluate_xorList, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, evaluate_tensorRow, system, Matrix.sum_apply]

/-- The two retained matrix sums determine all 400 entries over every
characteristic-two field. This is solely a coefficient calculation. -/
theorem system_injective : Function.Injective (system (K := K)) := by
  intro X Y h
  apply sub_eq_zero.mp
  have hrow (i : Fin 400) : evaluate (X - Y) equationData[i.val]! = 0 := by
    rw [selected_equations, evaluate_sub, evaluate_systemRow, evaluate_systemRow]
    rw [congrFun h (position i).1, sub_self]
  have hall (a : Nat) (ha : a ∈ equationData.toList) : evaluate (X - Y) a = 0 := by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ha)
    have hi' : i < 400 := by simpa only [equationData_size] using hi
    have hh := hrow ⟨i, hi'⟩
    change evaluate (X - Y) equationData[i]! = 0 at hh
    rwa [getElem!_pos equationData i hi] at hh
  apply Matrix.ext
  intro r c
  have ht := evaluate_listProduct_eq_zero (X - Y) inverseData[(flat r c).val]! 0
    equationData.toList hall
  rw [inverse_checked] at ht
  change evaluate (X - Y) (2 ^ (20 * r.val + c.val)) = 0 at ht
  rw [evaluate_single] at ht
  exact ht

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.Certificate
