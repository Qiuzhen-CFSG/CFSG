module
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.OddThree
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.BinaryThree

/-!
# Discharging both classical families of the nonnormal-component sieve

The odd signed-degree-three involution centralizer and binary degree-three
Borel computations supply the corresponding entire input families. The
catalogue therefore retains only the independent positive local cubic
rank facts for the remaining finite and binary models.

Source: Aschbacher–Smith A.1.34(3), A.3.8(1–2), pp.29–30 and45–46.
-/

public section
namespace CFSG.Quasithin.ChapterA.QTComponents
variable {S : Type*} [Group S] [Finite S]

/-- The signed odd-degree-three local computations supply their entire
row-input family on the actual carrier. -/
theorem oddThreeBudgetInput : OddThreeBudgetInput S := by
  intro p hp ho unitary hm hr
  cases unitary with
  | false => exact linear_three_odd_false hr p hp ho hm
  | true => exact unitary_three_odd_false hr p hp ho hm

/-- The binary degree-three Borel computation supplies its entire family,
including the actual PSL₂(7) endpoint. -/
theorem binaryThreeBudgetInput : BinaryThreeBudgetInput S := by
  intro n hn hm hr
  exact BinaryThree.binary_model_seven hr hn hm

/-- Only positive local cubic ranks in the remaining rows remain explicit. -/
theorem nonnormal_model_of_budget_of_remaining_local
    (hlocal : RemainingLocalInput S) (hr : OddRankBudget S)
    (hm : Chapter1.Section02.LocalModels.TheoremCModel S) : NonnormalModel S :=
  nonnormal_model_of_budget oddThreeBudgetInput binaryThreeBudgetInput hlocal hr hm

end CFSG.Quasithin.ChapterA.QTComponents
