module

public import GorensteinWalter.Section3.FirstCaseCountAssemble
public import GorensteinWalter.Section3.FirstCaseKleinB3Zero
import Mathlib.Tactic


noncomputable section

namespace GorensteinWalter

universe u

/-! The Klein-branch counting package is now unconditional. -/
public theorem firstCase_klein_count_data_nonempty
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    Nonempty (FirstCaseCountData c) := by
  exact firstCase_count_data_nonempty_of_b3_zero hmin c hfirst hklein
    (firstCase_klein_b3_zero hmin c hfirst hklein)

end GorensteinWalter
