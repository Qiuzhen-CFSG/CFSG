module

public import GorensteinWalter.Section2.Basic
public import GorensteinWalter.Section3.FirstCaseCyclicTwoCore
public import GorensteinWalter.Section3.FirstCaseTwoCoreKleinFour
public import GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import GorensteinWalter.Suzuki.FirstCaseIsASeven

/-!
# Section 3: elimination of the first case
-/

noncomputable section

open Matrix

namespace GorensteinWalter

universe u

/-! ## Section 3: elimination of the first case -/

/-- A group isomorphic to `A₇` is a `D`-group. -/
public theorem isDGroup_of_isomorphic_aSeven
    {G : Type u} [Group G] [Finite G]
    (e : Nonempty (G ≃* alternatingGroup (Fin 7))) :
    IsDGroup G := by
  exact isDGroup_of_mulEquiv_aSeven e

/-- Section 3 eliminates case (1) of Theorem 2.10. -/
public theorem firstCase_impossible
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c) :
    False := by
  by_cases hcyclic : twoCoreOf c.Hhat ≤ c.S0
  · exact firstCase_cyclicTwoCore_impossible hmin c hfirst hcyclic
  · have hA7 := firstCase_isASeven hmin c hfirst
    exact hmin.2.1 (isDGroup_of_isomorphic_aSeven hA7)

end GorensteinWalter
