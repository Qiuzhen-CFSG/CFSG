module

public import GorensteinWalter.Section4.SecondCaseAlternatingIndexBoundCore
public import GorensteinWalter.Section4.SecondCaseA7SmallIndexAbsurd

/-!
# The final A₇ count endpoint

This wrapper separates the finite-count constructor from its final use: once
the three source counts are packaged as `SecondCaseA7CountData`, the generic
fiber estimate gives `M.index ≤ 7`, and the A₇ quotient/maximality endpoint
closes the contradiction.
-/

namespace GorensteinWalter

universe u

public theorem secondCase_a7_impossible_of_countData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (counts : SecondCaseA7CountData w.M) : False := by
  exact secondCase_a7_small_index_absurd hmin c w d hA7 hmodel
    (index_le_seven_of_countData w.M counts)

end GorensteinWalter
