module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024RefinedCountData

/-!
# Conjugacy witnesses for refined Ree two counts

Kernel reduction verifies each internal conjugator and the order-four flags
of the representatives. The multiplication and parametrizations are proved
in `Order1024RefinedCountModel`; the witness data use Shinoda (1975), (2.3).
-/

@[expose] public section
namespace ReeTwo.SylowModel.RefinedCounting
set_option maxRecDepth 32768

theorem countConjugators_valid : ∀ c n,
    countMul (countElement c n) (countElement c (countConjugators c n)) =
      countMul (countElement c (countConjugators c n))
        (countElement c (countReps c (countClasses c n))) := by
  decide +kernel

theorem countFour_valid : ∀ c j,
    countFourTest (countElement c (countReps c j)) = countFour c j := by
  decide +kernel

end ReeTwo.SylowModel.RefinedCounting
