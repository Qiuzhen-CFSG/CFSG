module

public import Theory.SpecificGroups.PSL3Four.HyperbolicRootRecognition.Reflections

/-!
# The two hyperbolic cross-commutator matrices

The two exact quotient reflections eliminate all but two of the 256 cross
matrices. Each reflection has one of six nonsingular binary shear matrices.
The criterion checks only the sixteen quotient vectors and the square map,
not a group multiplication table. The four small uniqueness calculations
retain the literal reflection formulas needed to preserve both root planes.

Center transitivity alone is insufficient in the hyperbolic case: another
quadratic law has balanced nonzero square fibers but a unique singular plane.
The genuine fixed quotient planes from 45.3 are the essential source input.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 45.3, pp.242–243.
-/

public section
namespace Theory.GroupTheory.HyperbolicRecognition

/-- The two source reflections force one of the actual UT₃(F₄) word laws. -/
theorem twoCases_of_reflections :
    ∀ M : Cross, HasFirstReflection M → HasSecondReflection M → TwoCases M := by
  decide +kernel

theorem aligned_first_frame :
    ∀ P : Frame, FirstReflection alignedMatrix P → P = identityFrame := by
  decide +kernel

theorem aligned_second_frame :
    ∀ P : Frame, SecondReflection alignedMatrix P → P = identityFrame := by
  decide +kernel

theorem crossed_first_frame :
    ∀ P : Frame, FirstReflection crossedMatrix P → P = exchangeFrame := by
  decide +kernel

theorem crossed_second_frame :
    ∀ P : Frame, SecondReflection crossedMatrix P → P = exchangeFrame := by
  decide +kernel

end Theory.GroupTheory.HyperbolicRecognition
