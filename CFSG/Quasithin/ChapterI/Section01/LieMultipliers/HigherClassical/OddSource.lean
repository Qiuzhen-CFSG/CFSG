module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL4.OddCentralKernels
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.OddCentralKernels
public import Theory.GroupTheory.Covering

/-!
# Degree-four odd-center source deductions

The degree-four step of Aschbacher–Smith A.2.17, printed p.39, precedes the
Fermat/Mersenne restrictions. Its eventual source corollary must therefore
cover every odd prime. Here the ternary linear case is proved outright by
cyclic-Sylow transfer and O₃(L)=1. For the ternary unitary case the currently
proved order bound reduces the center to a five-group; excluding five and
the larger-prime cases remain separate obligations.

Each result uses the original quotient L/Z(L), an actual model equivalence,
and the given odd center and trivial defining core. The unitary coefficient
field has order nine. No natural-cover lifting or universal-cover hypothesis
is assumed, and no claim of the full I.1.4 multiplier table is made.
-/

public section

open Subgroup PerfectCentralCovering Theory.GroupTheory
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

namespace CFSG.Quasithin.ChapterI.LieMultipliers.HigherClassical.OddSource

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

/-- The p=3 linear source branch, with every source premise discharged. -/
theorem center_eq_bot_of_isPSL_four_three
    (hodd : Odd (Nat.card (center L))) (hcore : pCore 3 L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 4 3) : center L = ⊥ := by
  rcases hmodel with ⟨F, hfield, hfinite, hF, ⟨e⟩⟩
  let := hfield
  let := hfinite
  simpa only [centerQuotientCover_ker] using
    Matrix.PSL4.OddCentralKernels.ker_eq_bot_of_odd_of_threeCore_eq_bot
      hF (centerQuotientCover e) (by simpa only [centerQuotientCover_ker] using hodd) hcore

/-- The p=3 unitary source branch reduces to its still-unexcluded five-part. -/
theorem center_isFiveGroup_of_isPSU_four_three
    (hodd : Odd (Nat.card (center L))) (hcore : pCore 3 L = ⊥)
    (hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 4 3) :
    IsPGroup 5 (center L) := by
  rcases hmodel with ⟨F, hfield, hfinite, J, hF, _hconj, ⟨e⟩⟩
  let := hfield
  let := hfinite
  have hk :=
    OddCentralKernels.kernel_isFiveGroup_of_odd_of_threeCore_eq_bot
      J (by simpa using hF) (centerQuotientCover e)
      (by simpa only [centerQuotientCover_ker] using hodd) hcore
  exact hk.of_equiv (MulEquiv.subgroupCongr (centerQuotientCover_ker e))

end CFSG.Quasithin.ChapterI.LieMultipliers.HigherClassical.OddSource
