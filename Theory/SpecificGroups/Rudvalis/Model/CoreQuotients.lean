module

public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.SurjectiveKernels
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max4Action
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max4Image
public import Theory.SpecificGroups.Rudvalis.Model.CoreQuotients.Max6Action

/-!
# Assembly of the intrinsic Rudvalis local core quotients

The marked max4 conjugation action on the actual eight-group has full image,
identifying its relative centralizer with its intrinsic two-core. The max6
action on five certified blocks also has full image. The certified local
orders identify both kernels with the intrinsic two-cores.

This module reexports the resulting equivalences `max4QuotientEquiv` and
`max6FiveQuotientEquiv`, including their literal quotient-projection laws.
Neither equivalence requires simplicity of the ambient Rudvalis model or a
split-extension assertion. The conditional interfaces below are preserved.
Source: GLS3 Table 5.3r and its max4 justification, printed pp.291–292.
These are the two marked local quotients used in the Rudvalis branch of
Aschbacher–Smith E.1.14(5), p.214, citing Asc82a, Lemma 4.9.
-/

namespace Rudvalis.CoreQuotients

open Subgroup SylowOvergroups SylowOvergroups.RadicalCoverage.LocalCover

/-- Full image makes the actual max4 centralizer exactly the intrinsic two-core. -/
public theorem max4_centralizer_eq_pCore_of_full_image
    (h : Function.Surjective max4EightAction) :
    (centralizer (elementary 2 : Set Model)).subgroupOf max4 = pCore 2 max4 := by
  rw [← max4EightAction_ker, ← max4LinearAction_ker]
  exact max4_kernel_eq_pCore max4LinearAction (max4LinearAction_surjective_of_eightAction h)

/-- The max4 quotient identification obtained from the literal eight-group action. -/
public noncomputable def max4QuotientEquivOfFullImage
    (h : Function.Surjective max4EightAction) :
    (max4 ⧸ pCore 2 max4) ≃* Matrix.PSL3Two.PSL :=
  max4QuotientEquivOfSurjective max4LinearAction
    (max4LinearAction_surjective_of_eightAction h)

end Rudvalis.CoreQuotients
