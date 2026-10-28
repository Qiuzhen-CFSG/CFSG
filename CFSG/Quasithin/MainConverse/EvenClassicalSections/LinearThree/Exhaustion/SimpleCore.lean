module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Structure
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.SimpleCore.Reduction

/-!
# Assembly of simple-core recognition from the two intrinsic calculations

The finite-group reduction constructs the simple normal subgroup and proves
its centralizer trivial from a solvable-centralizer calculation. Recognition
then needs only identify this already constructed subgroup. The two remaining
calculations are independent: the model calculation may take simplicity,
normality and trivial centralizer as explicit hypotheses while the other
calculation supplies the centralizer input used to establish those properties.

The theorem below is conditional. It does not discharge the `hcore` argument
of `proper_subgroup_envelope_of_core_inputs` until both matrix calculations
are supplied. Neither a K-group hypothesis nor a unitary section theorem is
an acceptable source of those calculations.

Source: GLS3, Theorem 6.5.3(e–i), `refs/KGroup/GLS3/chapter6.tex`.
Its printed recognition proof uses K; the characteristic-two application
requires intrinsic model recognition in its place.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open scoped MatrixGroups

/-- Construct the core using component centralizers, then identify its actual model.
The hypotheses concern two distinct calculations and neither assumes the existence
of a recognized normal core. The unconditional source assembly must prove both. -/
public theorem hasRecognizedCore_of_component_centralizers_and_models
    (F : Type) [Field F] [Finite F] (U : Subgroup PSL(3,F))
    (hgeom : ¬ FixesPointOrDual F U) (hab : ¬ HasAbelianNormal U)
    (hcentralizer : ∀ N : Subgroup U, N.IsSubnormal → IsSimpleGroup N →
      ¬ Group.IsSolvable N → Group.IsSolvable (Subgroup.centralizer (N : Set U)))
    (hmodel : ∀ (N : Subgroup U) [N.Normal] [IsSimpleGroup N],
      ¬ Group.IsSolvable N → Subgroup.centralizer (N : Set U) = ⊥ → CoreModel N) :
    HasRecognizedCore U := by
  let := nontrivial_of_not_fixesPointOrDual F U hgeom
  obtain ⟨N, hn, hs, hns, hc⟩ :=
    exists_simple_normal_of_solvable_component_centralizers hab hcentralizer
  let := hn
  let := hs
  exact ⟨N, hn, hs, hns, hc, hmodel N hns hc⟩

end CFSG.Quasithin.MainConverse.LinearThreeSections
