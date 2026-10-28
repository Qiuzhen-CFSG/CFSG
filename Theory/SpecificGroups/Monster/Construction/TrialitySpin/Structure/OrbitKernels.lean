module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Actions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.UnionKernel
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Axis2Kernels

/-!
# Conditional triality axis actions and orbit kernels

This interface assembles the permutation results under exactly the three
premises of `OrbitPresentation`: normal-form bijectivity and the normal-form
membership tests for `Q1` and `NPlus`.

* `N1_preserves_A` and `N1_commutes_k1` give the action on the individual
  two-point `k1` orbits of `A2 ∪ A3`. Its kernel is `J` by
  `fixesK1Orbits_iff_mem_J`, and `Q1_inf_J` proves `Q1 ⊓ J = K1`.
* `mem_Q1_iff_axis1_code` characterizes `Q1` by preservation of axis 1 and
  its actual Golay projection.
* `NPlus_preserves_axes` preserves each of `A2` and `A3`. The theorems
  `fixesAxis2K1Orbits_iff_mem_axis2K1Kernel` and
  `fixesAxis2K3Orbits_iff_mem_axis2K3Kernel` identify the two axis-2 kernels
  with the specified three-generator subgroups. Their orbit relations remain
  distinct: `k1` multiplies the loop coordinate by Ω, and `k3` by −Ω.

The proofs compute normal-form actions, use faithfulness of the Golay action
modulo the all-ones line, and identify the remaining central coordinates.
For the single-axis calculation, the proved radical theorem for the Golay
triple form restricts the second loop coordinate to that line.

These are the conditional permutation ingredients of Aschbacher,
*Sporadic Groups*, Lemmas 14.4 and 14.6, printed pp. 61–63, and
Lemma 27.3(5–6), printed p. 146. The presentation premises must still be
discharged by the normal-form development; the real representations and final
source-theorem assembly belong to their consumers.
-/
