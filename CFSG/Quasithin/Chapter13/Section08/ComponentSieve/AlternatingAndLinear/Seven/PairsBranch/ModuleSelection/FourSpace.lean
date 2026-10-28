module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.FourSpace.Parabolic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.FourSpace.PermutationInput
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.FourSpace.PermutationCertificate

/-!
# The four-space plane obstruction

The full stabilizer of a plane in any faithful binary four-dimensional A₇
action has order dividing 576 and index at most 35. The finite permutation
certificate forces a stabilizer containing the even pair stabilizer to
equal it, with index 105, a contradiction.

This argument covers every faithful action, including its dual, without a
representation-classification premise. The kernel-checked permutation
certificate discharges the finite input, giving the unconditional
`fourPlaneExclusion` needed by the module-selection argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.24,
printed p.959/PDF p.976.
-/

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
open Representation.BinaryOffender

/-- The finite permutation certificate suffices uniformly for all faithful
four-dimensional representations and every two-dimensional subspace. -/
public theorem fourPlaneExclusion_of_permutationCertificate
    (hcert : FourSpace.PermutationCertificate) : FourPlaneExclusion := by
  intro V _ _ _ σ hσ hdim S hS hstable
  obtain ⟨hcard, hindex⟩ := FourSpace.planeStabilizer_bounds σ hσ hdim S hS
  have heq := FourSpace.overgroup_eq_of_certificate hcert
    (subspaceStabilizer σ S) hstable hcard
  rw [heq, FourSpace.pair_index_of_certificate hcert] at hindex
  omega

/-- The even stabilizer of the partition `{{0,1},{2,3},{4,5},{6}}` stabilizes
no plane in any faithful binary four-dimensional A₇ representation. -/
public theorem fourPlaneExclusion : FourPlaneExclusion :=
  fourPlaneExclusion_of_permutationCertificate FourSpace.permutationCertificate

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
