module

public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexPlane

/-!
# Separation through the concrete seven-dimensional Lyons plane

The local subgroup lies in the stabilizer of the displayed plane once its two
local matrix identities are certified. Consequently a lower bound for the
plane's orbit is a lower bound for the subgroup index. This separates the
finite matrix calculations from the geometric orbit calculation; neither
requires a coverage certificate, the order of the local subgroup, or an
assumed ambient order or simplicity theorem.

The concrete matrix identities and the orbit lower bound remain explicit
premises here. This module retains their final assembly. Source matrices and
subgroup words are documented in `Atlas111Source/` and `Atlas111OrderSource/`;
the plane's exploratory data are in `Atlas111SeparationSource/`.
-/

namespace Lyons.OrderCertificate

open scoped Pointwise

/-- The exact ATLAS-word subgroup fixes the plane if its generators do. -/
public theorem localSubgroup_le_separationPlane_stabilizer
    (ha : matrixRepresentation localA * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionA)
    (hb : matrixRepresentation localB * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionB) :
    localSubgroup ≤ MulAction.stabilizer LyonsGroup separationPlane := by
  apply (Subgroup.closure_le _).mpr
  exact Set.pair_subset_iff.mpr (separationPlane_fixed_of_matrix_identities ha hb)

/-- A geometric orbit bound supplies the required concrete subgroup-index bound. -/
public theorem le_localIndex_of_separationPlane_orbit
    (ha : matrixRepresentation localA * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionA)
    (hb : matrixRepresentation localB * separationPlaneColumns =
      separationPlaneColumns * separationPlaneActionB)
    (horbit : 8835156 ≤ (MulAction.orbit LyonsGroup separationPlane).ncard) :
    8835156 ≤ localSubgroup.index := by
  rw [← MulAction.index_stabilizer] at horbit
  exact horbit.trans (Subgroup.index_antitone
    (localSubgroup_le_separationPlane_stabilizer ha hb))

/-- Explicit distinct translates are one way to certify the plane's orbit bound. -/
public theorem le_separationPlane_orbit_of_injective_translates
    (r : Fin 8835156 → LyonsGroup)
    (hinj : Function.Injective (fun i => r i • separationPlane)) :
    8835156 ≤ (MulAction.orbit LyonsGroup separationPlane).ncard := by
  let f : Fin 8835156 → MulAction.orbit LyonsGroup separationPlane :=
    fun i => ⟨r i • separationPlane, MulAction.mem_orbit separationPlane (r i)⟩
  have hf : Function.Injective f := fun i j h => hinj (congrArg Subtype.val h)
  have : Finite (MulAction.orbit LyonsGroup separationPlane) :=
    (Finite.finite_mulAction_orbit separationPlane).to_subtype
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf

end Lyons.OrderCertificate
