module
public import Theory.GroupTheory.Signalizer.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Invariant subgroups of signalizer subgroups

An invariant subgroup of an odd solvable signalizer subgroup is again a
signalizer subgroup for the same supplied action. Its order divides the
original subgroup order, solvability passes through the inclusion, and
its fixed subgroups satisfy the same bounds by containment.

This is the downward-closure observation following the definition of
signalizer subgroups in Kurzweil–Stellmacher, *The Theory of Finite Groups*,
§11.1, printed p.304. It supports restriction, quotient lifting, and the
maximal-intersection argument for transitivity.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

public theorem IsSignalizerSubgroup.mono {θ : TwoSignalizerFamily A G}
    {U V : Subgroup G} (hU : θ.IsSignalizerSubgroup U) (hVU : V ≤ U)
    (hV : IsInvariant A G V) : θ.IsSignalizerSubgroup V := by
  let _ := hU.2.1
  refine ⟨hU.1.of_dvd_nat (Subgroup.card_dvd_of_le hVU),
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hVU), hV, ?_⟩
  intro a
  exact (inf_le_inf_right _ hVU).trans (hU.2.2.2 a)


end Theory.GroupTheory.TwoSignalizerFamily
