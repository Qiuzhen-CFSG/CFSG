module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.Lifting
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.LocalCentralizer.OrderBound

/-!
# The local J₂ universal-cover kernel has order at most two

Every perfect central extension of the literal involution centralizer is a
quotient of the sixteen-relator group in `LocalCentralizer.Presentation`.
The kernel-checked certificate in `LocalCentralizer.OrderBound` proves that
this presentation is finite of order at most 3840. Since the local group has
order 1920, every such kernel has order at most two. Applying this to the
canonical universal projection discharges the local premise of
`J2UpperBound.LocalReduction`.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 §6.1.
-/

public section
namespace Theory.SpecificGroups.J2HSMultipliers.J2
open LocalCentralizerPresentation PerfectCentralCovering Subgroup
open Sporadic.LeechRelated.J2.ExceptionalParabolics

/-- The explicit presentation order gives the kernel bound for every perfect
central extension of the actual local subgroup, with its quotient map retained. -/
theorem local_kernel_card_le_two_of_presentation_bound
    (hfinite : Finite Presentation) (hcard : Nat.card Presentation ≤ 3840)
    {E : Type*} [Group E] [Group.IsPerfect E]
    (f : E →* Local) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    Nat.card f.ker ≤ 2 := by
  let := hfinite
  have hE : Nat.card E ≤ 3840 :=
    (Nat.card_le_card_of_surjective (coverMap f hf hk) (coverMap_surjective f hf hk)).trans hcard
  have h := f.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, FirstParabolic.card_l₁] at h
  omega

/-- The exact local input consumed by `J2UpperBound.LocalReduction`, conditional
only on the independent finite presentation calculation. -/
theorem local_universal_kernel_card_le_two_of_presentation_bound
    (hfinite : Finite Presentation) (hcard : Nat.card Presentation ≤ 3840) :
    Nat.card (universalProjection Seed.l₁).ker ≤ 2 := by
  let : Group.IsPerfect Seed.l₁ := FirstParabolic.CoverSquareOrbit.l₁_isPerfect
  exact local_kernel_card_le_two_of_presentation_bound hfinite hcard _
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- The universal perfect central cover of the literal order-1920 involution
centralizer in J₂ has kernel of order at most two. -/
theorem local_universal_kernel_card_le_two :
    Nat.card (universalProjection Seed.l₁).ker ≤ 2 :=
  local_universal_kernel_card_le_two_of_presentation_bound
    presentation_finite_card_le.1 presentation_finite_card_le.2

end Theory.SpecificGroups.J2HSMultipliers.J2
