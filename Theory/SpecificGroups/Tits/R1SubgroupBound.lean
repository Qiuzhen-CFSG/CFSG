module

public import Theory.SpecificGroups.Tits.R1DihedralBound
public import Theory.SpecificGroups.Tits.R1CosetCover
public import Theory.GroupTheory.PresentedGroupBounds

/-!
# Transferring a certified local coset bound to Parrott's `R₁`

The certified cover by 1024 cosets of the local two-involution subgroup bounds
the local presentation by `10 * 1024`. Its surjection onto the subgroup generated
without `r8` transfers this upper bound to the actual Parrott presentation.

Source: Parrott, “A Characterization of the Tits' Simple Group” (1972), §5,
p. 683; see `refs/original/n-group-global/parrott-tits-presentation.md`.
-/

namespace Tits

/-- A certified local coset cover suffices for the required subgroup bound. -/
public theorem parrottR1Subgroup_bound_of_cosetCover
    (C : Subgroup.GeneratorCosetCover parrottR1DihedralSubgroup
      parrottR1Generator (Fin 1024)) :
    Finite parrottR1Subgroup ∧ Nat.card parrottR1Subgroup ≤ 10240 := by
  obtain ⟨hfinite, hcard⟩ := parrottR1DihedralSubgroup_finite_card_le
  let := hfinite
  obtain ⟨hlocal, hbound⟩ := C.finite_card_le parrottR1_closure_range_generator
  apply parrottR1Subgroup_bound_of_local
  refine ⟨hlocal, hbound.trans ?_⟩
  simpa using Nat.mul_le_mul_right 1024 hcard

/-- Parrott's subgroup generated without `r8` is finite of order at most 10240. -/
public theorem parrottR1Subgroup_finite_card_le :
    Finite parrottR1Subgroup ∧ Nat.card parrottR1Subgroup ≤ 10240 :=
  parrottR1Subgroup_bound_of_cosetCover parrottR1CosetCover

end Tits
