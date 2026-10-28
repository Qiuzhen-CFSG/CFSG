module

public import Theory.GroupTheory.PGroup.CharacteristicSeriesAutomorphisms
public import Theory.GroupTheory.CentricRadicalObstructions

/-!
# Characteristic-series obstructions to intrinsic radicality

A normalizer element of a centric intrinsic radical p-subgroup belongs to
that subgroup if it acts trivially on a three-step characteristic series.
The series kernel is a normal p-subgroup of the full automorphism group,
so intrinsic radicality makes the action inner; centricity finishes.

Source: the elementary automorphism-kernel argument proved in
`PGroup.CharacteristicSeriesAutomorphisms`.
-/

namespace Subgroup

/-- Trivial action on a three-step characteristic series detects membership
in a centric intrinsic radical subgroup. The two intermediate subgroups are
characteristic in U; no characteristicity inside each other is required. -/
public theorem mem_of_intrinsic_radical_of_characteristic_series
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (U : Subgroup G) (hU : IsPGroup p U)
    (hcent : centralizer (U : Set G) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore p (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (C D : Subgroup U) [C.Characteristic] [D.Characteristic]
    (g : normalizer (U : Set G))
    (hUC : ∀ x : U, x⁻¹ * U.normalizerMonoidHom g x ∈ C)
    (hCD : ∀ x ∈ C, x⁻¹ * U.normalizerMonoidHom g x ∈ D)
    (hD : ∀ x ∈ D, U.normalizerMonoidHom g x = x) : (g : G) ∈ U := by
  let K := characteristicStepKernel ⊤ C ⊓ characteristicStepKernel C D ⊓
    characteristicStepKernel D ⊥
  have hle : K ≤ pCore p (MulAut U) :=
    le_sSup ⟨inferInstance, isPGroup_threeStepKernel hU C D⟩
  apply mem_of_normalizerMonoidHom_mem_inner U hcent g
  apply hrad
  refine ⟨⟨g, rfl⟩, hle ⟨⟨fun x _ => hUC x, hCD⟩, ?_⟩⟩
  intro x hx
  change x⁻¹ * U.normalizerMonoidHom g x = 1
  rw [hD x hx, inv_mul_cancel]

end Subgroup
