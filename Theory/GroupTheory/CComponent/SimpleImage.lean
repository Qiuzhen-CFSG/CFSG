module

public import Theory.GroupTheory.CComponent.Structure

/-!
# Selecting a C-component over a simple image

When C-components generate the solvable residual, a surjection onto a
nontrivial perfect simple group is already onto on one actual C-component.
The residual maps onto the target, so at least one component has nontrivial
image; subnormality and simplicity then identify that image with the target.
No condition on the kernel is used.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Proposition 1.2.1(1), p.503, and its use in Lemma 14.4.8(2), p.1009.
-/

public section
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- Residual generation lifts a perfect simple image through an arbitrary kernel. -/
theorem exists_cComponent_surjects_of_layer_eq_residual
    [IsSimpleGroup D] [Group.IsPerfect D]
    (hgen : cComponentLayer G = solvableResidual G)
    (f : G →* D) (hf : Function.Surjective f) :
    ∃ C : Subgroup G, C.IsCComponent ∧ C.map f = ⊤ := by
  have hr : (cComponentLayer G).map f = ⊤ := by
    rw [hgen, map_solvableResidual_eq f hf, solvableResidual_eq_top]
  have hex : ∃ C : Subgroup G, C.IsCComponent ∧ C.map f ≠ ⊥ := by
    by_contra hn
    have hz : (cComponentLayer G).map f ≤ ⊥ := by
      apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro C hC
      apply map_le_iff_le_comap.mp
      have hc : C.map f = ⊥ := by
        by_contra hc
        exact hn ⟨C, hC, hc⟩
      exact hc.le
    rw [hr] at hz
    exact top_ne_bot (le_bot_iff.mp hz)
  obtain ⟨C, hC, hn⟩ := hex
  exact ⟨C, hC, ((hC.subnormal.map hf).eq_bot_or_top_of_isSimpleGroup
    inferInstance).resolve_left hn⟩

omit [Finite G] in
/-- The selected subgroup covers the source modulo the literal kernel. -/
theorem sup_ker_eq_top_of_map_eq_top (f : G →* D) {C : Subgroup G}
    (hC : C.map f = ⊤) : C ⊔ f.ker = ⊤ := by
  have h := congrArg (comap f) hC
  simpa only [comap_map_eq, comap_top] using h

end Subgroup
