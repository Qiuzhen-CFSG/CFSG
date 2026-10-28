module
public import Theory.SpecificGroups.Rudvalis.Multiplier.Universe
public import Theory.PGroupCore

/-!
# Removing a Rudvalis covering center when the two-core vanishes

The native multiplier bound makes the center of a perfect Rudvalis cover
a group of order at most two. It is therefore contained in the two-core.
When that core is trivial, the original central quotient map itself is
an isomorphism; the pointwise formula below preserves its marking.

Source: Aschbacher--Smith I.1.3 and the terminal inspection in 4.4.3,
printed pp.407 and 622--623.
-/

public noncomputable section
namespace Rudvalis.Multiplier
open Subgroup Theory.GroupTheory
variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

/-- The two-core hypothesis removes the entire covering center, with the
resulting isomorphism equal to the specified quotient map on every element. -/
theorem center_eq_bot_and_exists_equiv
    (e : E ⧸ center E ≃* Model) (hcore : pCore 2 E = ⊥) :
    center E = ⊥ ∧ ∃ d : E ≃* Model,
      ∀ x, d x = e (QuotientGroup.mk' (center E) x) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center E := by
    ext x
    change e (QuotientGroup.mk' (center E) x) = 1 ↔ x ∈ center E
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let c : PerfectCentralCovering.Cover E Model :=
    { toMonoidHom := f, surjective := hf, isPerfect := inferInstance,
      ker_le_center := hk.le }
  have hc := cover_kernel_card_le_two_any_universe c
  change Nat.card f.ker ≤ 2 at hc
  rw [hk] at hc
  have hp : IsPGroup 2 (center E) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    have hpos := Nat.card_pos (α := center E)
    refine ⟨1,?_⟩
    have hcases : Nat.card (center E) = 1 ∨ Nat.card (center E) = 2 := by omega
    rcases hcases with h | h <;> simp only [h,pow_one] <;> decide
  have hz : center E = ⊥ := bot_unique (hcore ▸ (show center E ≤ pCore 2 E from
    le_sSup ⟨inferInstance,hp⟩))
  have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp (hk.trans hz)
  exact ⟨hz,MulEquiv.ofBijective f ⟨hi,hf⟩,fun _ => rfl⟩

end Rudvalis.Multiplier
