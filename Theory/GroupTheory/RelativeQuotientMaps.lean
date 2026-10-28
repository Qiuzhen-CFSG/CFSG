module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Inclusions and projections of relative subgroup quotients

An inclusion `C ≤ H` induces an injection `C/(U ∩ C) → H/(U ∩ H)`.
Increasing the denominator from `U` to `W` gives a surjection whose
kernel is precisely the image of `W ∩ C`. Only normality inside the
respective numerator is needed. In particular these maps make `C/W`
a subquotient of `H/U` without requiring `W` to be normal in `H`.

These are the elementary quotient maps underlying the comparison of
the two chief-factor filtrations in Aschbacher–Smith, Lemma 13.8.33,
printed p.968 (1 March 2004 manuscript).
-/

public section

namespace QuotientGroup

open Subgroup

variable {G : Type*} [Group G]

theorem quotientMapSubgroupOfOfLe_injective (C H U : Subgroup G)
    [(U.subgroupOf C).Normal] [(U.subgroupOf H).Normal] (hCH : C ≤ H) :
    Function.Injective (quotientMapSubgroupOfOfLe (le_refl U) hCH) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H x =>
    apply (QuotientGroup.eq_one_iff _).mpr
    change QuotientGroup.mk' (U.subgroupOf H) (inclusion hCH x) = 1 at hx
    exact (QuotientGroup.eq_one_iff (inclusion hCH x)).mp hx

theorem quotientMapSubgroupOfOfLe_surjective (C U W : Subgroup G)
    [(U.subgroupOf C).Normal] [(W.subgroupOf C).Normal] (hUW : U ≤ W) :
    Function.Surjective (quotientMapSubgroupOfOfLe hUW (le_refl C)) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H y => exact ⟨QuotientGroup.mk' (U.subgroupOf C) y, rfl⟩

theorem ker_quotientMapSubgroupOfOfLe (C U W : Subgroup G)
    [(U.subgroupOf C).Normal] [(W.subgroupOf C).Normal] (hUW : U ≤ W) :
    (quotientMapSubgroupOfOfLe hUW (le_refl C)).ker =
      (W.subgroupOf C).map (QuotientGroup.mk' (U.subgroupOf C)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    constructor
    · intro hx
      change QuotientGroup.mk' (W.subgroupOf C) x = 1 at hx
      exact mem_map.mpr ⟨x, (QuotientGroup.eq_one_iff x).mp hx, rfl⟩
    · rintro ⟨y, hy, he⟩
      rw [← he]
      exact (QuotientGroup.eq_one_iff y).mpr hy

end QuotientGroup
