module

public import Mathlib.GroupTheory.Sylow

/-!
# Overgroups of a self-normalizing Sylow subgroup

If a subgroup contains a Sylow subgroup whose ambient normalizer is itself,
then it too is self-normalizing. Apply the Frattini argument to the subgroup
inside its own normalizer; the Sylow normalizer supplies no extra elements.
All normality used here is relative to that normalizer.

Source: the Frattini argument, `Sylow.normalizer_sup_eq_top'`.
-/

namespace Subgroup

/-- Every overgroup of a self-normalizing Sylow subgroup is self-normalizing. -/
public theorem normalizer_eq_of_self_normalizing_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : normalizer (P : Set G) = (P : Subgroup G))
    (H : Subgroup G) (hPH : (P : Subgroup G) ≤ H) :
    normalizer (H : Set G) = H := by
  let N := normalizer (H : Set G)
  have hPN : (P : Subgroup G) ≤ N := hPH.trans H.le_normalizer
  let Q : Sylow p N := P.subtype hPN
  have hQH : (Q : Subgroup N) ≤ H.subgroupOf N := fun _ hx => hPH hx
  have : (H.subgroupOf N).Normal := H.normal_in_normalizer
  have hfr := Q.normalizer_sup_eq_top' hQH
  have hn : normalizer (Q : Set N) = (Q : Subgroup N) := by
    change normalizer ((P : Subgroup G).subgroupOf N : Set N) = _
    rw [← subgroupOf_normalizer_eq hPN]
    change (normalizer (P : Set G)).subgroupOf N = _
    rw [hP]
    rfl
  rw [hn, sup_of_le_right hQH] at hfr
  have hNH : N ≤ H := subgroupOf_eq_top.mp hfr
  exact le_antisymm hNH H.le_normalizer

end Subgroup
