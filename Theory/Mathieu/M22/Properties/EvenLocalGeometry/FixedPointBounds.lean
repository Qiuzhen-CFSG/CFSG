module

public import Theory.Mathieu.M22.Properties.EvenLocalGeometry
public import Theory.Mathieu.M22.Properties.FixedHexads

/-!
# Bounds and invariance of common fixed points in M₂₂

A nontrivial elementary two-subgroup contains an involution. Its common
fixed-point set is contained in the fixed hexad of that involution, hence
has at most six points. Relative normality in a subgroup makes the common
fixed points invariant under that subgroup.

These facts reduce the local coverage calculation in Aschbacher–Smith,
Theorem 0.1.2(5), printed pp.3–4, to finite orbit and point-fixation checks.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22EvenGeometry
open Subgroup
open scoped Pointwise

/-- Any nontrivial elementary two-subgroup fixes at most six points in common. -/
theorem commonFixedPoints_card_le_six (R : Subgroup M22) (hR : R ≠ ⊥)
    [IsElementaryAbelian 2 R] : (commonFixedPoints R).card ≤ 6 := by
  obtain ⟨r, hr, hne⟩ := R.bot_or_exists_ne_one.resolve_left hR
  have hord : orderOf r = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian r hr) hne
  have hsub : commonFixedPoints R ⊆ m22FixedPoints r := by
    intro a ha
    exact (mem_m22FixedPoints r a).mpr ((mem_commonFixedPoints R a).mp ha r hr)
  exact (Finset.card_le_card hsub).trans_eq
    (m22Block_card _ (m22FixedPoints_mem_blocks r hord))

/-- A normal subgroup's fixed points are invariant under its overgroup. -/
theorem le_commonFixedPoints_stabilizer_of_normal {P : Subgroup M22}
    (R : Subgroup P) [R.Normal] :
    P ≤ MulAction.stabilizer M22 (commonFixedPoints (R.map P.subtype)) := by
  apply le_trans ?_ (normalizer_le_fixedPoints_stabilizer _)
  intro g hg
  apply le_normalizer_map P.subtype
  refine ⟨⟨g, hg⟩, ?_, rfl⟩
  rw [normalizer_eq_top]
  exact mem_top _

end Sporadic.Mathieu.M22EvenGeometry
