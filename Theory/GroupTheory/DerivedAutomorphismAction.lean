module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Faithfulness and coverage of conjugation on a derived subgroup

If `G'` has trivial center, its ambient centralizer is `Z(G)`: the
commutators of that normal centralizer with `G` lie in its intersection
with `G'`, which is trivial. Thus a centerless `G` acts faithfully on `G'`.

For any self-centralizing normal subgroup `N` of a finite group `G`, an
upper bound `|Out(N)| ≤ |G:N|` makes conjugation onto `Aut(N)` surjective.
Indeed `|Aut(N)| = |Inn(N)| |Out(N)| ≤ |N| |G:N| = |G|`, and the action
is already injective. This needs neither an order formula nor simplicity.

These elementary criteria separate the group theory from the concrete
binary Ree and Tits calculations required in Aschbacher–Smith F.1.12,
`refs/quasithin.pdf`, printed pp.263–264.
-/

public section

open Subgroup

namespace Subgroup

/-- When the derived subgroup is centerless, its ambient centralizer is
exactly the center of the whole group. -/
theorem centralizer_commutator_eq_center_of_center_eq_bot
    {G : Type*} [Group G] (hD : center (_root_.commutator G) = ⊥) :
    centralizer (_root_.commutator G : Set G) = center G := by
  let C := centralizer (_root_.commutator G : Set G)
  have hCD : C ⊓ _root_.commutator G = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz : (⟨x, hx.2⟩ : _root_.commutator G) ∈ center (_root_.commutator G) := by
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact hx.1 y y.property
    rw [hD, mem_bot] at hz
    exact mem_bot.mpr (congrArg Subtype.val hz)
  apply le_antisymm _ (center_le_centralizer _)
  have hcomm : ⁅C, (⊤ : Subgroup G)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hCD]
    exact le_inf (commutator_le_left C ⊤) (commutator_mono le_top le_rfl)
  exact commutator_top_right_eq_bot_iff_le_center.mp hcomm

end Subgroup

namespace MulAut

/-- A faithful normal-subgroup action covers every automorphism when the
outer automorphism order is bounded by the ambient index. -/
theorem conjNormal_bijective_of_outer_card_le_index
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hc : centralizer (N : Set G) = ⊥)
    (ho : Nat.card (Outer N) ≤ N.index) :
    Function.Bijective (conjNormal : G →* MulAut N) := by
  apply (conjNormal_injective_of_centralizer_eq_bot N hc).bijective_of_nat_card_le
  have hi : Nat.card (innerSubgroup N) ≤ Nat.card N :=
    Nat.card_le_card_of_surjective (conj : N →* MulAut N).rangeRestrict
      (conj : N →* MulAut N).rangeRestrict_surjective
  calc
    Nat.card (MulAut N) = Nat.card (innerSubgroup N) * Nat.card (Outer N) :=
      (innerSubgroup N).card_mul_index.symm
    _ ≤ Nat.card N * N.index := Nat.mul_le_mul hi ho
    _ = Nat.card G := N.card_mul_index

end MulAut
