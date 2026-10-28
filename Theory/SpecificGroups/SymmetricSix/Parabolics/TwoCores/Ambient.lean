module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.PGroupCore

import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The ambient two-cores and center of the six-letter groups

Both `A₆` and `S₆` have trivial two-core, and `S₆` has trivial center.
Simplicity handles normal subgroups of `A₆`; every nontrivial normal subgroup
of `S₆` contains `A₆`. The latter cannot be a two-group because its order is
divisible by three, and cannot be central because its own center is trivial.

These are intrinsic results about the permutation models used by the
parabolic calculations. Source: Aschbacher–Smith, *The Classification of
Quasithin Groups*, I.5.7, printed pp. 420–421.
-/

public section

namespace Theory.SpecificGroups.SymmetricSix

private theorem a6_not_isPGroup_two : ¬ IsPGroup 2 A6 := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
  rw [a6_order] at hn
  have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 360).trans hn
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

/-- The actual alternating group on six letters has no nontrivial normal
two-subgroup. -/
theorem a6_twoCore_eq_bot : pCore 2 A6 = ⊥ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Letter)
      (by simp [Letter]) (N := pCore 2 A6) with h | h
  · exact h
  · apply False.elim
    apply a6_not_isPGroup_two
    have hp := pCore_isPGroup (p := 2) (G := A6)
    rw [h] at hp
    exact hp.of_equiv Subgroup.topEquiv

/-- The actual symmetric group on six letters has no nontrivial normal
two-subgroup. -/
theorem s6_twoCore_eq_bot : pCore 2 S6 = ⊥ := by
  by_contra h
  have hn : Nontrivial (pCore 2 S6) := (Subgroup.nontrivial_iff_ne_bot _).2 h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Letter)
    (by simp [Letter]) hn
  exact a6_not_isPGroup_two (pCore_isPGroup.to_le hle)

/-- The six-letter symmetric group has trivial center, as required in the
exceptional reducible-action case of I.5.7. -/
theorem s6_center_eq_bot : Subgroup.center S6 = ⊥ := by
  by_contra h
  have hn : Nontrivial (Subgroup.center S6) := (Subgroup.nontrivial_iff_ne_bot _).2 h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Letter)
    (by simp [Letter]) hn
  have hall (a : A6) : a = 1 := by
    have ha : a ∈ Subgroup.center A6 := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (hle a.property) b.val
    rwa [a6_center_eq_bot, Subgroup.mem_bot] at ha
  obtain ⟨a, ha⟩ := exists_ne (1 : A6)
  exact ha (hall a)

end Theory.SpecificGroups.SymmetricSix
