module
public import Theory.GroupAction.FixedHyperplaneQuadratic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# Two-group actions on a four-element group

Every action by automorphisms of a two-group on a finite group of order
four is quadratic. No faithfulness or elementary-abelian premise is needed.
Orbit counting makes the common fixed subgroup have even cardinality.
Its positive order divides four, leaving order two or four. The former
case is the fixed-index-two quadraticity theorem; the latter action is
trivial.

This supplies the small-summand actions used when comparing the two
sixteen-element modules in Stellmacher (9.1), printed p48 of
`refs/files/stellmacher-n-group.pdf`.
-/

public theorem two_group_action_on_four_is_quadratic
    {A V : Type*} [Group A] [Group V] [Finite V] [MulDistribMulAction A V]
    (hA : IsPGroup 2 A) (hV : Nat.card V = 4) : commutatorAction₂ A V = ⊥ := by
  let F := FixedPoints.subgroup A V
  have hmod := hA.card_modEq_card_fixedPoints V
  change Nat.ModEq 2 (Nat.card V) (Nat.card F) at hmod
  have hdvd : Nat.card F ∣ 2 ^ 2 := by simpa [hV] using F.card_subgroup_dvd_card
  obtain ⟨n, hn, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases n
  · rw [hV, heq] at hmod
    norm_num [Nat.ModEq] at hmod
  · apply fixed_hyperplane_isQuadraticAction
    change Nat.card V = 2 * Nat.card F
    norm_num [hV, heq]
  · have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by simpa [hV] using heq)
    apply bot_unique
    rw [commutatorAction₂, commutatorSubgroup, Subgroup.closure_le]
    rintro _ ⟨actor, point, _, rfl⟩
    have hfix : actor • point = point := (htop.ge (Subgroup.mem_top point)) actor
    rw [hfix, inv_mul_cancel]
    exact Subgroup.one_mem _
