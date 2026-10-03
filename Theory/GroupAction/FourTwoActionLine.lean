module
public import Theory.GroupAction.FourElementTwoAction
public import Theory.GroupAction.Quadratic
public import Theory.GroupAction.Lemmas
public import Mathlib.Tactic

/-!
# Nontrivial two-group actions on a four-element group

For a two-group acting on any group of order four, nontrivial displacement
has order exactly two. Fixed-point parity and divisibility make the common
fixed subgroup have order two, while the existing four-element quadraticity
theorem places displacement inside it. No faithfulness, involution, or
elementary-abelian assumption is required.

This finite-action calculation supplies the quotient displacement count in
the small branch of Stellmacher (10.1), Journal of Algebra 190 (1997),
printed page 60. The consumer constructs the actual quotient action.
-/

public theorem commutatorAction_card_two_of_nontrivial_two_action_on_four
    {A V : Type*} [Group A] [Group V] [Finite V] [MulDistribMulAction A V]
    (hA : IsPGroup 2 A) (hV : Nat.card V = 4)
    (hne : commutatorAction A V ≠ ⊥) :
    Nat.card (commutatorAction A V) = 2 := by
  let C := commutatorAction A V
  let F := FixedPoints.subgroup A V
  have hCtwo : 1 < Nat.card C := (Subgroup.one_lt_card_iff_ne_bot C).mpr hne
  have hquad : commutatorAction₂ A V = ⊥ :=
    two_group_action_on_four_is_quadratic hA hV
  have hCF : C ≤ F := commutatorAction_le_fixedPoints_of_commutatorAction₂_eq_bot hquad
  have hFtwo : 2 ≤ Nat.card F := by
    have hle := Subgroup.card_le_of_le hCF
    omega
  have hFdiv : Nat.card F ∣ 4 := hV ▸ F.card_subgroup_dvd_card
  have hFnotFour : Nat.card F ≠ 4 := by
    intro hfour
    have htop : F = ⊤ := Subgroup.eq_top_of_card_eq F (hfour.trans hV.symm)
    have htriv : ActsTrivially (A := A) (G := V) := by
      intro a v
      have hv : v ∈ F := htop.ge (Subgroup.mem_top v)
      exact hv a
    apply hne
    apply bot_unique
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro _ ⟨actor, point, rfl⟩
    simp [htriv actor point]
  have hFcard : Nat.card F = 2 := by
    obtain ⟨n, hn, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card F ∣ 2 ^ 2 by simpa using hFdiv)
    interval_cases n <;> omega
  have hCbound : Nat.card C ≤ 2 := hFcard ▸ Subgroup.card_le_of_le hCF
  change Nat.card C = 2
  omega
