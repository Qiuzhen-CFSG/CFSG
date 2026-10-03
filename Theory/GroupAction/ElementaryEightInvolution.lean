module
public import Theory.GroupAction.FourElementInvolutionLines

/-!
# Fixed points of an involution on an elementary eight

A nontrivial action of a two-element group on an elementary abelian group of
order8 has exactly four fixed elements. The specified nonidentity actor is
required to move an element; without that hypothesis the fixed subgroup may
be the whole elementary eight.

The established involution displacement identity expresses order8 as the
product of the fixed and displacement orders, and places displacement inside
the fixed subgroup. Together with subgroup cardinality this leaves fixed
orders4 and8. Nontrivial action excludes8.

This elementary finite-action calculation supplies the initial-center fixed
plane of the actual selected eight in Stellmacher (9.1), Journal of
Algebra190 (1997), p.48. It uses the supplied action instance unchanged.
-/

universe u
/-- A nontrivial involution action on an elementary eight has a four-element
fixed subgroup. -/
public theorem fixed_subgroup_card_four_of_nontrivial_involution_on_eight
    {Q U : Type u} [Group Q] [Group U] [Finite Q] [Finite U]
    [IsElementaryAbelian 2 U] [MulDistribMulAction Q U]
    (x : Q) (hx : x ≠ 1 ∧ x^2=1) (hQcard : Nat.card Q=2)
    (hUcard : Nat.card U=8) (hne : ∃ u : U, x • u ≠ u) :
    Nat.card (FixedPoints.subgroup Q U)=4 := by
  let _ : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hUcard]; decide)
  obtain ⟨hprod,hle⟩ := card_two_action_fixed_commutator_card_data (U := U) x hx hQcard
  let C := FixedPoints.subgroup Q U
  change Nat.card U = Nat.card C * Nat.card (commutatorAction Q U) at hprod
  rw [hUcard] at hprod
  have hCcard : Nat.card C ≤ 8 := by simpa only [hUcard] using C.card_le_card_group
  have hMcard : Nat.card (commutatorAction Q U) ≤ Nat.card C := Subgroup.card_le_of_le hle
  have hnot8 : Nat.card C ≠ 8 := by
    intro hh
    have htop : C=⊤ := Subgroup.eq_top_of_card_eq C (hh.trans hUcard.symm)
    obtain ⟨u,hu⟩ := hne
    have hufix : u ∈ C := by rw [htop]; trivial
    exact hu (hufix x)
  change Nat.card C = 4
  interval_cases h : Nat.card C <;> omega
