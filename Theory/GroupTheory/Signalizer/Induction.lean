module
public import Theory.GroupTheory.Signalizer.LocalCompleteness
public import Theory.GroupTheory.Signalizer.Quotient
public import Theory.GroupAction.Quotient
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Reducing binary signalizer completion to the local criterion

Fix a finite elementary binary actor of order at least eight. A universal
local-to-complete criterion for this actor implies completeness of every
family on a finite ambient group. The criterion is an explicit hypothesis
quantified over ambient groups and their supplied actions in the same
universe. This module proves the induction reduction; the unconditional
completion theorem must discharge that criterion independently.

Strong induction uses the ambient group order plus the sum of the orders
of the actual family values. A nontrivial normal signalizer subgroup gives
a quotient with smaller ambient order and no larger values; quotient
completeness lifts through the actual invariant kernel. If no such subgroup
exists, every nontrivial signalizer subgroup has a proper normalizer. The
restricted families there are complete by induction, giving the normalizer
condition. Each relevant q-prime family has no larger values and at least
one strictly smaller value, giving the other local condition by induction.
The supplied criterion now completes the family. The same original action
is retained through every restriction and canonical quotient construction.

Source: the minimal-counterexample reduction in Kurzweil–Stellmacher,
*The Theory of Finite Groups*, §11.2.9, printed p.325,
`refs/latex/kurzweil.tex`.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

universe u v

public theorem complete_of_local_criterion
    {A : Type u} {G : Type v} [Group A] [Finite A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    (hA : 8 ≤ Nat.card A)
    (criterion : ∀ (H : Type v) [Group H] [Finite H] [MulDistribMulAction A H]
      (η : TwoSignalizerFamily A H), 8 ≤ Nat.card A → η.IsLocallyComplete → η.IsComplete)
    (θ : TwoSignalizerFamily A G) : θ.IsComplete := by
  classical
  let _ : Fintype {a : A // a ≠ 1} := Fintype.ofFinite _
  have main : ∀ n : ℕ, ∀ (H : Type v) [Group H] [Finite H] [MulDistribMulAction A H]
      (η : TwoSignalizerFamily A H),
      Nat.card H + ∑ a, Nat.card (η.subgroup a) = n → η.IsComplete := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H _ _ _ η hn
      by_cases hex : ∃ N : Subgroup H, η.IsSignalizerSubgroup N ∧ N ≠ ⊥ ∧ N.Normal
      · obtain ⟨N, hN, hNne, hNN⟩ := hex
        let _ := hNN
        let _ := quotientMulDistribMulAction (A := A) N hN.2.2.1
        let hequiv : ∀ a : A, ∀ x : H,
            QuotientGroup.mk' N (a • x) = a • QuotientGroup.mk' N x := fun _ _ => rfl
        let ηbar := η.quotient (IsElementaryAbelian.isPGroup 2 A) N hequiv
        have hsum : (∑ a, Nat.card (ηbar.subgroup a)) ≤ ∑ a, Nat.card (η.subgroup a) := by
          apply Finset.sum_le_sum
          intro a _
          rw [quotient_subgroup]
          exact Nat.le_of_dvd Nat.card_pos ((η.subgroup a).card_map_dvd (QuotientGroup.mk' N))
        have hcard : Nat.card (H ⧸ N) < Nat.card H := by
          have hNcard := (Subgroup.one_lt_card_iff_ne_bot (H := N)).mpr hNne
          have hpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
          have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup N
          nlinarith
        have hsmall : Nat.card (H ⧸ N) + ∑ a, Nat.card (ηbar.subgroup a) < n := by
          rw [← hn]
          exact Nat.add_lt_add_of_lt_of_le hcard hsum
        exact η.isComplete_of_quotient (IsElementaryAbelian.isPGroup 2 A) N hequiv hN
          (ih _ hsmall (H ⧸ N) ηbar rfl)
      · apply criterion H η hA
        constructor
        · intro U hU hUne
          let _ := hU.2.2.1
          let N := Subgroup.normalizer (U : Set H)
          let _ : IsInvariant A H N := isInvariant_normalizer U
          have hNne : N ≠ ⊤ := by
            intro heq
            exact hex ⟨U, hU, hUne, Subgroup.normalizer_eq_top_iff.mp heq⟩
          have hcard : Nat.card N < Nat.card H := by
            exact lt_of_not_ge fun h => hNne (N.eq_top_of_le_card h)
          have hsum : (∑ a, Nat.card ((η.restrict N).subgroup a)) ≤
              ∑ a, Nat.card (η.subgroup a) := by
            apply Finset.sum_le_sum
            intro a _
            rw [restrict_subgroup]
            exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_comap_dvd_of_injective
              (η.subgroup a) N.subtype N.subtype_injective)
          have hsmall : Nat.card N + ∑ a, Nat.card ((η.restrict N).subgroup a) < n := by
            rw [← hn]
            exact Nat.add_lt_add_of_lt_of_le hcard hsum
          exact (η.isSignalizerSubgroup_closureWithin_iff N).mpr
            (ih _ hsmall N (η.restrict N) rfl)
        · intro q _ hdiv
          obtain ⟨a, ha⟩ := hdiv
          have hsum : (∑ b, Nat.card ((η.qPrime q).subgroup b)) <
              ∑ b, Nat.card (η.subgroup b) := by
            exact Finset.sum_lt_sum (fun b _ => η.qPrime_card_le q b)
              ⟨a, Finset.mem_univ a, η.qPrime_card_lt_of_dvd q a ha⟩
          have hsmall : Nat.card H + ∑ b, Nat.card ((η.qPrime q).subgroup b) < n := by
            rw [← hn]
            exact Nat.add_lt_add_left hsum _
          exact ih _ hsmall H (η.qPrime q) rfl
  exact main _ G θ rfl

end Theory.GroupTheory.TwoSignalizerFamily
