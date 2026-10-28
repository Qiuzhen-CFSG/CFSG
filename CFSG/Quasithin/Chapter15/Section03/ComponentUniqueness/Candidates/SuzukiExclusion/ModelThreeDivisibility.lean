module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure.Models
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.SpecificGroups.ThreeDivisibility.Exceptional
public import Theory.SpecificGroups.ThreeDivisibility.Sporadic
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order

/-!
# Three-divisibility of the component alternatives

Every nonsuzuki alternative in the literal list 1.1.5(3) has order divisible
by three. The matrix cases use explicit cubic elements or faithful rank-one
subgroups; the derived endpoints and sporadic cases use their actual carriers.
An isomorphism transports divisibility, and the quotient order divides the
original group order, so central covers introduce no additional obligation.

The model/action input is unchanged, including the arbitrary Hermitian form,
the genuine triality central quotient, and the Ree fixed group specified by
all exceptional root equations. No construction of the Ree endomorphism is
needed for this consequence of a supplied model witness. The actions are
retained in the input but play no role in this cardinality argument.

Source: Aschbacher--Smith, `refs/quasithin.pdf`, 1.1.5(3), printed pp.501--503;
Theorem C and Remark A.2.4, p.33; the final implication of 15.3.34, p.1134.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.ModelThreeDivisibility
open Subgroup ComponentStructure ClassificationModels Chapter1.Section02.LocalModels
open Theory.SpecificGroups.ThreeDivisibility BenderSuzuki.MatrixGroups
variable {K : Type*} [Group K]

private theorem linear {n q : ℕ} (hn : 2 ≤ n) (h : ClassicalGroup.IsPSL K n q) :
    3 ∣ Nat.card K := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F n hn

private theorem unitary {f : ℕ} (hf : 0 < f)
    (h : ClassicalGroup.IsPSU K 3 (2 ^ f)) : 3 ∣ Nat.card K := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact unitary_three_dvd J f hf hcard hconj

private theorem g2_model {q : ℕ} (h : IsG2At K q) : 3 ∣ Nat.card K := by
  obtain ⟨F, hF, hfin, _, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact g2 F

private theorem bender (h : IsBenderModel K) :
    (∃ m : ℕ, 0 < m ∧ Nonempty (K ≃* SuzukiMatrixGroup m)) ∨ 3 ∣ Nat.card K := by
  cases h with
  | linear f _ iso => exact Or.inr (linear (by decide) iso)
  | unitary f hf iso => exact Or.inr (unitary (by omega) iso)
  | suzuki m hm iso => exact Or.inl ⟨m, hm, iso⟩

private theorem rank_two (h : RankTwoTheoremC K) : 3 ∣ Nat.card K := by
  cases h with
  | linear f _ iso => exact linear (by decide) iso
  | symplectic f _ iso =>
      obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact symplectic F hcard
  | g2 f _ iso => exact g2_model iso
  | triality f _ iso => exact Triality.Standard.model_three_dvd_card iso
  | ree m _ iso =>
      obtain ⟨d, ⟨e⟩⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact ReeF4.LocalBlockInput.three_dvd_card d
  | symplectic_derived iso =>
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact symplectic_derived
  | g2_derived iso =>
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact g2_derived
  | tits iso =>
      obtain ⟨e⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact tits

private theorem alternating_card (n : ℕ) (hn : n = 6 ∨ n = 7) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl <;>
    simp only [Nat.card_eq_fintype_card, _root_.card_alternatingGroup] <;> norm_num

private theorem alternating_action {α : MulAut K} {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hn : n = 6 ∨ n = 7) (h : AlternatingAction α n σ) : 3 ∣ Nat.card K := by
  rcases h with ⟨e, _⟩ | ⟨_, _, e, _⟩
  · rw [Nat.card_congr e.toEquiv]
    exact alternating_card n hn
  · have hd : 3 ∣ Nat.card (K ⧸ center K) := by
      rw [Nat.card_congr e.toEquiv]
      exact alternating_card n hn
    exact hd.trans (center K).card_quotient_dvd_card

private theorem sporadic_three_dvd (name : SporadicName) (hne : name ≠ .j3) :
    3 ∣ Nat.card name.Carrier := by
  cases name with
  | m11 => change 3 ∣ Nat.card Sporadic.Mathieu.M11; rw [Sporadic.Mathieu.m11_order]; decide
  | m12 => change 3 ∣ Nat.card Sporadic.Mathieu.M12; rw [Sporadic.Mathieu.m12_order]; decide
  | m22 => change 3 ∣ Nat.card Sporadic.Mathieu.M22; rw [Sporadic.Mathieu.m22_order]; decide
  | m23 => change 3 ∣ Nat.card Sporadic.Mathieu.M23; rw [Sporadic.Mathieu.m23_order]; decide
  | m24 => change 3 ∣ Nat.card Sporadic.Mathieu.M24; rw [Sporadic.Mathieu.m24_order]; decide
  | j2 => exact j2
  | j3 => exact (hne rfl).elim
  | j4 => exact j4
  | hs => exact hs
  | he => exact held
  | ru => exact rudvalis

/-- The exact component-model list leaves only Suzuki or three-divisibility.
The conclusion in fact needs no separate finiteness or quasisimplicity premise. -/
theorem suzuki_or_three_dvd (α : MulAut K) (h : ModelAction115 K α) :
    (∃ m : ℕ, 0 < m ∧ Nonempty (K ≃* SuzukiMatrixGroup m)) ∨ 3 ∣ Nat.card K := by
  cases h with
  | lie _ model _ =>
      rcases model with h | h | ⟨n, hn, h⟩
      · exact bender h
      · exact Or.inr (rank_two h)
      · exact Or.inr (linear (by rcases hn with rfl | rfl <;> decide) h)
  | two_cover _ _ model _ =>
      right
      have hd : 3 ∣ Nat.card (K ⧸ pCore 2 K) := by
        rcases model with h | h
        · exact linear (by decide) h
        · exact g2_model h
      exact hd.trans (pCore 2 K).card_quotient_dvd_card
  | six σ _ action => exact Or.inr (alternating_action (Or.inl rfl) action)
  | seven σ _ action => exact Or.inr (alternating_action (Or.inr rfl) action)
  | odd model _ =>
      right
      rcases model with h | ⟨p, _, h⟩
      · exact linear (by decide) h
      · exact linear (by decide) h
  | sporadic name hne model _ =>
      right
      obtain ⟨e⟩ := model
      have hd : 3 ∣ Nat.card (K ⧸ pCore 2 K) := by
        rw [Nat.card_congr e.toEquiv]
        exact sporadic_three_dvd name hne
      exact hd.trans (pCore 2 K).card_quotient_dvd_card

end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.ModelThreeDivisibility
