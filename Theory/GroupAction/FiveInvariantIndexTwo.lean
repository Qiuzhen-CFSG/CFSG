module

public import Theory.GroupAction.FaithfulSixteen
public import Mathlib.GroupTheory.Index

/-!
# Invariant subgroups above an index-two layer

Suppose E has index two in F, and a group with action image divisible by five
acts on P/F of order sixteen. An invariant normal subgroup Q containing E
is E, F, P, or an index-two supplement to F meeting it in E.

The image of Q in P/F is trivial or full. The index-two interval between
E and F then determines the intersection; the relative-index formula
counts the supplement. In particular F ≤ Q cannot be omitted when claiming
only the alternatives F and P.

Application: the corrected full-Ree reduction in Aschbacher--Smith,
The Classification of Quasithin Groups, Lemma 14.2.21, printed p.989.
-/

namespace Theory.GroupAction

open Subgroup

private theorem interval_two {P : Type*} [Group P]
    (E F Q : Subgroup P) (hEQ : E ≤ Q) (hQF : Q ≤ F)
    (hEF : E.relIndex F = 2) : Q = E ∨ Q = F := by
  have hm := E.relIndex_mul_relIndex Q F hEQ hQF
  rw [hEF] at hm
  have hd : Q.relIndex F ∣ 2 := dvd_of_mul_left_eq _ hm
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with h | h
  · exact Or.inr (le_antisymm hQF (relIndex_eq_one.mp h))
  · have he : E.relIndex Q = 1 := by rw [h] at hm; omega
    exact Or.inl (le_antisymm (relIndex_eq_one.mp he) hEQ)

/-- The index-two supplement is a genuine additional possibility unless
some further group-theoretic condition excludes it. -/
public theorem invariant_subgroup_cases_of_index_two_layer {A P : Type*} [Group A] [Group P] [Finite P]
    (E F Q : Subgroup P) [F.Normal] [Q.Normal]
    (ρ : A →* MulAut (P ⧸ F))
    (hQ : ∀ a : A, ∀ v : P ⧸ F,
      v ∈ Q.map (QuotientGroup.mk' F) ↔ ρ a v ∈ Q.map (QuotientGroup.mk' F))
    (hEQ : E ≤ Q) (hEF : E ≤ F) (hindex : E.relIndex F = 2)
    (hA : 5 ∣ Nat.card ρ.range) (hV : Nat.card (P ⧸ F) = 16) :
    Q = E ∨ Q = F ∨ Q = ⊤ ∨
      (Q ⊓ F = E ∧ Q ⊔ F = ⊤ ∧ Q.index = 2) := by
  have hjoin : Q ⊔ F = F ∨ Q ⊔ F = ⊤ := by
    rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five ρ hA hV
        (Q.map (QuotientGroup.mk' F)) hQ with hb | ht
    · exact Or.inl (sup_eq_right.mpr (by simpa using (map_eq_bot_iff Q).mp hb))
    · right
      have hm : (Q ⊔ F).map (QuotientGroup.mk' F) = ⊤ := by
        rw [Subgroup.map_sup, ht, top_sup_eq]
      have hc := congrArg (Subgroup.comap (QuotientGroup.mk' F)) hm
      rwa [Subgroup.comap_map_eq_self (by simp),
        Subgroup.comap_top] at hc
  rcases hjoin with h | h
  · have hQF : Q ≤ F := h ▸ (le_sup_left : Q ≤ Q ⊔ F)
    rcases interval_two E F Q hEQ hQF hindex with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases interval_two E F (Q ⊓ F) (le_inf hEQ hEF) inf_le_right hindex with hi | hi
    · right; right; right
      refine ⟨hi, h, ?_⟩
      have hh := relIndex_sup_left F Q
      rw [h, relIndex_top_right, ← inf_relIndex_right Q F, hi, hindex] at hh
      exact hh
    · have hFQ : F ≤ Q := hi ▸ (inf_le_left : Q ⊓ F ≤ Q)
      exact Or.inr (Or.inr (Or.inl (by simpa only [sup_eq_left.mpr hFQ] using h)))

end Theory.GroupAction
