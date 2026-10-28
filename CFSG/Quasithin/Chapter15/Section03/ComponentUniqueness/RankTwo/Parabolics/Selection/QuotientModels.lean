module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Definitions

/-!
# Transporting every characteristic-two model to the component image

The component image is L/Z(L). A simple perfect L has trivial center; a
two-cover has the specified two-core as center; and the alternating action
alternative supplies either the actual A₆ model or its central quotient.
Thus all cases of 1.1.5(3)(a)--(c) transfer without guessing a group order
or silently identifying a small derived group with an alternating group.

The result still retains the exceptional cases and asserts no Borel
containment. Their elimination is the separate parabolic inspection.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3),
printed pp.501--502, Theorem C(3),(4), printed p.33, and p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open Candidates.ComponentStructure Chapter1.Section02.LocalModels ClassificationModels

private theorem center_eq_bot_of_simple_perfect (X : Type*) [Group X]
    [IsSimpleGroup X] [Group.IsPerfect X] : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) inferInstance with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim

private theorem rankTwo_cases {X D : Type*} [Group X] [Group D]
    (h : RankTwoTheoremC X) (e : D ≃* X) :
    LargerFieldRankTwoModel D ∨ ExceptionalModel D := by
  cases h with
  | linear n hn h =>
      by_cases hlarge : 1 < n
      · exact Or.inl (.linear n hlarge (h.of_mulEquiv e))
      · have he : n = 1 := by omega
        exact Or.inr (.linear_three_two (by simpa [he] using h.of_mulEquiv e))
  | symplectic n hn h => exact Or.inl (.symplectic n hn (h.of_mulEquiv e))
  | g2 n hn h => exact Or.inl (.g2 n hn (h.of_mulEquiv e))
  | triality n hn h =>
      by_cases hlarge : 1 < n
      · exact Or.inl (.triality n hlarge (h.of_mulEquiv e))
      · have he : n = 1 := by omega
        exact Or.inr (.triality_two (by simpa [he] using h.of_mulEquiv e))
  | ree m hm h =>
      obtain ⟨d, ⟨a⟩⟩ := h
      exact Or.inl (.ree m hm ⟨d, ⟨e.trans a⟩⟩)
  | symplectic_derived h => exact Or.inr (.symplectic_derived (h.map (e.trans ·)))
  | g2_derived h => exact Or.inr (.g2_derived (h.map (e.trans ·)))
  | tits h => exact Or.inr (.tits (h.map (e.trans ·)))

private theorem lieType_cases {X D : Type*} [Group X] [Group D]
    (h : LieTypeTwoModel X) (e : D ≃* X) :
    SmallBinaryModel D ∨ LargerFieldRankTwoModel D ∨ ExceptionalModel D := by
  rcases h with h | h | ⟨n, hn, h⟩
  · exact Or.inr (Or.inr (.rank_one (h.of_mulEquiv e)))
  · exact Or.inr (rankTwo_cases h e)
  · rcases hn with rfl | rfl
    · exact Or.inl (Or.inl (h.of_mulEquiv e))
    · exact Or.inl (Or.inr (h.of_mulEquiv e))

variable {G : Type*} [Group G] (L : Subgroup G) [L.Normal]

private noncomputable def componentEquivOfCenterEqBot (hz : center L = ⊥) :
    centralizerQuotientComponent L ≃* L :=
  (centralizerQuotientComponentEquiv L).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

/-- The complete catalogue on the actual component image, retaining all cases
whose exclusion needs local geometry. No p.1139 conclusion is an input. -/
theorem component_model_cases [IsQuasisimple L] {α : MulAut L}
    (h : CharacteristicTwoAction115 L α) :
    SmallBinaryModel (centralizerQuotientComponent L) ∨
      LargerFieldRankTwoModel (centralizerQuotientComponent L) ∨
      ExceptionalModel (centralizerQuotientComponent L) := by
  rcases h with ⟨hs, hm, _⟩ | ⟨_, hz, hm, _⟩ | ⟨σ, _, ha⟩
  · let := hs
    exact lieType_cases hm
      (componentEquivOfCenterEqBot L (center_eq_bot_of_simple_perfect L))
  · let e := (centralizerQuotientComponentEquiv L).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hz)
    rcases hm with hm | hm
    · exact Or.inr (Or.inl (.linear 2 (by decide) (hm.of_mulEquiv e)))
    · exact Or.inr (Or.inl (.g2 2 (by decide) (hm.of_mulEquiv e)))
  · rcases ha with ⟨e, _⟩ | ⟨_, _, e, _⟩
    · have hz : center L = ⊥ := by
        apply bot_unique
        intro x hx
        rw [mem_bot]
        apply e.injective
        rw [map_one]
        have hc : e x ∈ center (alternatingGroup (Fin 6)) := by
          rw [mem_center_iff]
          intro y
          obtain ⟨w, rfl⟩ := e.surjective y
          exact (map_mul e w x).symm.trans
            ((congrArg e ((mem_center_iff.mp hx) w)).trans (map_mul e x w))
        rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)), mem_bot] at hc
        exact hc
      exact Or.inr (Or.inr (.alternating_six
        ⟨(componentEquivOfCenterEqBot L hz).trans e⟩))
    · exact Or.inr (Or.inr (.alternating_six
        ⟨(centralizerQuotientComponentEquiv L).symm.trans e⟩))

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
