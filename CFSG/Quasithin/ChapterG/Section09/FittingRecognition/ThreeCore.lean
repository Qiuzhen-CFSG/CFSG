module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeCore.Action
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeCore.Automizers
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.DegreeCases

/-!
# The cubic Fitting reduction in G.9.4

The normal rank-two three-group supplied by B.5.2 carries an automizer
section isomorphic to the actual actor. A.1.25 and the cyclic index-two
subgroup of a Sylow two-subgroup of GL₂(3) bound that elementary section.
The earlier A.1.5 rank input applies to O₃(G) itself. Normality and the
faithful irreducible action give full moved space and even dimension.

The final theorem feeds these proved fields to the existing degree-case
reduction. The sole earlier explicit input is A.1.5's three-group rank
consequence; its discharge remains with the Section G.9 assembly owner.

Source: Aschbacher--Smith, proof of G.9.4, printed p.355, PDF p.366.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

open Subgroup

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- The actor is an elementary section of the actual covering automizer,
whose two-sections have order at most four. -/
theorem actor_rank_le_two_of_faithful_three_core (h : FittingHypothesis K ρ A m)
    (hf : A ⊓ centralizer (pCore 3 G : Set G) = ⊥) : m ≤ 2 := by
  obtain ⟨c, B, hn, hp, he, hr⟩ := exists_rank_two_three_cover h
  let : B.Normal := hn
  let : IsElementaryAbelian 2 A := h.elementary
  obtain ⟨H, _, f, hsurj⟩ := exists_automizer_section c.projection c.surjective B A
    (by rwa [he])
  have hc := three_automorphism_elementary_section_card hp hr H f hsurj
  rw [h.card_actor] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

/-- Every field of the cubic reduction is proved. A.1.5 is used only for
the lower three-rank bound on the actual core. -/
theorem threeCoreData (rankInput : ThreeGroupRankInput.{u})
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    ThreeCoreData ρ A m := by
  have hf := faithful_three_core h hc
  exact {
    faithful := hf
    actor_rank_le := actor_rank_le_two_of_faithful_three_core h hf
    core_rank_ge := rankInput G A (pCore 3 G) m h.elementary h.card_actor pCore_isPGroup
      (by rw [normalizer_eq_top]; exact le_top) hf
    moved_eq_top := three_core_moved_eq_top h hm hf
    even_degree := even_degree_of_faithful_three_core h hm hf }

/-- The literal rank/degree reduction used by the independent normalizer
branches, now with every three-core field discharged. -/
theorem caseOne_or_remaining_degrees_of_cubic (rankInput : ThreeGroupRankInput.{u})
    (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hc : IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    CaseOne ρ m ∨
    (m = 1 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 6) :=
  caseOne_or_remaining_degrees h hm (threeCoreData rankInput h hm hc)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
