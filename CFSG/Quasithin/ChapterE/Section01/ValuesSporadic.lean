module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.Mathieu.M11.Basic
public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M24.Basic
public import Theory.SpecificGroups.Held.Model.Basic

/-!
# The positivity step for the sporadic E-generation values

For each model in E.1.14(4), an explicit involution proves that its order is
even. Lagrange's theorem transfers this to any ambient finite group containing
an isomorphic subgroup. Consequently, once rank-one E-generation of the
ambient group is established, the source minimum is attained and equals one.
This applies also to the almost-simple extensions in the source.

These are conditional assembly lemmas, not the upper-generation assertions
of E.1.14(4)--(5). Those assertions require local generation proofs for the
models and their permitted extensions. In particular an order computation,
or the existence of an involution, does not supply an E-generation bound.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.6 and E.1.14(4)--(5), pp.210, 214; the latter cites Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.9.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE

open Sporadic.Mathieu

/-- The four model alternatives in E.1.14(4), with actual multiplicative
equivalences. No generation conclusion is part of this predicate. -/
def IsRankOneSporadicModel (L : Type*) [Group L] : Prop :=
  Nonempty (L ≃* M11) ∨ Nonempty (L ≃* M12) ∨
    Nonempty (L ≃* M24) ∨ Nonempty (L ≃* Held.He)

private theorem even_card_m11 : Even (Nat.card M11) := by
  apply even_iff_two_dvd.mpr
  simpa only [m11GeneratorA_order] using M11.orderOf_dvd_natCard m11GeneratorA_mem

private theorem even_card_m12 : Even (Nat.card M12) := by
  apply even_iff_two_dvd.mpr
  simpa only [m12GeneratorA_order] using M12.orderOf_dvd_natCard m12GeneratorA_mem

private theorem even_card_m24 : Even (Nat.card M24) := by
  apply even_iff_two_dvd.mpr
  simpa only [m24GeneratorA_order] using M24.orderOf_dvd_natCard m24GeneratorA_mem

private theorem even_card_held : Even (Nat.card Held.He) := by
  apply even_iff_two_dvd.mpr
  simpa only [Held.orderOf_a] using orderOf_dvd_natCard Held.a

/-- The evenness needed for the positive minimum comes from actual model
involutions; no model-order or simplicity theorem is needed. -/
theorem IsRankOneSporadicModel.even_card {L : Type*} [Group L]
    (h : IsRankOneSporadicModel L) : Even (Nat.card L) := by
  unfold IsRankOneSporadicModel at h
  rcases h with h | h | h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact even_card_m11
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact even_card_m12
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact even_card_m24
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv]
    exact even_card_held

variable {G : Type*} [Group G]

/-- Evenness transfers from the embedded socle model to the whole extension. -/
theorem IsRankOneSporadicModel.even_card_ambient {L : Subgroup G}
    (h : IsRankOneSporadicModel L) : Even (Nat.card G) :=
  h.even_card.trans_dvd L.card_subgroup_dvd_card

variable [Finite G]

/-- A proved positive E-generation bound makes the source parameter positive
for every ambient group containing one of the four equality-case models. -/
theorem generationParameter_pos_of_rankOneSporadicModel {L : Subgroup G}
    (hL : IsRankOneSporadicModel L) {i : ℕ} (hi : 0 < i)
    (hgen : IsEGenerated i G) : 0 < generationParameter G :=
  (generationParameter_spec (Nat.not_odd_iff_even.mpr hL.even_card_ambient)
    ⟨i, hi, hgen⟩).1

/-- Conditional final step for E.1.14(4). The outstanding hypothesis is
rank-one E-generation of the ambient group, including any outer 2-extension. -/
theorem generationParameter_eq_one_of_rankOneSporadicModel {L : Subgroup G}
    (hL : IsRankOneSporadicModel L) (hgen : IsEGenerated 1 G) :
    generationParameter G = 1 := by
  have hpos := generationParameter_pos_of_rankOneSporadicModel hL (by decide) hgen
  have hle := generationParameter_le (by decide : 0 < 1) hgen
  omega

end CFSG.Quasithin.ChapterE
