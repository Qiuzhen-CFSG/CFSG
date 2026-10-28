module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.ThreeElements
public import Theory.GroupAction.SubgroupFixedPrimeElement

/-!
# Fixed three-elements in normalized chi-zero blocks

The actual alternating and even-field rank-one quotients give an element
of order three by `exists_order_three`. Orbit counting for conjugation by
a cubic actor then gives a fixed three-element in each normalized block.
Thus no coverage theorem for automorphisms of PSL₂ is needed here.

Source: Aschbacher–Smith, proof of E.6.14, printed p.251 (PDF p.262).
The normalization step belongs to `FixedNine.Permutation`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

theorem fixed_three_of_normalizes {L : Subgroup G}
    (hL : ChapterC.IsChiZeroBlock L) {x : G} (hx : orderOf x = 3)
    (hn : x ∈ normalizer (L : Set G)) :
    ∃ a ∈ L, orderOf a = 3 ∧ a ∈ centralizer ({x} : Set G) := by
  obtain ⟨a, ha⟩ := exists_order_three hL
  exact L.exists_order_prime_in_centralizer_of_normalizes
    (hx ▸ pow_orderOf_eq_one x) hn (ha ▸ orderOf_dvd_natCard a)

theorem fixed_nine_of_normalizes {L₁ L₂ : Subgroup G}
    (h₁ : ChapterC.IsChiZeroBlock L₁) (h₂ : ChapterC.IsChiZeroBlock L₂)
    (hc : L₂ ≤ centralizer (L₁ : Set G)) {x : G} (hx : orderOf x = 3)
    (hn₁ : x ∈ normalizer (L₁ : Set G)) (hn₂ : x ∈ normalizer (L₂ : Set G)) :
    ∃ E : Subgroup G, IsElementaryAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ L₁ ⊔ L₂ ∧ E ≤ centralizer ({x} : Set G) := by
  obtain ⟨a, haL, ha, hax⟩ := fixed_three_of_normalizes h₁ hx hn₁
  obtain ⟨b, hbL, hb, hbx⟩ := fixed_three_of_normalizes h₂ hx hn₂
  exact fixed_nine_of_commuting_threes h₁.chi.short hc haL hbL ha hb hax hbx

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
