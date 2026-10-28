module
public import Theory.Representation.BinaryAlternatingFiveFlag.PairedBorel

/-!
# Transport of the paired Borel section to literal subgroup images

An injective coordinate map retains the two three-spaces and their fixed
lines inside the original group. Independent point-stabilizer lifts and an
element exchanging the supported factors supply the irreducible interval.
Thus a normalized subgroup containing the fixed plane and meeting the
six-space outside that plane contains the whole six-space. The exchange
is stated on the actual factor subgroups; no formula for its square is needed.

Source: Aschbacher--Smith, 14.6.9(k), printed p.1027.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveFlag
open Subgroup FiveCentralizerGeometry AlternatingFiveBorel
variable {G : Type*} [Group G]

/-- Literal coordinate maps for independent point stabilizers and an exchange of their factors. -/
structure PairedBorelCoordinates (J : Subgroup G) where
  embedding : V × V →* G
  injective : Function.Injective embedding
  first_actor : ∀ b : B, ∃ g ∈ J, ∀ x : V × V,
    embedding (act b x.1, x.2) = g * embedding x * g⁻¹
  second_actor : ∀ b : B, ∃ g ∈ J, ∀ x : V × V,
    embedding (x.1, act b x.2) = g * embedding x * g⁻¹
  exchange : ∃ t ∈ J,
    ((three.prod (⊥ : Subgroup V)).map embedding).map (MulAut.conj t).toMonoidHom =
      ((⊥ : Subgroup V).prod three).map embedding

namespace PairedBorelCoordinates
variable {J : Subgroup G}

abbrev six (d : PairedBorelCoordinates J) : Subgroup G := pairThree.map d.embedding
abbrev two (d : PairedBorelCoordinates J) : Subgroup G := pairLine.map d.embedding

theorem cards (d : PairedBorelCoordinates J) : Nat.card d.six = 64 ∧ Nat.card d.two = 4 := by
  constructor
  · exact (Nat.card_congr (pairThree.equivMapOfInjective d.embedding d.injective).toEquiv).symm.trans
      pairThree_card
  · exact (Nat.card_congr (pairLine.equivMapOfInjective d.embedding d.injective).toEquiv).symm.trans
      pairLine_card

theorem two_le_six (d : PairedBorelCoordinates J) : d.two ≤ d.six :=
  map_mono (prod_mono line_le_three line_le_three)

theorem six_le_of_normalized_intersection (d : PairedBorelCoordinates J)
    (F : Subgroup G) (hZF : d.two ≤ F) (hJF : J ≤ normalizer (F : Set G))
    (hne : ¬ d.six ⊓ F ≤ d.two) : d.six ≤ F := by
  let W := pairThree ⊓ F.comap d.embedding
  have hline : pairLine ≤ W :=
    le_inf (prod_mono line_le_three line_le_three) (map_le_iff_le_comap.mp hZF)
  have hfirst : ∀ b : B, ∀ x ∈ W, (act b x.1, x.2) ∈ W := by
    intro b x hx
    obtain ⟨g, hg, he⟩ := d.first_actor b
    refine ⟨⟨three_invariant b x.1 hx.1.1, hx.1.2⟩, ?_⟩
    change d.embedding (act b x.1, x.2) ∈ F
    rw [he x]
    exact (mem_normalizer_iff.mp (hJF hg) (d.embedding x)).mp hx.2
  have hsecond : ∀ b : B, ∀ x ∈ W, (x.1, act b x.2) ∈ W := by
    intro b x hx
    obtain ⟨g, hg, he⟩ := d.second_actor b
    refine ⟨⟨hx.1.1, three_invariant b x.2 hx.1.2⟩, ?_⟩
    change d.embedding (x.1, act b x.2) ∈ F
    rw [he x]
    exact (mem_normalizer_iff.mp (hJF hg) (d.embedding x)).mp hx.2
  have hf (P : Subgroup (V × V)) (hP : P ≤ pairThree) :
      P ≤ W ↔ P.map d.embedding ≤ F := by
    constructor
    · exact fun hh => map_le_iff_le_comap.mpr (hh.trans inf_le_right)
    · exact fun hh => le_inf hP (map_le_iff_le_comap.mp hh)
  have hexchange : three.prod (⊥ : Subgroup V) ≤ W ↔
      (⊥ : Subgroup V).prod three ≤ W := by
    rw [hf _ (prod_mono le_rfl bot_le), hf _ (prod_mono bot_le le_rfl)]
    obtain ⟨t, ht, he⟩ := d.exchange
    have htF : F.map (MulAut.conj t).toMonoidHom = F :=
      mem_normalizer_iff_map_conj_eq.mp (hJF ht)
    constructor
    · intro hh
      have hm := map_mono (f := (MulAut.conj t).toMonoidHom) hh
      rwa [he, htF] at hm
    · intro hh
      apply (map_le_map_iff_of_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective).mp
      rwa [he, htF]
  rcases pair_line_irreducible_of_factor_exchange W hline inf_le_left hfirst hsecond hexchange with
    hW | hW
  · exfalso
    apply hne
    rintro a ⟨⟨v, hv, rfl⟩, hvF⟩
    exact mem_map_of_mem d.embedding (hW.le (show v ∈ W from ⟨hv, hvF⟩))
  · rintro a ⟨v, hv, rfl⟩
    have hvW : v ∈ W := hW.symm ▸ hv
    exact hvW.2

theorem irreducible_interval (d : PairedBorelCoordinates J)
    (W : Subgroup G) (hZ : d.two ≤ W) (hE : W ≤ d.six)
    (hJW : J ≤ normalizer (W : Set G)) : W = d.two ∨ W = d.six := by
  by_cases hWZ : W ≤ d.two
  · exact Or.inl (le_antisymm hWZ hZ)
  · right
    apply le_antisymm hE (d.six_le_of_normalized_intersection W hZ hJW ?_)
    exact fun hh => hWZ ((le_inf hE le_rfl).trans hh)

end PairedBorelCoordinates
end BinaryPermutation.AlternatingFiveFlag
