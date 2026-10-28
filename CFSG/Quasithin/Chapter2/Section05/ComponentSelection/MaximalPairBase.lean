module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.MaximalPairs

/-!
# Saturated pairs preserving the largest source base

For the superscript-star family, start with its globally largest base and
maximize the local pair above that witness. Componentwise maximality then
supplies saturation without losing the largest-base condition. A replacement
containing the same pair and an original Sylow subgroup consequently preserves
both starred families. Choosing an arbitrary maximal pair would not establish
the superscript-star condition.

Source: Aschbacher--Smith 2.5.3(4), printed pp.552--553, applying 2.3.7(3--4).
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M H U₀ HU₀ : Subgroup G}

/-- Maximize the pair above a prescribed original pair, retaining its base. -/
theorem exists_saturated_pair_above
    (h₀ : (U₀, HU₀) ∈ localPairsIn (Chapter1.He G) M H) :
    ∃ U HU : Subgroup G, (U, HU) ∈ localPairsIn (Chapter1.He G) M H ∧
      U₀ ≤ U ∧ HU₀ ≤ HU ∧
      (∀ V K, (V, K) ∈ localPairsIn (Chapter1.He G) M H →
        U ≤ V → HU ≤ K → V ≤ U ∧ K ≤ HU) ∧
      ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
        HU ≤ normalizer (P : Set G) → P ≤ twoCore HU := by
  let I : Set (Subgroup G × Subgroup G) :=
    {P | P ∈ localPairsIn (Chapter1.He G) M H ∧ (U₀, HU₀) ≤ P}
  have hI : I.Nonempty := ⟨(U₀, HU₀), h₀, le_rfl⟩
  obtain ⟨⟨U, HU⟩, hmem, hm⟩ := I.toFinite.exists_maximal hI
  have hmax : ∀ V K, (V, K) ∈ localPairsIn (Chapter1.He G) M H →
      U ≤ V → HU ≤ K → V ≤ U ∧ K ≤ HU := by
    intro V K hv hUV hHK
    exact hm ⟨hv, hmem.2.trans ⟨hUV, hHK⟩⟩ ⟨hUV, hHK⟩
  exact ⟨U, HU, hmem.1, hmem.2.1, hmem.2.2, hmax,
    saturation_of_maximal_pair hmem.1 hmax⟩

/-- The source maximal pair can always be chosen to retain the globally
largest-base witness whenever the original group lies in Gamma-star. -/
theorem exists_saturated_pair_preserving_star
    (hH : H ∈ gammaZero (Chapter1.He G) M) :
    ∃ U HU : Subgroup G, (U, HU) ∈ localPairsIn (Chapter1.He G) M H ∧
      (H ∈ gammaStar (Chapter1.He G) M →
        ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U) ∧
      ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
        HU ≤ normalizer (P : Set G) → P ≤ twoCore HU := by
  classical
  by_cases hs : H ∈ gammaStar (Chapter1.He G) M
  · obtain ⟨⟨U₀, HU₀⟩, hp, hbig⟩ := hs.1.2
    obtain ⟨U, HU, hp, hU, _hHU, _hm, hsat⟩ := exists_saturated_pair_above hp
    refine ⟨U, HU, hp, fun _ V hV => (hbig V hV).trans ?_, hsat⟩
    exact Nat.card_le_card_of_injective (inclusion hU) (inclusion_injective hU)
  · have hg : H ∈ gamma (Chapter1.He G) M :=
      hH.elim (fun h => h.1.1) (fun h => h.1)
    obtain ⟨U, HU, hp, _hm, hsat⟩ := exists_saturated_local_pair hg
    exact ⟨U, HU, hp, fun h => (hs h).elim, hsat⟩

/-- Keeping the selected pair and original Sylow subgroup preserves both
source stars in the replacement subgroup. -/
theorem replacement_preserves_stars
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    {U HU X : Subgroup G}
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hbig : H ∈ gammaStar (Chapter1.He G) M →
      ∀ V ∈ localBases (Chapter1.He G) M, Nat.card V ≤ Nat.card U)
    (S : Sylow 2 H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hHUX : HU ≤ X) (hSX : (S : Subgroup H).map H.subtype ≤ X)
    (hXcore : twoCore X ≠ ⊥) :
    X ∈ gammaZero (Chapter1.He G) M ∧
      (∃ R : Sylow 2 X, (R : Subgroup X).map X.subtype =
        (S : Subgroup H).map H.subtype) ∧
      (∃ R : Sylow 2 ↥(X ⊓ M), (R : Subgroup ↥(X ⊓ M)).map (X ⊓ M).subtype =
        (S : Subgroup H).map H.subtype) ∧
      (H ∈ gammaStar (Chapter1.He G) M → X ∈ gammaStar (Chapter1.He G) M) ∧
      (H ∈ gammaMax (Chapter1.He G) M → X ∈ gammaMax (Chapter1.He G) M) := by
  have hpX : (U, HU) ∈ localPairsIn (Chapter1.He G) M X := ⟨hpair.1, hHUX⟩
  exact lemma_2_3_7_3 hH hpair S hUS ⟨hXcore, ⟨(U, HU), hpX⟩⟩ hSX
    (fun h => ⟨hbig h, HU, hpX⟩)

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
