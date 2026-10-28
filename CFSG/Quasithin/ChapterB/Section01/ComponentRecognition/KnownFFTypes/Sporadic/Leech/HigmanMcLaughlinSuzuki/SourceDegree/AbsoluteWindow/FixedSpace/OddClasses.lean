module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses.Five
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses.Three
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OddClassBound.PrimeCases
public import Mathlib.Data.Set.Card

/-!
# HS odd-class counting from the two remaining small-prime covers

The carrier order and the fixed-point exclusion of order 77 reduce odd orders
prime to fifteen to one, seven and eleven. The checked prime-class calculations
give one representative at seven and two at eleven. The identity completes a
four-element cover of this branch.

Adjoining a two-element cover of the three-divisibility branch and a three-element
cover of the remaining five-divisibility branch gives nine representatives for
all odd-order elements. Passing to actual conjugacy classes and counting the
image proves exactly `OddClassBound`.

Source: the HS class list in the ATLAS and CTblLib 1.3.11, `ctospora.tbl`.
The consumer is `FixedSpace.finrank_eq_one_or_twenty_of_models`, used in the
HS case of Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace

open _root_.Sporadic.LeechRelated.HS.OddClassBound

/-- The trivial, seven and two eleven classes cover the odd-order elements
prime to fifteen. All conjugacy statements use the actual HS carrier. -/
theorem odd_primeToFifteen_cover :
    ∃ r : Fin 4 → KnownSimple.SporadicName.hs.Carrier,
      ∀ g : KnownSimple.SporadicName.hs.Carrier,
        Odd (orderOf g) → ¬ 3 ∣ orderOf g → ¬ 5 ∣ orderOf g →
          ∃ i, IsConj g (r i) := by
  refine ⟨![1, seven, eleven, eleven ^ 2], ?_⟩
  intro g ho h3 h5
  rcases TraceField.odd_order_cases_of_not_three_five g ho h3 h5 with h | h | h
  · refine ⟨0, ?_⟩
    change IsConj g 1
    rw [orderOf_eq_one_iff.mp h]
  · exact ⟨1, orderSeven_conjugate g h⟩
  · rcases orderEleven_conjugate g h with hc | hc
    · exact ⟨2, hc⟩
    · exact ⟨3, hc⟩

private theorem card_classes_le_of_cover {G I : Type*} [Group G] [Finite I]
    (s : Set G) (r : I → G) (hc : ∀ g ∈ s, ∃ i, IsConj g (r i)) :
    Nat.card (ConjClasses.mk '' s) ≤ Nat.card I := by
  classical
  let f : I → ConjClasses G := fun i => ConjClasses.mk (r i)
  have hsub : ConjClasses.mk '' s ⊆ Set.range f := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi⟩ := hc g hg
    exact ⟨i, (ConjClasses.mk_eq_mk_iff_isConj.mpr hi).symm⟩
  calc
    Nat.card (ConjClasses.mk '' s) ≤ Nat.card (Set.range f) :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    _ ≤ Nat.card I :=
      Nat.card_le_card_of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective

/-- Exact assembly for the modular-saturation consumer. Its two independent
coverage premises concern actual elements and must still be constructed. -/
theorem oddClassBound_of_small_prime_covers
    (hthree : OddThreeClassCover) (hfive : OddFiveClassCover) : OddClassBound := by
  intro hs
  obtain ⟨r3, h3⟩ := hthree hs
  obtain ⟨r5, h5⟩ := hfive hs
  obtain ⟨r0, h0⟩ := odd_primeToFifteen_cover
  let I := Fin 2 ⊕ (Fin 3 ⊕ Fin 4)
  let r : I → KnownSimple.SporadicName.hs.Carrier := Sum.elim r3 (Sum.elim r5 r0)
  have hcard : Nat.card I = 9 := by simp [I, Nat.card_eq_fintype_card]
  rw [← hcard]
  apply card_classes_le_of_cover _ r
  intro g hg
  have ho : Odd (orderOf g) := Nat.not_even_iff_odd.mp (fun h => hg h.two_dvd)
  by_cases hd3 : 3 ∣ orderOf g
  · obtain ⟨i, hi⟩ := h3 g ho hd3
    exact ⟨Sum.inl i, hi⟩
  by_cases hd5 : 5 ∣ orderOf g
  · obtain ⟨i, hi⟩ := h5 g ho hd3 hd5
    exact ⟨Sum.inr (Sum.inl i), hi⟩
  · obtain ⟨i, hi⟩ := h0 g ho hd3 hd5
    exact ⟨Sum.inr (Sum.inr i), hi⟩

/-- The checked three- and five-divisibility covers complete the odd-class
bound for the actual HS carrier. -/
theorem oddClassBound : OddClassBound :=
  oddClassBound_of_small_prime_covers oddThreeClassCover oddFiveClassCover

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace
