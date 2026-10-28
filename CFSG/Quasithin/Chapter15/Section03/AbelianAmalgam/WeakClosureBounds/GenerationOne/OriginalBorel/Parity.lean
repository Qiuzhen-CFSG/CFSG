module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.RankOneTori
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.HigherRankTori

/-!
# The defining torus in the original marked component Borel

Each characteristic-two model supplies an actual injection of defining-field
units into the marked component intersection in H/J. Its order divides the
original maximal subgroup's order. A three-prime maximal intersection therefore
forces the defining exponent to be odd, without equating it to n(H).

Source: Aschbacher--Smith E.2.2, printed pp.215--216, and the first paragraph
of the proof of 15.3.65, printed p.1152.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H]

/-- The defining field torus lies in the literal marked component Borel. -/
def HasSourceTorus (M K : Subgroup H) (f : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
    ∃ i : Fˣ →* componentOverlap M K, Function.Injective i

private theorem torus_of_pair {F X : Type*} [Field F] [Finite F] [Group X]
    {M K : Subgroup H} {B : Subgroup X} (h : ModelBorelPair M K B)
    (i : Fˣ →* B) (hi : Function.Injective i) :
    ∃ j : Fˣ →* componentOverlap M K, Function.Injective j := by
  obtain ⟨e, he⟩ := h
  let b := (e.subgroupMap (componentOverlap M K)).trans (MulEquiv.subgroupCongr he)
  exact ⟨b.symm.toMonoidHom.comp i, b.symm.injective.comp hi⟩

theorem exchanged_torus {M K : Subgroup H} {f : ℕ}
    (h : ExchangedModel M K f) : HasSourceTorus M K f := by
  rcases h with ⟨F,hF,hfin,hc,_,hcard,hp⟩ | ⟨m,hm,rfl,hp⟩
  · exact ⟨F,hF,hfin,hcard,torus_of_pair hp BorelReduction.psl2Torus BorelReduction.psl2Torus_injective⟩
  · refine ⟨BenderSuzuki.PFAppendixIII.BinaryGaloisField (2*m+1), inferInstance, inferInstance, ?_, ?_⟩
    · simpa [BenderSuzuki.PFAppendixIII.BinaryGaloisField] using GaloisField.card 2 (2*m+1) (by omega)
    · exact torus_of_pair hp (BorelReduction.suzukiTorus m hm) (BorelReduction.suzukiTorus_injective m hm)

theorem unitary_torus {M K : Subgroup H} {f : ℕ}
    (h : UnitaryModel M K f) : HasSourceTorus M K f := by
  obtain ⟨F,hF,hfin,hc,J,hJ,hf,hcard,hconj,_,hp⟩ := h
  exact ⟨BorelReduction.unitaryFixedField J,inferInstance,inferInstance,
    BorelReduction.unitaryFixedField_card J f (by omega) hcard hconj,
    torus_of_pair hp (BorelReduction.psu3Torus J hJ) (BorelReduction.psu3Torus_injective J hJ)⟩

theorem bender_torus {M K : Subgroup H} {f : ℕ}
    (h : BenderModel M K f) : HasSourceTorus M K f := by
  rcases h with h | h
  · exact exchanged_torus h
  · exact unitary_torus h

theorem diagram_torus {M K T : Subgroup H} {f : ℕ}
    (h : DiagramModel M K T f) : HasSourceTorus M K f := by
  rcases h with ⟨F,hF,hfin,hc,_,hcard,e,hB,_⟩ | ⟨F,hF,hfin,hc,_,hcard,e,hB,_⟩
  · exact ⟨F,hF,hfin,hcard,torus_of_pair ⟨e,hB⟩ (BorelReduction.psl3Torus F)
      (BorelReduction.psl3Torus_injective F)⟩
  · exact ⟨F,hF,hfin,hcard,torus_of_pair ⟨e,hB⟩ BorelReduction.sp4DerivedTorus
      BorelReduction.sp4DerivedTorus_injective⟩

theorem HasSourceTorus.card_dvd {M K : Subgroup H} {f : ℕ}
    (h : HasSourceTorus M K f) : 2^f-1 ∣ Nat.card M := by
  obtain ⟨F,hF,hfin,hcard,i,hi⟩ := h
  have ht : 2^f-1 ∣ Nat.card (componentOverlap M K) := by
    simpa only [Nat.card_units,hcard] using card_dvd_of_injective i hi
  have he : Nat.card (componentOverlap M K) = Nat.card (sourceImage M (M ⊓ K)) :=
    Nat.card_congr (subgroupOfEquivOfLe (map_mono inf_le_right)).toEquiv
  rw [he] at ht
  exact ht.trans (((M ⊓ K).card_map_dvd (QuotientGroup.mk' (sourceKernel M))).trans
    (card_dvd_of_le inf_le_left))

theorem HasSourceTorus.odd {M K : Subgroup H} {f : ℕ}
    (h : HasSourceTorus M K f) (hthree : ¬3 ∣ Nat.card M) : Odd f := by
  apply odd_field_exponent_of_three_prime_intersection (M := M) (H := ⊤)
  · simpa only [inf_top_eq] using hthree
  · simpa only [inf_top_eq] using h.card_dvd

theorem reduced_torus {M K T : Subgroup H} {f : ℕ}
    (h : ReducedCases M K T f) : HasSourceTorus M K f := by
  cases h with
  | exchanged _ hm => exact exchanged_torus hm
  | bender _ hm => exact bender_torus hm
  | diagram _ hm => exact diagram_torus hm
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalBorel
