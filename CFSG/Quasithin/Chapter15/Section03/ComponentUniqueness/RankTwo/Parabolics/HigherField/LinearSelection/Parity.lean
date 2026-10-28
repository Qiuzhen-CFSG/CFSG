module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.LinearSelection.BorelTransport
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure

/-!
# Parity in the linear larger-field branch

The projective PSL₃ Borel has order prime to three when the binary field
degree is odd. This property transfers to the original component Borel
through its central two-kernel, contradicting the earlier rank-two actor
Y₊ ≤ B. Thus the field degree in the linear branch is even.

This proves the parity assertion after the linear family is identified;
it does not select that family from the other rank-two models.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final proof
of 15.3.35, printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection

variable {D : Type*} [Group D] [Finite D]

/-- Odd field degree excludes three in every marked projective Sylow normalizer. -/
theorem three_not_dvd_normalizer_of_odd_psl3 {n : ℕ} (hn : Odd n)
    (hmodel : ClassicalGroup.IsPSL D 3 (2^n)) (P : Sylow 2 D) :
    ¬ 3 ∣ Nat.card (normalizer (P : Set D)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hN : (normalizer (P : Set D)).map e.toMonoidHom =
      normalizer (Q : Set PSL(3,F)) := P.normalizer_map_surjective e.toMonoidHom e.surjective
  have hc : Nat.card (normalizer (Q : Set PSL(3,F))) = Nat.card (normalizer (P : Set D)) := by
    rw [← hN, card_map_of_injective e.injective]
  rw [← hc]
  exact Matrix.PSL3.LinearThree.BorelStructure.three_not_dvd_card_sylowNormalizer_of_odd
    F hn hF Q

variable {G : Type*} [Group G] [Finite G]

/-- The linear component branch has even degree, including central two-covers. -/
theorem even_degree_of_linear_component
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL (componentImage I L L) 3 (2^n)) : Even n := by
  by_contra hn
  have ho : Odd n := Nat.not_even_iff_odd.mp hn
  exact no_three_free_component_borel I L M Yplus S B c hB hYB
    (three_not_dvd_normalizer_of_odd_psl3 ho hmodel)
end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection
