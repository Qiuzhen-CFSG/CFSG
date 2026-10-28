module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Source
public import Theory.GroupTheory.SolvableNormalAbelian
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import FeitThompson.FinalTheorem

/-!
# From abelian odd control to the literal E.6.27 hypothesis

Every nontrivial odd-order group has a nontrivial characteristic abelian
subgroup: apply the odd-order theorem and take the last nontrivial derived
term. The ambient normalizer preserves its embedded image. Consequently
the abelian control supplied by normalized 4.4.3 suffices for every odd
subgroup in the actual hypothesis of E.6.27. No normality in G is asserted.

The final theorem applies this reduction to the original E.6.27 centralizer
conclusion. The abelian source theorem remains an explicit premise here.
Source: Aschbacher--Smith, Remark 4.4.2 and 7.4.1, printed pp.619,699--700,
and Proposition E.6.27, printed p.257.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB ChapterE.Section06 ChapterE.Section06.FixedPointBounds
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The abelian version controls the full normalizer of every nontrivial
odd subgroup of the same literal relative centralizer. -/
theorem odd_normalizer_control_of_abelian {M W : Subgroup G}
    (habel : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ M ⊓ centralizer (W : Set G) →
      Odd (Nat.card B) → IsMulCommutative B → normalizer (B : Set G) ≤ M)
    (X : Subgroup G) (hne : X ≠ ⊥)
    (hX : X ≤ M ⊓ centralizer (W : Set G)) (hodd : Odd (Nat.card X)) :
    normalizer (X : Set G) ≤ M := by
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hne
  let : Group.IsSolvable X := odd_order_theorem X hodd
  obtain ⟨A, hchar, hcomm, hA⟩ := Group.exists_nontrivial_abelian_characteristic X
  let := hchar
  let := hcomm
  have hneA : A.map X.subtype ≠ ⊥ := by
    intro he
    exact hA ((A.map_eq_bot_iff_of_injective X.subtype_injective).mp he)
  have hoA : Odd (Nat.card (A.map X.subtype)) :=
    hodd.of_dvd_nat (card_dvd_of_le (map_subtype_le A))
  exact (normalizer_le_normalizer_characteristic_image X A).trans
    (habel _ hneA ((map_subtype_le A).trans hX) hoA inferInstance)

/-- Actual E.6.27 application with precisely the abelian odd-local premise
used in 7.4.1; the arbitrary-odd premise is discharged above. -/
theorem centralizer_le_of_abelian_odd_control
    {T : Sylow 2 G} {M W U : Subgroup G}
    (h : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hU : U ≠ ⊥) (hUW : U ≤ W) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (j : ℕ∞) < ChapterE.globalR W)
    (hn : nPrime (ChapterE.inducedAutomizer W
      (M ⊓ centralizer (U : Set G))) ≤ j)
    (hJ : thompsonJ (M ⊓ centralizer (U : Set G)) j ≤
      M ⊓ centralizer (W : Set G))
    (habel : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ M ⊓ centralizer (W : Set G) →
      Odd (Nat.card B) → IsMulCommutative B → normalizer (B : Set G) ≤ M) :
    centralizer (U : Set G) ≤ M :=
  ChapterE.Section06.FixedPointBounds.source_proposition_E_6_27 h hU hUW
    hj1 hj hn hJ (odd_normalizer_control_of_abelian habel)

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
