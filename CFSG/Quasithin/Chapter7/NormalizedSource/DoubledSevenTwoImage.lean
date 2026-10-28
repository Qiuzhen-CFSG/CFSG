module
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Source
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddCodimension

/-!
# E.6.27 for a two-group centralizer image in the A₇ row

The H.8 near-offender exclusion forces the first higher Thompson subgroup
of the literal local centralizer to fix the whole orbit. A two-group image
has no nontrivial odd Cartan witness, so its E.3.37 parameter is one.
E.6.27 then controls the full ambient centralizer, retaining its original
odd-subgroup normalizer hypothesis. No global-r bound is assumed beyond
the previously proved hyperplane bound.

NonFFSourceDoubledSevenTwoImage supplies the actual chosen-module
application. The odd-normalizer hypothesis still requires the original
4.4.3 proof before this branch can be used unconditionally in 7.5.5.
Source: Aschbacher--Smith H.8, E.6.27 and 7.5.5, pp.389,257,701.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.AlternatingSevenConjugatePair
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds ChapterH.AlternatingPair
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M W U : Subgroup G}

/-- H.8 excludes every moving generator of the actual local J₁. -/
theorem doubledSeven_local_thompson [IsElementaryAbelian 2 W]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hno : ∀ A, ¬ IsFMinusOneOffender (automizerRepresentation W) A)
    (hU : U ≠ ⊥) (hUW : U ≤ W) :
    ChapterB.thompsonJ (M ⊓ centralizer (U : Set G)) 1 ≤ M ⊓ centralizer (W : Set G) := by
  refine le_inf (ChapterB.thompsonJ_le _ _ |>.trans inf_le_left) ?_
  apply thompson_centralizes_of_fixedCodim_gap W _
    (le_inf (h.le_sylow.trans h.sylow_le)
      (W.le_centralizer.trans (Subgroup.centralizer_le hUW)))
    (h.localCentralizer_le_normalizer hU hUW)
  intro A hA
  exact lt_of_not_ge (fun hc => hno A ⟨hA,hc⟩)

/-- The two-group-image branch of 7.5.5, retaining the original odd-local premise. -/
theorem doubledSeven_two_image_centralizer [IsElementaryAbelian 2 W]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M W)
    (hr : 1 < globalR W)
    (hno : ∀ A, ¬ IsFMinusOneOffender (automizerRepresentation W) A)
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ M ⊓ centralizer (W : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ M)
    (hU : U ≠ ⊥) (hUW : U ≤ W)
    (htwo : IsPGroup 2 (inducedAutomizer W (M ⊓ centralizer (U : Set G)))) :
    centralizer (U : Set G) ≤ M := by
  apply source_proposition_E_6_27 h hU hUW (j := 1) le_rfl hr ?_
    (doubledSeven_local_thompson h hno hU hUW) hodd
  apply nPrime_le_one_of_no_odd_prime
  intro p hp ho x hx
  have hd := orderOf_dvd_natCard x
  rw [hx] at hd
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  rw [hn] at hd
  have he : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)).resolve_left hp.ne_one
  exact ho.not_two_dvd_nat (he ▸ dvd_rfl)
end CFSG.Quasithin.Chapter7.NormalizedSource
