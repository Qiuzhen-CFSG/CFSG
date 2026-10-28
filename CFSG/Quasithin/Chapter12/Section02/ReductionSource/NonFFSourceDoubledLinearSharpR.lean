module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearNearOffenders
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearOddControl
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddCodimension
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.OddSubgroups

/-!
# E.6.27 for the original nonbinary doubled linear-three source

The actual near-offender theorem supplies Thompson centralization, and the
original odd-local theorem supplies the odd-normalizer premise. An explicit
odd-prime displacement estimate then gives the local Cartan bound required by
E.6.27. Its conclusion covers every original subspace of corank below 4n,
including the verification that such a subspace is nonzero. Consequently the
full original parameter r is at least 4n.

Only the odd-prime displacement estimate remains an explicit premise here;
this file does not assert that estimate for an arbitrary pair normalizer.
Source: Aschbacher--Smith 7.4.1 and E.6.27, printed pp.700 and257.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
open Chapter4.Section04.NormalizedRankOneOddControl
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal E.6.27 centralizer conclusion for every original subspace of
corank below 4n, conditional only on the odd-prime displacement estimate. -/
theorem sourceOrbit_linear_centralizer_le_of_odd_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 4*F.degree ≤
        fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a))
    (U : Subgroup G) (hUW : U ≤ D.sourceOrbit)
    (hsmall : subgroupCorank D.sourceOrbit U < 4*F.degree) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hU : U ≠ ⊥ := by
    rintro rfl
    rw [Section06.corank_bot,D.sourceOrbit_linear_dimension h hd F hmodel] at hsmall
    omega
  have hr : (1 : ℕ∞) < globalR D.sourceOrbit := by
    have hi : (1 : ℕ∞) < ((2*F.degree : ℕ) : ℕ∞) := by
      exact_mod_cast (by omega : 1 < 2*F.degree)
    exact hi.trans_le (D.sourceOrbit_linear_initial_globalR h hd F hn hmodel)
  have hcartan : Section06.FixedPointBounds.nPrime (inducedAutomizer D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤ 1 := by
    apply induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit
      (normalizer (L : Set G) ⊓ centralizer (U : Set G)) U
      (inf_le_left.trans (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge)
      hUW inf_le_right (b := 4*F.degree) (c := 1)
    · intro p hp ho a ha
      simpa only [one_mul] using hodd p hp ho a ha
    · simpa only [one_mul] using hsmall
  apply centralizer_le_of_abelian_odd_control
    (D.sourceOrbit_hypothesisE61_of_markedDoubled h hd) hU hUW
    (j := 1) le_rfl hr hcartan
    (D.sourceOrbit_linear_local_thompson_one h hd F hn hmodel U hUW)
  intro B hB hBC hBo hcomm
  let := hcomm
  exact D.sourceOrbit_linear_oddNormalizer_le h hd F hn hmodel B hB
    (hBC.trans inf_le_right) hBo

/-- The sharp lower bound uses the full original r-domain. The odd-prime
displacement estimate is retained explicitly for its separate source proof. -/
theorem sourceOrbit_linear_globalR_of_odd_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
      orderOf a = p → 4*F.degree ≤
        fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a)) :
    ((4*F.degree : ℕ) : ℕ∞) ≤ globalR D.sourceOrbit := by
  by_contra! hr
  obtain ⟨U,hUW,hescape,hcor⟩ := Section06.globalR_attained (ne_top_of_lt hr)
  have hsmall : subgroupCorank D.sourceOrbit U < 4*F.degree := by
    have hlt : (subgroupCorank D.sourceOrbit U : ℕ∞) < ((4*F.degree : ℕ) : ℕ∞) :=
      hcor ▸ hr
    exact_mod_cast hlt
  apply hescape
  exact (D.sourceOrbit_linear_centralizer_le_of_odd_fixedCodim
    h hd F hn hmodel hodd U hUW hsmall).trans
      (D.sourceOrbit_normalizer_eq_of_markedDoubled h hd).ge

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
