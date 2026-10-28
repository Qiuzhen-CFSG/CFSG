module
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalMinus
/-!
# Complete even orthogonal Case II

The actual double sign changes invert one torus coordinate and fix another.
Though these elements need not normalize the selected root subgroup, the
global central cover forces its local torus lifts to commute. Thus a
nonbinary plus quotient of rank at least three is impossible, and a minus
quotient has rank at most three. The completed binary parabolic bounds and
rank-two/three linear and unitary identifications resolve all other cases.

The original source counterexample and proper-section induction are retained.
No quasithinness of its central quotient is inferred.
Source: Aschbacher--Smith A.2.15(2), A.2.18, printed pp.37--40.
-/
public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G] [IsQuasisimple G]

/-- Global double-flip inverters exclude every nonbinary plus quotient in the simple range. -/
theorem not_orthogonalPlus_nonbinary_center_quotient (hG : IsQuasithin G)
    {r a : ℕ} (ha : 1 < a) (hr : 3 ≤ r)
    (iso : ClassicalGroup.IsPOmegaPlus (G ⧸ center G) r (2 ^ a)) : False := by
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by
    rw [hc]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) ha
  let f := centralQuotientCover e
  exact ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers.not_quasithin_plus
    hr hq f.toMonoidHom f.surjective f.ker_le_center hG

/-- A nonbinary minus central quotient has rank at most three in the original quasithin group. -/
theorem nonbinary_orthogonalMinus_center_quotient_rank_le_three (hG : IsQuasithin G)
    {r a : ℕ} (ha : 1 < a)
    (iso : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) r (2 ^ a)) : r ≤ 3 := by
  by_contra hr
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hq : 2 < Nat.card F := by
    rw [hc]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) ha
  let f := centralQuotientCover e
  exact ClassicalOrthogonal.TheoremDRootNormalizer.HigherRanks.CentralCovers.not_quasithin_minus
    (by omega) hq f.toMonoidHom f.surjective f.ker_le_center hG

variable {K : GroupClass.{u}} {S : Type u} [Group S] [Finite S] {p : ℕ}

/-- All plus-type even-characteristic central quotients are excluded in original Case II. -/
theorem caseII_orthogonalPlus_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {r a : ℕ} (ha : 0 < a) (hp : KnownSimple.OrthogonalPlusParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaPlus (G ⧸ center G) r (2 ^ a)) : False := by
  by_cases hb : a = 1
  · exact caseII_orthogonalPlus_binary_of_source h ih hp.2 (by simpa [hb] using iso)
  · exact not_orthogonalPlus_nonbinary_center_quotient h.1 (by omega) hp.2 iso

/-- All minus-type even-characteristic central quotients are excluded in original Case II. -/
theorem caseII_orthogonalMinus_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {r a : ℕ} (ha : 0 < a) (hp : KnownSimple.OrthogonalMinusParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaMinus (G ⧸ center G) r (2 ^ a)) : False := by
  by_cases hb : a = 1
  · exact caseII_orthogonalMinus_binary_of_source h ih hp.2 (by simpa [hb] using iso)
  · have hr := nonbinary_orthogonalMinus_center_quotient_rank_le_three h.1 (by omega) iso
    have hr' : r = 2 ∨ r = 3 := by have := hp.2; omega
    rcases hr' with rfl | rfl
    · exact caseII_orthogonalMinus_two_of_source h ih ha iso
    · exact caseII_orthogonalMinus_three_of_source h ih ha iso
end CFSG.Quasithin.ChapterA.Section02.EvenLie
