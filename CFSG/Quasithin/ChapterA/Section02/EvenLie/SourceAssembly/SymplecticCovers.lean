module

public import Theory.SpecificGroups.Symplectic.TheoremDRootNormalizer.OddCentral
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.RankOneAliases
public import CFSG.Quasithin.ChapterA.Section02.EvenLie.SourceAssembly.OrthogonalSimple

/-!
# Symplectic and odd orthogonal Case II in the original source induction

A proper binary Sp6 section bounds the rank of the original central quotient
by three. Rank one and two use the completed covering calculations. In rank
three over a larger even field, independently inverted torus coordinates
lift through the original odd center to a rank-three elementary subgroup
in an actual two-local subgroup of G. The remaining binary rank-three cover
has a two-group kernel and is excluded by the original offending prime.
The literal odd orthogonal comparison then closes that entire family too.

Source: Aschbacher--Smith A.2.15(2) and A.2.18, printed pp.37--40.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02.EvenLie
universe u
variable {G : Type u} [Group G] [Finite G] [IsQuasisimple G]
  {K : GroupClass.{u}} {S : Type u} [Group S] [Finite S] {p : ℕ}

/-- The original odd center permits lifting the split torus of every nonbinary Sp6 quotient. -/
theorem caseII_symplectic_three_nonbinary_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {a : ℕ} (ha : 1 < a)
    (iso : ClassicalGroup.IsPSp (G ⧸ center G) 3 (2 ^ a)) : False := by
  obtain ⟨F,hF,hfin,hc,⟨e⟩⟩ := iso
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  have hcard : 2 < Nat.card F := by
    rw [hc]
    exact (by norm_num : (2 : ℕ) = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) ha
  exact Theory.SpecificGroups.SymplecticRoot.OddCentral.not_quasithin_of_odd_center
    hcard (center_odd_of_source h ih) e h.1

/-- Every even-characteristic symplectic Case II is excluded under the original source hypotheses. -/
theorem caseII_symplectic_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {r a : ℕ} (ha : 0 < a) (hp : KnownSimple.SymplecticParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPSp (G ⧸ center G) r (2 ^ a)) : False := by
  have hr := symplectic_center_quotient_rank_le_three ih h.1 h.2.1 ha iso
  have hmin := hp.2.1
  interval_cases r
  · have ha2 : 2 ≤ a := by
      have hh := hp.2.2.1 rfl
      by_contra hn
      have : a = 1 := by omega
      simp [this] at hh
    exact caseII_symplectic_one_of_source h ih ha2 iso
  · exact caseII_symplectic_two_of_source h ih iso
  · by_cases ha1 : a = 1
    · exact caseII_binary_symplectic_six_of_source h ih (by simpa [ha1] using iso)
    · exact caseII_symplectic_three_nonbinary_of_source h ih (by omega) iso

/-- The literal characteristic-two odd orthogonal comparison completes that source family. -/
theorem caseII_orthogonalOdd_of_source
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    {r a : ℕ} (ha : 0 < a) (hp : KnownSimple.OrthogonalOddParameters r (2 ^ a))
    (iso : ClassicalGroup.IsPOmegaOdd (G ⧸ center G) r (2 ^ a)) : False :=
  caseII_symplectic_of_source h ih ha hp (odd_orthogonal_symplectic hp.2.1 iso)

end CFSG.Quasithin.ChapterA.Section02.EvenLie
