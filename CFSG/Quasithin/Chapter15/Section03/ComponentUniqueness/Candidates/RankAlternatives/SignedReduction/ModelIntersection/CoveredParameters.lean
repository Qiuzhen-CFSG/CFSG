module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.SpecificGroups.SU3.EvenTwoRank

/-!
# Signed parameters in the central two-cover alternative

The actual quotient in 1.1.5(3b) is PSL₃(4) or G₂(4). Their two-ranks are
four and six, respectively. The odd-parameter bound therefore forces any
signed degree-three model of this quotient to have parameter q = 2ⁿ.
The concrete linear and unitary two-ranks are 2n and n. For PSL₃(4), these
leave q = 4 or unitary q = 16; the latter violates q ≡ −1 (mod 3). For
G₂(4), they leave linear q = 8 or unitary q = 64, each violating its signed
congruence. Thus only the linear PSL₃(4) parameter survives.

All rank comparisons use actual carrier isomorphisms. In the unitary case
q is the fixed-field order and the matrix field has order q². The theorem
`covered_parameters` supplies precisely the `hCover` premise of
`ModelIntersection.intersection_of_carrier_comparisons`; its group is the
parent's quotient K/O₂(K), and no assertion about O₂(K) is made here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.18(2)
(printed pp.51--52), 1.1.5(3b) (pp.501--503), and the intersections used
on pp.1135 and 1139. The concrete rank proofs cite the rank table on p.356.
-/

public section

open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection.CoveredParameters
open Chapter1.Section02.LocalModels ClassificationModels
variable {S : Type*} [Group S] [Finite S] {unitary : Bool} {q n : ℕ}

private theorem signed_binary_twoRank (hn : 0 < n)
    (h : IsPSLSign S unitary 3 (2 ^ n)) :
    primeRank 2 S = if unitary then n else 2 * n := by
  cases unitary with
  | false =>
    obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
    exact (primeRank_equiv 2 e).trans (Matrix.PSL3Even.two_rank F hn hc)
  | true =>
    obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := h
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    exact (primeRank_equiv 2 e).trans
      (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J hn hc hconj)

private theorem psl_four_twoRank (h : ClassicalGroup.IsPSL S 3 4) :
    primeRank 2 S = 4 := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  exact (primeRank_equiv 2 e).trans
    (Matrix.PSL3Even.two_rank F (n := 2) (by decide) hc)

private theorem gTwo_four_twoRank (h : IsG2At S 4) : primeRank 2 S = 6 := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := h
  exact (primeRank_equiv 2 e).trans (Atlas.G2.EvenTwoRank.two_rank F (n := 2) hc)

/-- The supplied signed parameter for PSL₃(4) is uniquely linear with q = 4. -/
theorem psl_four_signed_parameters (hmodel : ClassicalGroup.IsPSL S 3 4)
    (hmod : q % 3 = (if unitary then 2 else 1))
    (hsigned : IsPSLSign S unitary 3 q) : unitary = false ∧ q = 4 := by
  have hr := psl_four_twoRank hmodel
  obtain ⟨n, hn, hq⟩ := signed_parameter_binary hsigned
    (signed_even_of_twoRank hsigned (by omega))
  have hs := signed_binary_twoRank hn (hq ▸ hsigned)
  cases unitary with
  | false =>
    change primeRank 2 S = 2 * n at hs
    have hn2 : n = 2 := by omega
    exact ⟨rfl, by simpa [hn2] using hq⟩
  | true =>
    change primeRank 2 S = n at hs
    have hn4 : n = 4 := by omega
    norm_num [hq, hn4] at hmod

/-- The actual G₂(4) carrier has no signed degree-three model satisfying
the source congruence. -/
theorem not_gTwo_four_signed (hmodel : IsG2At S 4)
    (hmod : q % 3 = (if unitary then 2 else 1))
    (hsigned : IsPSLSign S unitary 3 q) : False := by
  have hr := gTwo_four_twoRank hmodel
  obtain ⟨n, hn, hq⟩ := signed_parameter_binary hsigned
    (signed_even_of_twoRank hsigned (by omega))
  have hs := signed_binary_twoRank hn (hq ▸ hsigned)
  cases unitary with
  | false =>
    change primeRank 2 S = 2 * n at hs
    have hn3 : n = 3 := by omega
    norm_num [hq, hn3] at hmod
  | true =>
    change primeRank 2 S = n at hs
    have hn6 : n = 6 := by omega
    norm_num [hq, hn6] at hmod

/-- The exact central-cover comparison required by the model-intersection
assembly, applied to the simple quotient rather than the original component. -/
theorem covered_parameters (S : Type*) [Group S] [Finite S]
    [IsQuasisimple S] [IsSimpleGroup S]
    (hmodel : ClassicalGroup.IsPSL S 3 4 ∨ IsG2At S 4)
    (unitary : Bool) (q : ℕ) (hmod : q % 3 = (if unitary then 2 else 1))
    (hsigned : IsPSLSign S unitary 3 q) :
    unitary = false ∧ q = 4 ∧ ClassicalGroup.IsPSL S 3 4 := by
  rcases hmodel with hmodel | hmodel
  · obtain ⟨hu, hq⟩ := psl_four_signed_parameters hmodel hmod hsigned
    exact ⟨hu, hq, hmodel⟩
  · exact (not_gTwo_four_signed hmodel hmod hsigned).elim

end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection.CoveredParameters
