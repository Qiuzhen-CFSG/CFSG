module

public import Stellmacher.MainDefs
public import Stellmacher.MainType
public import Stellmacher.MainType.NonsolvableAddendum
public import Stellmacher.ExceptionalType
public import Stellmacher.SectionEleven.ReducedSetup
public import Stellmacher.SectionFiveToSeven.MaximalTwoLocal
public import Stellmacher.SectionEleven.MultipleMaximalBranch
public import Stellmacher.SectionEleven.UniqueMaximalBranch
public import Stellmacher.SectionEleven.TheoremOneTerminalContext
public import Stellmacher.SectionEleven.TheoremOneSylowBound
public import Stellmacher.SectionEleven.EightSixFullTerminal
public import Stellmacher.SectionEleven.MultipleNineOneType
public import Stellmacher.SectionEleven.TenOneFullTerminal
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionNine.LemmaNineTen


/-!
# Stellmacher's two main local classification theorems

Theorem 1 uses the source Baumann subgroup, built from the elementary
Thompson subgroup, and the eight precise local configurations defined in
`Stellmacher.MainType`. Its original hypotheses produce an actual terminal
graph on a pair with the prescribed Sylow. For commuting critical centers,
(7.5) and (9.10) leave distances one and three, handled by the full (9.1)
and (10.1) type realizations. For noncommuting centers, (8.2) and the full
(8.6) realization supply the other alternatives. The companion modules give
the Sylow bound and the nonsolvable two-local assertion for the last four
types. This is a local classification; model-amalgam recognition is separate.

For Theorem 2, the Section 11 reduction first disposes of alternatives (d)
and (e), constructs Hypothesis 1, and retains solvability and characteristic
two for every two-local. The maximal-two-local lattice then splits into the
proved multiple-maximal and unique-maximal branches, giving respectively
an exceptional local type or exactly alternatives (b) and (c). This proof is
independent of Theorem 1 and retains the explicit trivial-two-core hypothesis
whose necessity is documented below.

Source: `refs/latex/stellmacher-n-group.tex`, Theorems 1 and 2, the type
definitions following (8.2), (8.6), (9.1), (10.1), and Section 11.
-/

universe u

namespace Stellmacher

namespace SectionEleven

open SectionsFiveToSeven

private theorem theorem_two_logical_reduction
    {H : Type u} [Group H] [Finite H]
    (hN2 : IsNTwoGroup H) (hEven : Even (Nat.card H))
    (hTwoCore : pCore 2 H = ⊥)
    (S0 : Sylow 2 H)
    (hMultiple :
      HypothesisOne H S0 →
      (∀ U : Subgroup H, IsTwoLocal U →
        Group.IsSolvable U ∧ IsCharacteristicTwoType U) →
      (∃ P1 P2 : Subgroup H,
        P1 ≠ P2 ∧
        IsMaximalTwoLocal P1 ∧
        IsMaximalTwoLocal P2 ∧
        (S0 : Subgroup H) ≤ P1 ∧
        (S0 : Subgroup H) ≤ P2) →
      IsOfExceptionalType H)
    (hUnique :
      HypothesisOne H S0 →
      (∀ U : Subgroup H, IsTwoLocal U →
        Group.IsSolvable U ∧ IsCharacteristicTwoType U) →
      ∀ M : Subgroup H,
        UniqueMaximalTwoLocalContaining (S0 : Subgroup H) M →
        IsOfExceptionalType H ∨
          (IsDihedralGroup S0 ∨ IsSemidihedralGroup S0) ∨
          (Nat.card S0 = 2 ^ 5 ∧
            ∃ U : Subgroup H,
              IsMaximalTwoLocal U ∧
              Nonempty
                (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))))) :
    IsOfExceptionalType H ∨
    (IsDihedralGroup S0 ∨ IsSemidihedralGroup S0) ∨
    (Nat.card S0 = 2 ^ 5 ∧
      ∃ U : Subgroup H,
        IsMaximalTwoLocal U ∧
        Nonempty
          (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ M : Subgroup H, IsStronglyEmbedded M) ∨
    (∃ U : Subgroup H,
      IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥) := by
  by_cases hStrong : ∃ M : Subgroup H, IsStronglyEmbedded M
  · exact Or.inr (Or.inr (Or.inr (Or.inl hStrong)))
  by_cases hOddCore : ∃ U : Subgroup H,
      IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥
  · exact Or.inr (Or.inr (Or.inr (Or.inr hOddCore)))
  have hHyp : HypothesisOne H S0 :=
    hypothesis_one_of_nTwo hN2 hEven hTwoCore S0 hStrong hOddCore
  have hLocal : ∀ U : Subgroup H, IsTwoLocal U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U :=
    two_local_solvable_characteristicTwo_of_nTwo hN2 hOddCore
  by_cases hMax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧
      IsMaximalTwoLocal P1 ∧
      IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧
      (S0 : Subgroup H) ≤ P2
  · exact Or.inl (hMultiple hHyp hLocal hMax)
  have hS0ne : (S0 : Subgroup H) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S0 hEven.two_dvd
  obtain ⟨M, hM⟩ :=
    exists_uniqueMaximalTwoLocalContaining_of_not_two S0 hS0ne (by
      rintro ⟨M1, M2, hne, ⟨hM1, hS1⟩, ⟨hM2, hS2⟩⟩
      exact hMax ⟨M1, M2, hne, hM1, hM2, hS1, hS2⟩)
  rcases hUnique hHyp hLocal M hM with hExceptional | hBC
  · exact Or.inl hExceptional
  · rcases hBC with hB | hC
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr (Or.inl hC))

end SectionEleven

open SectionEleven SectionsFiveToSeven Later SectionNine in
/-- **Stellmacher, Theorem 1.**

Let `S0` be a Sylow 2-subgroup of the finite group `H`, and let `B` be its
Baumann subgroup.  If every 2-local subgroup containing `B` is solvable and
of characteristic 2 type, and at least two distinct maximal 2-local
subgroups contain `S0`, then `H` has one of the eight local types listed in
the source.

Source: `refs/latex/stellmacher-n-group.tex`, lines 108--118. -/
public theorem theorem_one
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H,
      IsTwoLocal U →
      baumannSubgroup S0 ≤ U →
      Group.IsSolvable U ∧ IsCharacteristicTwoType U)
    (hmax : ∃ P1 P2 : Subgroup H,
      P1 ≠ P2 ∧
      IsMaximalTwoLocal P1 ∧
      IsMaximalTwoLocal P2 ∧
      (S0 : Subgroup H) ≤ P1 ∧
      (S0 : Subgroup H) ≤ P2) :
    IsOfMainTheoremType S0 := by
  obtain ⟨P1, P2, ⟨ctx⟩⟩ := theorem_one_terminal_context S0 hlocal hmax
  change IsOfExceptionalType H ∨ IsOfMathieuTwelveType H ∨
    IsOfOmegaSixPlusTwoType H ∨ IsOfOmegaSixMinusThreeType H ∨
    IsOfOmegaEightPlusThreeType H
  by_cases hcomm : ⁅ctx.Γ.z ctx.criticalPath.a, ctx.Γ.z ctx.criticalPath.a'⁆ = ⊥
  · have hbound := lemma_nine_ten_ambient (ctx.toSectionNineContext hcomm)
    obtain ⟨half, hodd⟩ :=
      (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath hcomm).odd_distance
    change ctx.criticalPath.length ≤ 3 at hbound
    change ctx.criticalPath.length = 2 * half + 1 at hodd
    have hlength : ctx.criticalPath.length = 1 ∨ ctx.criticalPath.length = 3 := by omega
    rcases hlength with hone | hthree
    · exact Or.inr (Or.inr (Or.inl (multiple_nine_one_type ctx hcomm hone)))
    · rcases multiple_ten_one_full_terminal ctx hcomm hthree with hMathieu | hTits
      · exact Or.inr (Or.inl hMathieu)
      · exact Or.inl (Or.inr (Or.inr (Or.inr hTits)))
  · by_cases hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
        CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)
    · rcases multiple_eight_six_full_terminal ctx hcomm hcenter with hG2 | hMinus | hPlus
      · exact Or.inl (Or.inr (Or.inr (Or.inl hG2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hMinus)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hPlus)))
    · rcases multiple_eight_two_terminal ctx hcomm hcenter with hL3 | hSp4
      · exact Or.inl (Or.inl hL3)
      · exact Or.inl (Or.inr (Or.inl hSp4))

/-- **Stellmacher, Theorem 2.**

If `H` is an `(N₂)`-group of even order with `O₂(H) = 1`, and `S0` is a
Sylow 2-subgroup of `H`, then one of the following holds: `H` has one of the
four exceptional local types; `S0` is dihedral or semidihedral; `S0` has order
`2⁵` and `H` has a maximal 2-local subgroup isomorphic to `C₂ × S₄`; `H`
has a strongly embedded subgroup; or some 2-local subgroup has nontrivial
`2'`-core.

The explicit `O₂(H) = 1` hypothesis is the exact input used by Section 11.
It is not displayed in the printed statement, and the paper's opening
definition of `(N₂)` records only 2-local solvability; nevertheless Section 11
asserts Hypothesis 1, whose second clause is `O₂(H)=1`, without deriving it.
Thus the explicit hypothesis records the source gap and excludes the formal
counterexample `C₂ × C₂ × C₂` to the unstrengthened statement.

Source: `refs/latex/stellmacher-n-group.tex`, lines 121--131; the journal
scan `refs/files/stellmacher-n-group.pdf`, p. 12, resolves the `2'`-core
notation in clause (e). -/
public theorem theorem_two
    {H : Type u} [Group H] [Finite H]
    (hN2 : IsNTwoGroup H) (hEven : Even (Nat.card H))
    (hTwoCore : pCore 2 H = ⊥)
    (S0 : Sylow 2 H) :
    IsOfExceptionalType H ∨
    (IsDihedralGroup S0 ∨ IsSemidihedralGroup S0) ∨
    (Nat.card S0 = 2 ^ 5 ∧
      ∃ U : Subgroup H,
        IsMaximalTwoLocal U ∧
        Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ M : Subgroup H, IsStronglyEmbedded M) ∨
    (∃ U : Subgroup H,
      IsTwoLocal U ∧ pPrimeCore 2 U ≠ ⊥) := by
  exact SectionEleven.theorem_two_logical_reduction hN2 hEven hTwoCore S0
    (fun hHyp hLocal hMax => SectionEleven.multiple_maximal_branch S0 hHyp hLocal hMax)
    (fun hHyp hLocal M hM => Or.inr (SectionEleven.unique_maximal_branch S0 hHyp hLocal M hM))

end Stellmacher
