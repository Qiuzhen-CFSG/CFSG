module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceCubicAction
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceContracts

/-!
# The corrected source prime-rank sieve in even degree

The only remaining noncubic rank-two models are triality and Ree. A cubic
source torus excludes both by their cubic residual theorems, so every other
source prime has rank one. Thus in even source degree the complete prime-rank
and diagonal-actor conclusion of 4.3.12(2) follows, conditional only on the
whole-radical generation needed to exclude the binary unitary cubic row.

The final application supplies these restrictions together with the literal
local-image geometry for inspection. It does not classify the two-local
normalizers or assert the four rows of 4.3.16. Odd source degrees still require
the noncubic triality/Ree field-actor exclusions.
Source: Aschbacher--Smith A.3.18, pp.51--53; 4.3.12--16, pp.617--618.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

/-- A cubic source torus eliminates the remaining triality and Ree possibilities
at every noncubic prime. This does not require radical generation. -/
theorem SecondarySourceData.noncubic_rank_one_of_three_dvd (s : SecondarySourceData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd3 : 3 ∣ 2^n-1) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hd : p ∣ 2^n-1) (hp3 : p ≠ 3) : primeRank p s.component = 1 := by
  rcases SecondarySourceData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
  · exact hr
  obtain ⟨hz,hm⟩ := SecondarySourceData.noncubic_rank_two_triality_or_ree s D h hp ho hd hp3 hr.ge
  rcases hm with ⟨f,hf,hm⟩ | ⟨m,hm,he⟩
  · exact (SecondarySourceData.not_triality_of_three_dvd s D h hd3 hf hm).elim
  · exact (SecondarySourceData.not_ree_of_three_dvd_of_center_bot s D h hd3 hz hm he).elim

/-- Source 4.3.12(2)'s prime restriction when the torus contains a cubic.
The separately proved whole-radical generation identity remains explicit. -/
theorem SecondarySourceData.prime_rank_or_diagonal_of_three_dvd (s : SecondarySourceData c n)
    (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hd3 : 3 ∣ 2^n-1) {p : ℕ} (hp : p.Prime) (ho : Odd p) (hd : p ∣ 2^n-1) :
    primeRank p s.component = 1 ∨
      (p = 3 ∧ ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
        IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
        ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x = 3 ∧
          IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) unitary q (s.action x) ∧
          s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) := by
  by_cases hp3 : p = 3
  · subst p
    rcases SecondarySourceData.component_primeRank_one_or_two s D h hp ho hd with hr | hr
    · exact Or.inl hr
    · exact Or.inr ⟨rfl,SecondarySourceData.cubic_rank_two_diagonal_actor s hg D h hd hr.ge⟩
  · exact Or.inl (SecondarySourceData.noncubic_rank_one_of_three_dvd s D h hd3 hp ho hd hp3)

/-- On the actual action, even source degree supplies the geometry and prime
restrictions needed by the remaining proper-two-local model inspection. -/
theorem SecondarySourceData.even_degree_inspection_inputs (s : SecondarySourceData c n)
    (hg : SecondarySourceData.ActionGeneration s)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (heven : Even n) :
    SecondarySourceData.LocalImageData s ∧
      ChapterA.Section02.IsTheoremCModel (SecondarySourceData.componentImage s) ∧
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2^n-1 →
        primeRank p s.component = 1 ∨
          (p = 3 ∧ ∃ (unitary : Bool) (q : ℕ), SignedCongruence unitary q ∧
            IsPSLSign (s.component ⧸ pCore 2 s.component) unitary 3 q ∧
            ∃ x : rootNormalizer c, (x : G) ∈ s.torus ∧ orderOf x = 3 ∧
              IsProjectiveDiagonalSign (s.component ⧸ pCore 2 s.component) unitary q (s.action x) ∧
              s.action x ∉ MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component)) := by
  refine ⟨SecondarySourceData.localImageData s D,SecondarySourceData.componentImage_theoremC s D h,?_⟩
  intro p hp ho hd
  exact SecondarySourceData.prime_rank_or_diagonal_of_three_dvd s hg D h
    ((Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mpr heven) hp ho hd

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
