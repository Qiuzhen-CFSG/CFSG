module
public import CFSG.Quasithin.ChapterA.Section02.FiniteModelRankExclusions
public import Theory.SpecificGroups.FiniteModelFiveRank

/-!
# The remaining finite Theorem B exceptions and five-rank

The placed A₅ pair supplies five-rank at least two. The intrinsic order
bounds exclude the last sporadic row J₄ and the binary symplectic six-space.
Combined with the two-rank-eight exclusions, the complete Theorem B list
therefore leaves only its three families with field parameters.

Source: Aschbacher--Smith A.2.2 and 4.4.12, printed pp.33 and622.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02
open ClassificationModels Theory.GroupTheory Theory.SpecificGroups.FiniteModelFiveRank
variable {G : Type*} [Group G] [Finite G]

/-- Five-rank two excludes the literal J₄ model. -/
theorem no_j4_of_fiveRank_ge_two (hr : 2 ≤ primeRank 5 G) :
    ¬ Nonempty (G ≃* Janko4.Model) := by
  rintro ⟨e⟩
  rw [primeRank_equiv 5 e] at hr
  have hh := j4_le_one
  omega

/-- Five-rank two excludes the binary projective symplectic six-space. -/
theorem no_binary_symplectic_six_of_fiveRank_ge_two (hr : 2 ≤ primeRank 5 G) :
    ¬ ClassicalGroup.IsPSp G 3 2 := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  rw [primeRank_equiv 5 e] at hr
  have hh : primeRank 5 (ClassicalGroup.PSp 3 F) ≤ 1 :=
    binary_symplectic_six_le_one hcard
  omega

/-- Two-rank eight and five-rank two remove all finite exceptional B rows. -/
theorem IsTheoremBModel.infinite_families_of_twoRank_ge_eight_fiveRank_ge_two
    (h : IsTheoremBModel G) (h2 : 8 ≤ primeRank 2 G) (h5 : 2 ≤ primeRank 5 G) :
    IsTheoremBOddModel G ∨ IsBenderModel G ∨ (∃ f, IsRankTwoModel G f) := by
  rcases h.remaining_of_twoRank_ge_eight h2 with ho | hb | hr | hs | hj
  · exact Or.inl ho
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hr)
  · exact False.elim (no_binary_symplectic_six_of_fiveRank_ge_two h5 hs)
  · exact False.elim (no_j4_of_fiveRank_ge_two h5 hj)

end CFSG.Quasithin.ChapterA.Section02
