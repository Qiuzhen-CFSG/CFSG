module
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.FiniteModelTwoRank
public import Theory.Mathieu.SmallModuleRanks.M24
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TwoRankCoarse
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRank
public import Theory.SpecificGroups.Held.TwoRank.Intrinsic
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# Rank-eight exclusions in the complete Theorem B model list

Certified order and intrinsic rank bounds remove the alternating and binary
linear exceptions. In the thirteen-row sporadic list, rank eight leaves only
the literal J₄ carrier. In particular J₃ and McL are checked here rather than
silently replacing the B catalogue by its smaller C counterpart.

Source: Aschbacher--Smith A.2.2 and 4.4.12, printed pp.33 and622.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02
open ClassificationModels Theory.GroupTheory Theory.SpecificGroups.FiniteModelTwoRank
variable {G : Type*} [Group G] [Finite G]

private theorem sporadic_le_seven (name : SporadicName) (hne : name ≠ .j4) :
    primeRank 2 name.Carrier ≤ 7 := by
  cases name with
  | m11 => exact m11_le_seven
  | m12 => exact m12_le_seven
  | m22 => exact m22_le_seven
  | m23 => exact m23_le_seven
  | m24 => exact _root_.Sporadic.Mathieu.m24_twoRank_le_six.trans (by decide)
  | j2 => exact _root_.Sporadic.LeechRelated.J2.primeRank_two_le_seven
  | j3 => exact j3_le_seven
  | j4 => exact False.elim (hne rfl)
  | hs => exact _root_.Sporadic.LeechRelated.HS.twoRank_le_four.trans (by decide)
  | he => exact Held.primeRank_two_le_six.trans (by decide)
  | ru => exact Rudvalis.primeRank_le_six.trans (by decide)

/-- Rank eight excludes every alternating degree allowed in Theorem B. -/
theorem no_small_alternating_of_twoRank_ge_eight (hr : 8 ≤ primeRank 2 G)
    {n : ℕ} (hn : n ≤ 9) : ¬ Nonempty (G ≃* alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  rw [primeRank_equiv 2 e] at hr
  have hh := alternating_le_seven hn
  omega

/-- Rank eight excludes both binary linear exceptions in Theorem B. -/
theorem no_binary_linear_of_twoRank_ge_eight (hr : 8 ≤ primeRank 2 G)
    {n : ℕ} (hn : n = 4 ∨ n = 5) : ¬ ClassicalGroup.IsPSL G n 2 := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  rw [primeRank_equiv 2 e] at hr
  have hh := binary_linear_le_seven hcard hn
  omega

/-- Of the complete thirteen sporadic B rows, rank eight retains only J₄. -/
theorem theoremBSporadic_j4_of_twoRank_ge_eight (hr : 8 ≤ primeRank 2 G)
    (h : IsTheoremBSporadicModel G) : Nonempty (G ≃* Janko4.Model) := by
  rcases h with ⟨name, ⟨e⟩⟩ | h
  · by_cases hj : name = .j4
    · subst name
      exact ⟨e⟩
    · let : Finite name.Carrier := Finite.of_equiv G e.toEquiv
      rw [primeRank_equiv 2 e] at hr
      have hh := sporadic_le_seven name hj
      omega
  · rcases h with hj | hm
    · obtain ⟨e⟩ := hj
      rw [primeRank_equiv 2 e] at hr
      have hh := j1_le_seven
      omega
    · obtain ⟨e⟩ := hm
      rw [primeRank_equiv 2 e] at hr
      have hh := mcl_le_seven
      omega

/-- The complete B list after the finite rank-eight exclusions; binary Sp₆ and J₄ remain explicit. -/
theorem IsTheoremBModel.remaining_of_twoRank_ge_eight
    (h : IsTheoremBModel G) (hr : 8 ≤ primeRank 2 G) :
    IsTheoremBOddModel G ∨ IsBenderModel G ∨ (∃ f, IsRankTwoModel G f) ∨
      ClassicalGroup.IsPSp G 3 2 ∨ Nonempty (G ≃* Janko4.Model) := by
  cases h with
  | alternating n hn iso => exact False.elim (no_small_alternating_of_twoRank_ge_eight hr hn iso)
  | odd h => exact Or.inl h
  | bender h => exact Or.inr (Or.inl h)
  | rank_two f h => exact Or.inr (Or.inr (Or.inl ⟨f,h⟩))
  | linear_binary n hn iso => exact False.elim (no_binary_linear_of_twoRank_ge_eight hr hn iso)
  | symplectic_binary h => exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  | sporadic h => exact Or.inr (Or.inr (Or.inr (Or.inr
      (theoremBSporadic_j4_of_twoRank_ge_eight hr h))))

end CFSG.Quasithin.ChapterA.Section02
