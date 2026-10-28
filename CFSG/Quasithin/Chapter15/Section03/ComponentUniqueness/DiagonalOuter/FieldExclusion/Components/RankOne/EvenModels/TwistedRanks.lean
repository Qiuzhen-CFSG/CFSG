module

public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.SpecificGroups.Tits.ThreeRankLowerBound
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.SpecificGroups.ReeF4.SubfieldTitsEmbedding
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.Triality.ElementaryNine

/-!
# Three-rank obstructions in the twisted characteristic-two models

The certified nonabelian subgroup of order 27 in the Atlas permutation image
has three-rank at least two. The actual Parrott--Atlas equivalence transports
this bound to the Tits group. Its checked embedding into the binary Ree fixed
matrices, followed by coefficient extension, gives the same bound in every
concrete Ree F₄ model. Neither argument needs simplicity of the ambient group.

For triality, two certified commuting cubic root words give an elementary
subgroup of order nine in the genuine graph-field carrier. This subgroup
excludes three-rank one at every binary field order, including q = 2.
All three exclusions require only finiteness, not simplicity.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.2.3--4,
printed p.33, and the proof of 15.3.38, printed p.1137 (`refs/quasithin.pdf`).
GLS3 §§2.2 and 2.6 give the twisted and subfield conventions; Theorem 2.5.15
retains Tits as the separate small derived endpoint. The actual permutation
and fixed-matrix witnesses are supplied by the imported constructions.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne

variable {S : Type*} [Group S] [Finite S]

/-- The faithful Parrott--Atlas comparison transports the nonabelian
three-subgroup obstruction to the exact Tits carrier in Theorem C. -/
theorem two_le_threeRank_of_tits
    (hmodel : Nonempty (S ≃* Tits.ParrottGroup)) : 2 ≤ primeRank 3 S := by
  obtain ⟨e⟩ := hmodel
  rw [primeRank_equiv 3 (e.trans Tits.parrottFiniteImageEquiv)]
  exact Tits.ThreeRank.rank_two_le

/-- The small derived Tits endpoint cannot have three-rank one. -/
theorem rank_ne_one_of_tits
    (hmodel : Nonempty (S ≃* Tits.ParrottGroup)) : primeRank 3 S ≠ 1 := by
  have h := two_le_threeRank_of_tits hmodel
  omega

/-- A genuine Tits subfield embedding gives the lower rank bound for every
Ree parameter, even before excluding the small full fixed group. -/
theorem two_le_threeRank_of_ree_f4 {m : ℕ}
    (hmodel : Nonempty (S ≃* ReeF4.Model m)) : 2 ≤ primeRank 3 S := by
  obtain ⟨e⟩ := hmodel
  obtain ⟨j, hj⟩ := ReeF4.Subfield.exists_tits_embedding m
  have h := (two_le_threeRank_of_tits ⟨MulEquiv.refl Tits.ParrottGroup⟩).trans
    (primeRank_le_of_injective 3 j hj)
  rwa [← primeRank_equiv 3 e] at h

/-- The Ree F₄ constructor, whose field order is `2 ^ (2 * m + 1)`,
cannot have three-rank one. -/
theorem rank_ne_one_of_ree_f4 {m : ℕ} (_hm : 1 ≤ m)
    (hmodel : Nonempty (S ≃* ReeF4.Model m)) : primeRank 3 S ≠ 1 := by
  have h := two_le_threeRank_of_ree_f4 hmodel
  omega

/-- An actual elementary subgroup of order nine suffices for the triality
constructor. The final exclusion below supplies this witness at every field
parameter, including `f = 1`. -/
theorem rank_ne_one_of_triality_of_elementary_nine {f : ℕ} (hf : 1 ≤ f)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ f) S)
    (hE : ∃ E : Subgroup (Triality.Standard.BinaryCarrier f (by omega)),
      IsElementaryAbelian 3 E ∧ Nat.card E = 9) : primeRank 3 S ≠ 1 := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff S f (by omega)).mp hmodel
  obtain ⟨E, hE, hcard⟩ := hE
  let := hE
  intro hr
  have hbound : primeRank 3 (Triality.Standard.BinaryCarrier f (by omega)) ≤ 1 := by
    rw [← primeRank_equiv 3 e, hr]
  have h := IsElementaryAbelian.card_le_prime_of_primeRank_le_one hbound E
  omega

/-- The genuine triality constructor cannot have three-rank one, including
the smallest field order `2`. The elementary subgroup witness is discharged
by the two independent cubic root words in the actual central quotient. -/
theorem rank_ne_one_of_triality {f : ℕ} (hf : 1 ≤ f)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ f) S) : primeRank 3 S ≠ 1 :=
  rank_ne_one_of_triality_of_elementary_nine hf hmodel
    (Triality.Standard.exists_elementaryAbelian_three_card_nine f (by omega))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
