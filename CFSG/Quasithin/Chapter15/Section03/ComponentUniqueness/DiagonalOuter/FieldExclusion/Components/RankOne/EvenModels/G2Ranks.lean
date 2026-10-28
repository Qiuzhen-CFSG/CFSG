module

public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Excluding three-rank one in the even G₂ cases

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.2.3–4,
printed p.33, and the proof of 15.3.38, printed p.1137.

The actual split-octonion model over every characteristic-two field contains
an elementary nine, as does the actual commutator subgroup of G₂(2).
Transporting these witnesses through the model isomorphisms excludes the
`g2` and `g2_derived` constructors from the rank-one component inspection.
The proof does not need simplicity or nonabelianness of the supplied group.
-/

public section

open Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne

variable {S : Type*} [Group S] [Finite S]

/-- An actual G₂ model over an even field has three-rank at least two. -/
theorem two_le_primeRank_of_g2_even {f : ℕ}
    (hmodel : ClassificationModels.IsG2At S (2 ^ f)) : 2 ≤ primeRank 3 S := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  rw [primeRank_equiv 3 e]
  exact Atlas.G2.EvenThreeRank.two_le_primeRank

/-- The G₂ constructor in the Theorem C rank-two list cannot have three-rank one. -/
theorem rank_ne_one_of_g2_even {f : ℕ} (_hf : 2 ≤ f)
    (hmodel : ClassificationModels.IsG2At S (2 ^ f)) : primeRank 3 S ≠ 1 := by
  have := two_le_primeRank_of_g2_even hmodel
  omega

/-- The actual binary derived group, transported by a multiplicative equivalence,
has three-rank at least two. -/
theorem two_le_primeRank_of_g2_derived
    (hmodel : Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    2 ≤ primeRank 3 S := by
  obtain ⟨e⟩ := hmodel
  rw [primeRank_equiv 3 e]
  exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived

/-- The binary derived constructor cannot have three-rank one. -/
theorem rank_ne_one_of_g2_derived
    (hmodel : Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    primeRank 3 S ≠ 1 := by
  have := two_le_primeRank_of_g2_derived hmodel
  omega

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
