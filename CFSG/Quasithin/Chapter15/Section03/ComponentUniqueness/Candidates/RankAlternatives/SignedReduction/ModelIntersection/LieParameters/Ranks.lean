module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.SpecificGroups.Triality.StandardTwoRank
public import Theory.SpecificGroups.PSL5Two.TwoRank
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates
/-!
# Two-rank obstructions for the large Lie carriers

Odd signed degree-three parameters have two-rank at most two. The checked
root and Sylow calculations for PSL₂, PSL₃, PSU₃, Sp₄, G₂, and PSL₅(2)
therefore force evenness outside their small endpoints. Triality uses its
actual cubic short-root subgroup inside the derived carrier. The Ree case
uses the additive coefficient group in the genuine fixed positive linear
block; its dimension is 2m+1, at least three in the simple range.

All ranks transport along the model's supplied multiplicative equivalence.
No exceptional family is replaced by a different carrier without a comparison.
Source: Aschbacher--Smith, 1.1.5(3), printed pp.501--503, intersected with
A.3.18(2), pp.51--52, in 15.3.37 and 15.3.43, pp.1135 and 1139.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
open Chapter1.Section02.LocalModels ClassificationModels
variable {S : Type*} [Group S] [Finite S] {unitary : Bool} {q : ℕ}

/-- The PSL₂ root group suffices at binary degree at least three. -/
theorem signed_even_of_linear_two {n : ℕ} (hn : 3 ≤ n)
    (hm : ClassicalGroup.IsPSL S 2 (2 ^ n)) (h : IsPSLSign S unitary 3 q) : Even q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  apply signed_even_of_twoRank h
  rw [primeRank_equiv 2 e]
  exact hn.trans (Theory.PSL2.root_two_rank_ge F hc)

/-- The two-dimensional PSL₃ root group suffices above the binary endpoint. -/
theorem signed_even_of_linear_three {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL S 3 (2 ^ n)) (h : IsPSLSign S unitary 3 q) : Even q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  apply signed_even_of_twoRank h
  rw [primeRank_equiv 2 e, Matrix.PSL3Even.two_rank F (by omega) hc]
  omega

/-- The center of the unitary root group suffices at binary degree at least three. -/
theorem signed_even_of_unitary_three {n : ℕ} (hn : 3 ≤ n)
    (hm : ClassicalGroup.IsPSU S 3 (2 ^ n)) (h : IsPSLSign S unitary 3 q) : Even q := by
  obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := hm
  apply signed_even_of_twoRank h
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective e.symm e.symm.injective
  rw [primeRank_equiv 2 e,
    BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.two_rank J (by omega) hc hconj]
  exact hn

/-- The symplectic elementary radical gives the required rank obstruction. -/
theorem signed_even_of_symplectic {n : ℕ} (hn : 1 ≤ n)
    (hm : ClassicalGroup.IsPSp S 2 (2 ^ n)) (h : IsPSLSign S unitary 3 q) : Even q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  apply signed_even_of_twoRank h
  rw [primeRank_equiv 2 e]
  have hr := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.projective_rank hc (by omega)
  change primeRank 2 (ClassicalGroup.PSp 2 F) = 3 * n at hr
  rw [hr]
  omega

/-- The three commuting G₂ root groups give the required rank obstruction. -/
theorem signed_even_of_g2 {n : ℕ} (hn : 1 ≤ n)
    (hm : IsG2At S (2 ^ n)) (h : IsPSLSign S unitary 3 q) : Even q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  apply signed_even_of_twoRank h
  rw [primeRank_equiv 2 e, Atlas.G2.EvenTwoRank.two_rank F hc]
  omega

/-- The cubic triality root group remains in the actual derived carrier. -/
theorem signed_even_of_triality {n : ℕ} (hn : 1 ≤ n)
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) S)
    (h : IsPSLSign S unitary 3 q) : Even q := by
  apply signed_even_of_twoRank h
  have hr := Triality.Standard.TwoRank.derived_twoRank_ge_three_mul_of_model n (by omega) hm
  have hi := Theory.GroupTheory.primeRank_le_of_injective 2 (commutator S).subtype Subtype.val_injective
  omega

/-- The six-dimensional elementary subgroup of PSL₅(2) gives the obstruction. -/
theorem signed_even_of_linear_five (hm : ClassicalGroup.IsPSL S 5 2)
    (h : IsPSLSign S unitary 3 q) : Even q := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hm
  apply signed_even_of_twoRank h
  rw [primeRank_equiv 2 e]
  exact (by decide : 3 ≤ 6).trans (Theory.SpecificGroups.PSL5Two.six_le_primeRank_of_card_two hc)

/-- The fixed linear root block of the genuine Ree carrier has rank 2m+1. -/
theorem signed_even_of_ree {m : ℕ} (hm : 1 ≤ m) (hmodel : IsReeF4At S m)
    (h : IsPSLSign S unitary 3 q) : Even q := by
  obtain ⟨d, ⟨e⟩⟩ := hmodel
  apply signed_even_of_twoRank h
  rw [primeRank_equiv 2 e]
  let a := ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.positiveLinearEquiv d
  let f : Multiplicative (ReeF4.CoefficientField m) →* d.fixedGroup :=
    (ReeF4.LocalBlockInput.PairRigidity.simpleBlock d .linear true).subtype.comp a.toMonoidHom
  have hr : 2 * m + 1 ≤ primeRank 2 d.fixedGroup := by
    apply primeRank_ge_of_elementary_embedding (f := f)
    · intro x
      change 2 • x.toAdd = 0
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero _
    · exact ReeF4.field_card m
    · exact Subtype.val_injective.comp a.injective
  omega
end CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
