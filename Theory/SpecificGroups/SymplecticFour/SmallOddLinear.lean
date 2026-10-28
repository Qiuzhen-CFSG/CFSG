module

public import Theory.SpecificGroups.SymplecticFour.OddPrimeLinearExclusion
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# The odd-field rank-one groups in symplectic four-space

The projective Borel degree bound forces an odd field to have order at most
ten. Nonsolvability excludes order three, and the actual seven-element
comparison is incompatible with the symplectic spectrum. Thus only the
literal A5 and A6 models remain, including for nonprime field parameters.

This is the odd rank-one row of Aschbacher--Smith E.2.7, printed p.220.
The statement concerns the given faithful symplectic representation and does
not presume a classification of symplectic subgroups.
-/

public section
open scoped MatrixGroups
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]

/-- All nonsolvable odd-field PSL2 subgroups of symplectic four-space are
the actual A5 or A6 models. -/
theorem odd_psl2_equiv_alternating_five_or_six
    {K : Type*} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (hns : ¬ Group.IsSolvable PSL(2,K))
    (j : PSL(2,K) →* Sp F) (hj : Function.Injective j) :
    Nonempty (PSL(2,K) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (PSL(2,K) ≃* alternatingGroup (Fin 6)) := by
  have hlo := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
    hodd hns
  have hhi := odd_psl2_borel_bound hodd j hj
  have hseven : Nat.card K ≠ 7 := by
    intro he
    exact odd_prime_psl2_not_injective (by decide : Nat.Prime 7) (by decide) he j hj
  have hc : Nat.card K = 5 ∨ Nat.card K = 9 := by
    obtain ⟨k,hk⟩ := hodd
    omega
  rcases hc with hfive | hnine
  · exact Or.inl ⟨(Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hfive).trans
      Atlas.Comparisons.Exceptional.psl2FourEquivAlt5⟩
  · exact Or.inr ⟨Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hnine⟩

end Theory.SpecificGroups.SymplecticFour
