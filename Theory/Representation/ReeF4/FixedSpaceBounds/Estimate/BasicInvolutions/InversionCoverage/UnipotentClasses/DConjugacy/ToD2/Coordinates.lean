module
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Reduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.SquareCollection
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2.EighthCollection

/-!
# Square equations and eighth-root transport on the Ree D section

The square equations and selected coordinates of conjugation by x₈ are
consequences of checked split-root collection and positive coordinate
uniqueness. The conjugating element belongs to the actual fixed Ree model.
These formulas supply the scalar elimination used by `ToD2`.
Source: GLS3 Table 2.4, 2.4.5(d), and Lemma 3.3.9.
-/
@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2
open Parabolics ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open OuterElimination MatrixRelations.LongCommutators

/-- The three square equations used to eliminate the two endpoint pairs. -/
theorem square_equations (m : ℕ) (p : PositiveParameters m) (hp : DSupport p)
    (hsq : wordElement m p ^ 2 = 1) :
    p.main 1 * p.main 3 + p.central 2 * p.central 0 = 0 ∧
    p.main 1 * halfFrobenius m (p.main 1) +
      halfFrobenius m (p.pair 2) * halfFrobenius m (p.main 3) +
      halfFrobenius m (p.central 0) * p.central 2 +
      halfFrobenius m (p.central 2) * halfFrobenius m (p.pair 1) = 0 ∧
    halfFrobenius m (p.main 1) * halfFrobenius m (p.pair 1) +
      halfFrobenius m (p.pair 2) * halfFrobenius m (p.central 0) +
      halfFrobenius m (p.central 2) * p.central 0 +
      p.main 3 * halfFrobenius m (p.main 3) = 0 := by
  rcases hp with ⟨hp0, hm0, hm2⟩
  have hs : splitWord m (parameters m p) ^ 2 = 1 := by
    simpa only [map_pow, map_one, wordElement_coe, positiveWord_split] using
      congrArg (toSplitGroup m) hsq
  have he := SquareCollection.equations m (parameters m p)
    (by simp [parameters, hm0]) (by simp [parameters, hm0])
    (by simp [parameters, hm2]) (by simp [parameters, hm2])
    (by simp [parameters, hp0]) (by simp [parameters, hp0]) hs
  have hc0 : parameters m p 2 = halfFrobenius m (p.central 0) := by
    change p.main 0 * halfFrobenius m (p.main 0) + halfFrobenius m (p.central 0) = _
    rw [hm0, zero_mul, zero_add]
  have hc2 : parameters m p 20 = halfFrobenius m (p.central 2) := by
    change p.main 2 * halfFrobenius m (p.main 2) + halfFrobenius m (p.central 2) = _
    rw [hm2, zero_mul, zero_add]
  rw [hc0, hc2] at he
  exact he

private def eighthParameters (m : ℕ) (p : PositiveParameters m)
    (t : CoefficientField m) : Fin 26 → CoefficientField m :=
  ![parameters m p 0, parameters m p 1, parameters m p 2, parameters m p 3,
    parameters m p 4, parameters m p 5, parameters m p 6, parameters m p 7,
    parameters m p 8, parameters m p 9, parameters m p 10, parameters m p 11,
    parameters m p 12, parameters m p 13, parameters m p 14, parameters m p 15,
    parameters m p 16, parameters m p 17, parameters m p 18, parameters m p 19,
    parameters m p 20, parameters m p 21, parameters m p 22, parameters m p 23,
    t, halfFrobenius m t]

private theorem word_eighth (m : ℕ) (t : CoefficientField m) :
    rootWord m 7 t = X m 22 t * X m 23 (halfFrobenius m t) := by
  simp only [rootWord, rootFieldEnd,
    if_pos (MatrixRelations.longRoot_isLong 7), halfFrobenius]
  exact mul_one _

/-- Eighth-root conjugation preserves D and has the displayed literal
coordinate action. Coordinates not needed by the elimination are unrestricted. -/
theorem eighth_transport (m : ℕ) (p : PositiveParameters m) (hp : DSupport p)
    (t : CoefficientField m) :
    ∃ q : PositiveParameters m, DSupport q ∧
      mainElement m 7 t * wordElement m p * (mainElement m 7 t)⁻¹ = wordElement m q ∧
      q.central 0 = p.central 0 ∧
      q.main 3 = p.main 3 + t * p.central 0 ∧
      halfFrobenius m (q.pair 2) = halfFrobenius m (p.pair 2) +
        t * halfFrobenius m (p.pair 1) + halfFrobenius m t * p.main 3 +
        t * halfFrobenius m t * p.central 0 ∧
      q.central 2 = p.central 2 + p.main 1 * t +
        p.main 3 * halfFrobenius m t ^ 2 + t * p.central 0 * halfFrobenius m t ^ 2 := by
  have hx := mainElement_mem_unipotent m 7 t
  have hpU := ElementaryTwoBound.D_le_unipotent m (wordElement_mem_D m p hp)
  obtain ⟨q, hq⟩ := exists_positiveWord m
    (mainElement m 7 t * wordElement m p * (mainElement m 7 t)⁻¹)
    ((unipotent m).mul_mem ((unipotent m).mul_mem hx hpU) ((unipotent m).inv_mem hx))
  have hinv : (mainElement m 7 t)⁻¹ = mainElement m 7 t := by
    apply inv_eq_of_mul_eq_one_left
    rw [← mainElement_add m 7 (by decide), CharTwo.add_self_eq_zero, mainElement_zero]
  have hconj : mainElement m 7 t * wordElement m p * (mainElement m 7 t)⁻¹ =
      wordElement m q := by
    apply toSplitGroup_injective m
    simpa only [wordElement_coe] using hq
  rcases hp with ⟨hp0, hm0, hm2⟩
  have h := congrArg (toSplitGroup m) hconj
  rw [hinv] at h
  simp only [map_mul, mainElement_coe, wordElement_coe, positiveWord_split] at h
  have he := EighthCollection.coordinates m (eighthParameters m p t) (parameters m q) (by
    simpa only [eighthParameters, parameters, splitWord, word_eighth,
      Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
      hp0, hm0, hm2, map_zero, zero_mul, zero_add, xz, one_mul, mul_one, mul_assoc]
      using h)
  change q.main 0 = 0 ∧ q.main 2 = 0 ∧ q.pair 0 = 0 ∧
    q.central 0 = p.central 0 ∧ q.main 3 = p.main 3 + t * p.central 0 ∧
    halfFrobenius m (q.pair 2) = _ ∧ q.central 2 = _ at he
  exact ⟨q, ⟨he.2.2.1, he.1, he.2.1⟩, hconj, he.2.2.2⟩

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.ToD2
