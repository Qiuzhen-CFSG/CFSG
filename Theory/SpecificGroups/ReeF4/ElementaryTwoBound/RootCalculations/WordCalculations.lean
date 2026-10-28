module
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Endpoints
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.CrossCollection
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.CentralizerCollection
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.LeftSquareCollection
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.RightSquareCollection

/-!
# Square and commutator detection in the Ree counting sections

The checked split collections force the two middle main parameters of a
square-one section word to vanish. Two cross-commutator coordinates force
commuting nonidentity endpoint elements into X₂ on the left. The X₂ test
forces the central seventh parameter of a D-supported word to vanish.
All equations are for the literal matrix curves, uniformly in the field.

Source: GLS3 2.4.5(d), 2.4.6 and Lemma 3.3.9,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/
public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.RootCalculations
open Subgroup Parabolics
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open NormalizedRootCentralizers.CenterExponent
open Parabolics.RadicalCoordinates.FixedCoordinates
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent.OuterElimination

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong i), halfFrobenius]

private theorem central_first (m : ℕ) (a : CoefficientField m) :
    centralWord m 0 a = MatrixRelations.LongCommutators.X m 3 a *
      MatrixRelations.LongCommutators.X m 2 (halfFrobenius m a) := by
  simp only [centralWord, fieldEnd_half]; rfl

private theorem central_seventh (m : ℕ) (a : CoefficientField m) :
    centralWord m 6 a = MatrixRelations.LongCommutators.X m 21 a *
      MatrixRelations.LongCommutators.X m 20 (halfFrobenius m a) := by
  simp only [centralWord, fieldEnd_half]; rfl

private theorem main_sixth (m : ℕ) (a : CoefficientField m) :
    rootWord m 5 a = MatrixRelations.LongCommutators.X m 16 a *
      MatrixRelations.LongCommutators.X m 17 (halfFrobenius m a) := by
  simp only [rootWord, fieldEnd_half]
  exact mul_one _

attribute [local irreducible] MatrixRelations.LongCommutators.X

/-- The literal cross-commutator conclusion used in the counting proof. -/
theorem cross_commute (m : ℕ) (e : Model m) (he : e ∈ left m) (_he1 : e ≠ 1)
    (f : Model m) (hf : f ∈ right m) (hf1 : f ≠ 1) (hc : Commute e f) :
    e ∈ ElementaryTwoBound.X m 1 := by
  obtain ⟨a,b,rfl⟩ := (mem_left_iff m e).mp he
  obtain ⟨c,d,rfl⟩ := (mem_right_iff m f).mp hf
  have hc' := congrArg (toSplitGroup m) hc.eq
  simp only [map_mul, mainElement_coe, centralElement_coe] at hc'
  have heq := CrossCollection.equations m
    ![a, halfFrobenius m a, b, halfFrobenius m b, c, halfFrobenius m c,
      d, halfFrobenius m d] (by
        simpa only [commute_iff_eq, word_1, central_first, main_sixth, central_seventh,
          Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk, mul_assoc, mul_one]
          using hc')
  change b * d = 0 ∧ b * c + d * halfFrobenius m b ^ 2 = 0 at heq
  have hb : b = 0 := by
    by_contra hb
    have hd : d = 0 := (mul_eq_zero.mp heq.1).resolve_left hb
    have hc0 : c = 0 := (mul_eq_zero.mp (by simpa only [hd, zero_mul, add_zero]
      using heq.2)).resolve_left hb
    exact hf1 (by simp only [hd, hc0, mainElement_zero, centralElement_zero, mul_one])
  simpa only [hb, centralElement_zero, mul_one] using mainElement_mem_X m 1 a

private theorem eq_zero_of_mul_half (m : ℕ) (a : CoefficientField m)
    (h : a * halfFrobenius m a = 0) : a = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact (halfFrobenius m).injective (by simpa only [map_zero] using h)

/-- The two noncentral B₂ parameters vanish on square-one D₁-supported words. -/
theorem square_left_support (m : ℕ) (p : PositiveParameters m) (hp : D₁Support p)
    (hsq : wordElement m p ^ 2 = 1) : T₁Support p := by
  obtain ⟨⟨hp0, hm0, hm2⟩, hp2, hc2⟩ := hp
  have hs : splitWord m (parameters m p) ^ 2 = 1 := by
    simpa only [map_pow, map_one, wordElement_coe, positiveWord_split] using
      congrArg (toSplitGroup m) hsq
  have he := LeftSquareCollection.equations m (parameters m p)
    (by simp [parameters, hm0]) (by simp [parameters, hm0])
    (by simp [parameters, hp2]) (by simp [parameters, hp2])
    (by simp [parameters, hm2]) (by simp [parameters, hm2])
    (by simp [parameters, hm2, hc2]) (by simp [parameters, hc2])
    (by simp [parameters, hp0]) (by simp [parameters, hp0]) hs
  change p.main 1 * halfFrobenius m (p.main 1) = 0 ∧
    halfFrobenius m (p.main 1) * halfFrobenius m (p.pair 1) +
      p.main 3 * halfFrobenius m (p.main 3) = 0 at he
  have h1 := eq_zero_of_mul_half m _ he.1
  have h3 := eq_zero_of_mul_half m (p.main 3)
    (by simpa only [h1, map_zero, zero_mul, zero_add] using he.2)
  exact ⟨⟨⟨hp0, hm0, hm2⟩, hp2, hc2⟩, h1, h3⟩

/-- The symmetric square calculation for D₂, without an implicit symmetry premise. -/
theorem square_right_support (m : ℕ) (p : PositiveParameters m) (hp : D₂Support p)
    (hsq : wordElement m p ^ 2 = 1) : T₂Support p := by
  obtain ⟨⟨hp0, hm0, hm2⟩, hp1, hc0⟩ := hp
  have hs : splitWord m (parameters m p) ^ 2 = 1 := by
    simpa only [map_pow, map_one, wordElement_coe, positiveWord_split] using
      congrArg (toSplitGroup m) hsq
  have he := RightSquareCollection.equations m (parameters m p)
    (by simp [parameters, hm0]) (by simp [parameters, hm0])
    (by simp [parameters, hm0, hc0]) (by simp [parameters, hc0])
    (by simp [parameters, hp1]) (by simp [parameters, hp1])
    (by simp [parameters, hm2]) (by simp [parameters, hm2])
    (by simp [parameters, hp0]) (by simp [parameters, hp0]) hs
  change p.main 3 * halfFrobenius m (p.main 3) = 0 ∧
    p.main 1 * halfFrobenius m (p.main 1) +
      halfFrobenius m (p.pair 2) * halfFrobenius m (p.main 3) = 0 at he
  have h3 := eq_zero_of_mul_half m _ he.1
  have h1 := eq_zero_of_mul_half m (p.main 1)
    (by simpa only [h3, map_zero, mul_zero, add_zero] using he.2)
  exact ⟨⟨⟨hp0, hm0, hm2⟩, hp1, hc0⟩, h1, h3⟩

private def extendedParameters (m : ℕ) (p : PositiveParameters m)
    (a : CoefficientField m) : Fin 26 → CoefficientField m :=
  ![parameters m p 0, parameters m p 1, parameters m p 2, parameters m p 3,
    parameters m p 4, parameters m p 5, parameters m p 6, parameters m p 7,
    parameters m p 8, parameters m p 9, parameters m p 10, parameters m p 11,
    parameters m p 12, parameters m p 13, parameters m p 14, parameters m p 15,
    parameters m p 16, parameters m p 17, parameters m p 18, parameters m p 19,
    parameters m p 20, parameters m p 21, parameters m p 22, parameters m p 23,
    a, halfFrobenius m a]

/-- A D-supported word commuting with a nonidentity X₂ element has zero Y₇ parameter. -/
theorem centralizer_support (m : ℕ) (p : PositiveParameters m) (hp : DSupport p)
    (a : CoefficientField m) (ha : a ≠ 0)
    (hc : Commute (wordElement m p) (mainElement m 1 a)) : KSupport p := by
  obtain ⟨hp0,hm0,hm2⟩ := hp
  have hc' := congrArg (toSplitGroup m) hc.eq
  simp only [map_mul, wordElement_coe, mainElement_coe, positiveWord_split] at hc'
  have he := CentralizerCollection.equations m (extendedParameters m p a) (by
    simpa only [commute_iff_eq, extendedParameters, parameters, splitWord, word_1,
      Matrix.cons_val_zero, Matrix.cons_val, Fin.reduceFinMk,
      hp0, hm0, hm2, map_zero, zero_mul, zero_add, xz, one_mul, mul_one, mul_assoc]
      using hc')
  change p.central 2 * a = 0 at he
  exact ⟨⟨hp0, hm0, hm2⟩, (mul_eq_zero.mp he).resolve_right ha⟩

end ReeF4.ElementaryTwoBound.RootCalculations
