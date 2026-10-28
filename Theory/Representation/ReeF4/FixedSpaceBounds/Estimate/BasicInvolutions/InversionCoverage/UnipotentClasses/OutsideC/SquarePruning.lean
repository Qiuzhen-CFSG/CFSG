module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.ReductionContracts
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.SquarePruning.Collection

/-!
# Square-one pruning in the nonzero eighth-coordinate branch

For a positive Ree word with nonzero X₈ parameter, the split square coordinates
18 and 6 force its X₁ main and central parameters to vanish. After the X₇ and
X₃ main parameters have been removed, coordinates 21 and 16 force X₅ and X₂
to vanish; coordinate 15 then removes Y₃. These are consequences of the literal
split F₄ root exchanges and uniqueness of positive coordinates, uniformly for
all coefficient fields (including m = 0). No involution classification or
conjugacy normalization is assumed.

This supplies `SquarePruning` to the separate outside-C conjugacy assembly.
Source: GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex;
the involution-class input to Guralnick--Malle Lemma 8.8, internal p.57.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
open Parabolics.RadicalCoordinates.FixedCoordinates
open ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open NormalizedRootCentralizers.CenterExponent.OuterElimination

private theorem split_square (m : ℕ) (p : PositiveParameters m)
    (hsq : wordElement m p ^ 2 = 1) : splitWord m (parameters m p) ^ 2 = 1 := by
  simpa only [map_pow, map_one, wordElement_coe, positiveWord_split] using
    congrArg (toSplitGroup m) hsq

/-- Both stages of square pruning, without an involution-class premise. -/
theorem squarePruning (m : ℕ) : SquarePruning m where
  initial p ha hsq := by
    obtain ⟨h₀, hc⟩ := SquareCollection.initial_equations m (parameters m p)
      (split_square m p hsq)
    change p.main 0 * p.pair 0 = 0 at h₀
    have hm : p.main 0 = 0 := (mul_eq_zero.mp h₀).resolve_right ha
    change halfFrobenius m (p.main 0) ^ 2 * p.main 2 +
      p.pair 0 * p.central 0 = 0 at hc
    simp only [hm, map_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hc
    exact ⟨hm, (mul_eq_zero.mp hc).resolve_left ha⟩
  normalized p ha hsq hm0 hc0 hm2 hm3 := by
    obtain ⟨hm, hp, hc⟩ := SquareCollection.normalized_equations m (parameters m p)
      (by simp [parameters, hm0]) (by simp [parameters, hm0])
      (by simp [parameters, hm0, hc0]) (by simp [parameters, hc0])
      (by simp [parameters, hm2]) (by simp [parameters, hm2])
      (by simp [parameters, hm3]) (by simp [parameters, hm3])
      (split_square m p hsq)
    change p.main 1 * p.pair 0 = 0 at hm
    change halfFrobenius m (p.pair 0) ^ 2 * p.pair 1 = 0 at hp
    have hm1 : p.main 1 = 0 := (mul_eq_zero.mp hm).resolve_right ha
    have hh : halfFrobenius m (p.pair 0) ≠ 0 := by
      intro h
      exact ha ((halfFrobenius m).injective (by simpa only [map_zero] using h))
    have hp1 : p.pair 1 = 0 := (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hh)
    change p.main 1 * halfFrobenius m (p.main 1) ^ 2 +
      p.main 1 * p.pair 0 * p.pair 1 + p.central 2 * p.pair 1 +
      p.pair 0 * p.central 3 = 0 at hc
    simp only [hm1, hp1, zero_mul, mul_zero, zero_add] at hc
    exact ⟨hm1, hp1, (mul_eq_zero.mp hc).resolve_left ha⟩

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC
