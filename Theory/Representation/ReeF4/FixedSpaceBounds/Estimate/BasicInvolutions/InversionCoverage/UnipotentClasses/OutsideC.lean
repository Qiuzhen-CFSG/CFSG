module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.NormalForm
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.ReductionContracts
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.MainNormalization
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.OutsideC.SquarePruning

/-!
# Outside-C involutions are conjugate to the short-root curve

The five-parameter terminal slice is unconditionally conjugate to the actual
short-root curve. Square pruning and removal of the X₇ and X₃ main parameters
reduce the nonzero X₈ branch to that slice. The checked square and conjugation
calculations discharge both inputs, proving the stronger short-root conclusion
uniformly for all m. Every conjugacy takes place in the actual fixed Ree model.

Source: Guralnick--Malle, Classification of 2F-modules II, Lemma 8.8,
internal p.57; GLS3 Table 2.4 and 2.4.5(d), refs/KGroup/GLS3/chapter2.tex.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
open EvenInvolutionGeometry ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent OutsideC

/-- The two coordinate calculations imply the stronger short-root conclusion. -/
theorem isShortRootInvolution_of_outside_coordinate_calculations (m : ℕ)
    (hsquare : SquarePruning m) (hnormal : MainNormalization m)
    (p : PositiveParameters m) (hp : p.pair 0 ≠ 0) (hsq : wordElement m p ^ 2 = 1) :
    IsShortRootInvolution (wordElement m p) := by
  obtain ⟨hmain, hcentral⟩ := hsquare.initial p hp hsq
  obtain ⟨q, hconj, heighth, hqmain, hqcentral, hq2, hq3⟩ :=
    hnormal p hp hmain hcentral
  have hq : q.pair 0 ≠ 0 := by simpa only [heighth] using hp
  have hsqq : wordElement m q ^ 2 = 1 := by
    have h := hconj.pow 2
    rw [hsq] at h
    exact isConj_one_right.mp h
  obtain ⟨hqm1, hqp1, hqc3⟩ :=
    hsquare.normalized q hq hsqq hqmain hqcentral hq2 hq3
  have he : q = sliceParameters m (q.pair 0) (q.pair 2) (q.pair 3)
      (q.central 1) (q.central 2) := by
    cases q with
    | mk pair main central =>
      change (⟨pair, main, central⟩ : PositiveParameters m) =
        ⟨![pair 0, 0, pair 2, pair 3], 0, ![0, central 1, central 2, 0]⟩
      congr 1
      · funext j
        fin_cases j
        · rfl
        · exact hqp1
        · rfl
        · rfl
      · funext j
        fin_cases j
        · exact hqmain
        · exact hqm1
        · exact hq2
        · exact hq3
      · funext j
        fin_cases j
        · exact hqcentral
        · rfl
        · rfl
        · exact hqc3
  have hshort := slice_isShortRootInvolution m (q.pair 0) (q.pair 2) (q.pair 3)
    (q.central 1) (q.central 2) hq
  rw [← he] at hshort
  obtain ⟨a, ha, hc⟩ := hshort
  exact ⟨a, ha, hc.trans hconj.symm⟩

/-- The published branch contract, conditional only on the two coordinate calculations. -/
theorem outsideCConjugacy_of_coordinate_calculations (m : ℕ)
    (hsquare : SquarePruning m) (hnormal : MainNormalization m) : OutsideCConjugacy m := by
  intro p hp hsq
  exact Or.inr (isShortRootInvolution_of_outside_coordinate_calculations m
    hsquare hnormal p hp hsq)

/-- A positive square-one word with nonzero X₈ parameter is conjugate to a
nonzero point of the literal short-root curve, for every m. -/
theorem isShortRootInvolution_of_eighth_ne_zero (m : ℕ)
    (p : PositiveParameters m) (hp : p.pair 0 ≠ 0) (hsq : wordElement m p ^ 2 = 1) :
    IsShortRootInvolution (wordElement m p) :=
  isShortRootInvolution_of_outside_coordinate_calculations m
    (squarePruning m) (mainNormalization m) p hp hsq

/-- Unconditional nonzero-X₈ branch of positive involution coverage.
This discharges the outside-C premise of `unipotentRootCoverage_of_coordinate_branches`. -/
theorem outsideCConjugacy (m : ℕ) : OutsideCConjugacy m := by
  intro p hp hsq
  exact Or.inr (isShortRootInvolution_of_eighth_ne_zero m p hp hsq)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses
