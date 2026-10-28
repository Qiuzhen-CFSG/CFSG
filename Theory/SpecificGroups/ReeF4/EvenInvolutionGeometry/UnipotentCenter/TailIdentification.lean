module
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.CentralSeventhTest
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.PairSixthTest
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.PairFourthTest
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.CentralThirdTest
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.OuterElimination
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.MiddleElimination

/-!
# Identifying the surviving positive Ree coordinate

The existing outer and middle eliminations reduce a central fixed word to the
five curves `x₆ x₄ y₅ y₇ y₃`. The four checked split-word tests respectively
remove `y₇`, `x₆`, `x₄`, and `y₃`. Substitution into the original unique fixed
coordinates leaves exactly `y₅ = centralWord m 4`, without a classification
or Sylow-center assumption.

This is the coordinate input to the actual-model assembly in
`EvenInvolutionGeometry.UnipotentCenter`.
Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith 16.1.6 and 16.5.13, printed pp.1172 and 1201–1202
of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.EvenInvolutionGeometry.UnipotentCenter
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
open NormalizedRootCentralizers.CenterExponent
open NormalizedRootCentralizers.CenterExponent.OuterElimination

private theorem positiveWord_tail (m : ℕ) (p : PositiveParameters m)
    (ho : OuterCoordinatesZero p) (hm1 : p.main 1 = 0) (hm3 : p.main 3 = 0) :
    positiveWord m p = tailSplitWord m (parameters m p) := by
  simp only [positiveWord_split, splitWord, tailSplitWord, parameters,
    Matrix.cons_val_zero, Matrix.cons_val, ho.pair_eighth,
    ho.pair_second, ho.main_first, ho.main_seventh, ho.central_first, hm1, hm3,
    map_zero, mul_zero, zero_add, xz, one_mul, mul_one]

private theorem remaining_coordinates_zero (m : ℕ) (p : PositiveParameters m)
    (ho : OuterCoordinatesZero p) (hm1 : p.main 1 = 0) (hm3 : p.main 3 = 0)
    (hcomm : ∀ i : Fin 8, ∀ t : CoefficientField m,
      Commute (positiveWord m p) (rootWord m i t)) :
    p.pair 2 = 0 ∧ p.pair 3 = 0 ∧ p.central 2 = 0 ∧ p.central 3 = 0 := by
  have hc (i : Fin 8) :
      Commute (tailSplitWord m (parameters m p)) (rootWord m i 1) := by
    rw [← positiveWord_tail m p ho hm1 hm3]
    exact hcomm i 1
  exact ⟨detect_pairsixth m _ (hc 2), detect_pairfourth m _ (hc 6),
    detect_centralseventh m _ (hc 1), detect_centralthird m _ (hc 7)⟩

private theorem root_zero (m : ℕ) (r : Theory.AlgebraicGroup.F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (Theory.AlgebraicGroup.F4Chevalley.rootCurve_zero r)
private theorem main_zero (m : ℕ) (i : Fin 8) : rootWord m i 0 = 1 := by
  simp [rootWord, root_zero]
private theorem central_zero (m : ℕ) (i : Fin 8) : centralWord m i 0 = 1 := by
  simp [centralWord, root_zero]

/-- Commutation with the actual main curves forces every fixed coordinate
except the central fifth parameter to vanish. -/
theorem positiveWord_eq_central_fifth (m : ℕ) (hm : 0 < m) (p : PositiveParameters m)
    (hcomm : ∀ i : Fin 8, ∀ t : CoefficientField m,
      Commute (positiveWord m p) (rootWord m i t)) :
    positiveWord m p = centralWord m 4 (p.central 1) := by
  have ho := outerCoordinatesZero_of_commute m p hcomm
  obtain ⟨hm1, hm3⟩ := middle_coordinates_zero m hm p ho hcomm
  obtain ⟨hp2, hp3, hc2, hc3⟩ := remaining_coordinates_zero m p ho hm1 hm3 hcomm
  simp [positiveWord, positive_pair_indices, positive_quartet_indices,
    pairCount, quartetCount, List.ofFn_succ, ho.pair_eighth, ho.pair_second,
    ho.main_first, ho.main_seventh, ho.central_first, hm1, hm3, hp2, hp3, hc2, hc3,
    main_zero, central_zero]
end ReeF4.EvenInvolutionGeometry.UnipotentCenter
