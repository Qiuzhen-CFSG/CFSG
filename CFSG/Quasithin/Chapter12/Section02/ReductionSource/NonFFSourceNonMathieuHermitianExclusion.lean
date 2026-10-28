module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssemblyInputs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourOddControl
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPositiveExclusion

/-!
# Exclusion of the normalized non-FF Hermitian tensor

The original half-field tensor first reduces to field four. Full odd-normalizer
control, now including cubic actors, proves r ≥ 4 in that case. The zero
weak-closure configuration would have r = 3, so it is impossible. The completed
positive-closure argument through 8.2.13 excludes the remaining branch.

The final export discharges the literal HermitianRow premise at the original
chosen-module boundary. It keeps the original Sylow subgroup, component,
normalizer action and all covering kernels, and includes half-degree one.
The known-simple catalogue and ambient hypotheses are those of the source.
Source: Aschbacher–Smith 7.4.1, 7.5.6 and 8.2.2–13, printed pp.700–701, 714–723,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original field-four zero branch contradicts the full source r-bound.
No outer actor or centralizer kernel has been removed from that branch. -/
theorem sourceOrbit_hermitian_field_four_zero_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3, B.Carrier))
    (hfield : B.degree = 2) (hw : globalW D.sourceOrbit T = 0) : False := by
  have hr := D.sourceOrbit_hermitian_field_four_globalR_ge_four
    h hmany hV hnon d B eQ hfield
  have he := (D.sourceOrbit_hermitian_field_four_zero_configuration h hmany hV hnon d hw).1
  rw [he] at hr
  norm_num at hr

/-- The complete normalized half-field tensor exclusion on the literal original
module. The higher-field and both field-four weak-closure branches are discharged. -/
theorem sourceOrbit_hermitian_tensor_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3, B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2 * n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) : False := by
  have hw := D.sourceOrbit_hermitian_tensor_weakClosure_zero
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  obtain ⟨hn, hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d, _, _⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_field_four_zero_impossible h hmany hV hnon d B eQ hB hw

/-- The original non-Mathieu chosen-module consumer for the genuine 3.2.9(4)
row. The family-sieve owner need only supply its actual half-field tensor. -/
theorem sourceOrbit_hermitian_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (_hnm : ¬ Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs) : False := by
  obtain ⟨B, C, ⟨eQ⟩, hn, hfield, _, hmodel⟩ := hrow
  let := inflated_irreducible D.orbitRepresentation C hs.irreducible
  let n := schurDegree (inflated D.orbitRepresentation C)
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact D.sourceOrbit_hermitian_tensor_impossible
    h hmany hV hs hnon B C eQ n rfl hfield hmodel

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
