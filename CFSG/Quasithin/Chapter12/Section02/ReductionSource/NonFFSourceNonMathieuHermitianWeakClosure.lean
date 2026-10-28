module

public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWeakClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianStrongBounds

/-!
# Hermitian weak closure on the chosen orbit

The original chosen module supplies the normalizer embedding, the non-FF
weak-closure setup and the lower bound r >= 4n when n > 1. The paired-action
argument then forces a hypothetical offender with w < n to have dual core
of rank less than 8n. Consequently the geometric lower bound for that same
dual core suffices for w >= n. The tensor consumer uses the actual half-field
marking and preserves the original Sylow subgroup and offender normalizer.

The final exports discharge the geometric span bound and prove w >= n
for n > 1. They retain the separate n = 1 branch and do not yet exclude
the Hermitian source row.

Source: Aschbacher--Smith H.4.5 and 7.5.6, printed pp.381,701
(refs/quasithin.pdf).
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
variable (D : ChosenModule T L V) (n : ℕ) [NeZero n]

/-- A small original offender has dual core of binary rank less than 8n. -/
theorem sourceOrbit_hermitian_small_offender_dualCore_rank_lt
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (g : G) (hOff : IsWOffenderAt D.sourceOrbit T g)
    (hw : globalW D.sourceOrbit T < n) :
    rank (automizerDualCore D.sourceOrbit
      (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) (3*n)) < 8*n := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  exact Chapter8.Section02.HermitianSource.small_offender_dualCore_rank_lt D.sourceOrbit T n
    (D.hermitianOrbitCoordinates n d) j hj he D.sourceOrbit_weakClosure_setup
    (Or.inr (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon))
    (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn) g hOff hw

/-- The dual-core span bound discharges the remaining geometric premise
of the chosen-orbit weak-closure estimate. -/
theorem sourceOrbit_hermitian_globalW_ge_of_dualCore_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (hspan : ∀ g : G, IsWOffenderAt D.sourceOrbit T g → globalW D.sourceOrbit T < n →
      8*n ≤ rank (automizerDualCore D.sourceOrbit
        (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) (3*n))) :
    (n : ℕ∞) ≤ globalW D.sourceOrbit T := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  exact Chapter8.Section02.HermitianSource.globalW_ge_of_dualCore_span D.sourceOrbit T n
    (D.hermitianOrbitCoordinates n d) j hj he D.sourceOrbit_weakClosure_setup
    (Or.inr (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon))
    (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn) hspan

/-- Literal half-field tensor input gives the same conditional bound on the
original chosen orbit, with no replacement of the action or Sylow subgroup. -/
theorem sourceOrbit_hermitian_tensor_globalW_ge_of_dualCore_span
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n)
    (hspan : ∀ g : G, IsWOffenderAt D.sourceOrbit T g → globalW D.sourceOrbit T < n →
      8*n ≤ rank (automizerDualCore D.sourceOrbit
        (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit g)) (3*n))) :
    (n : ℕ∞) ≤ globalW D.sourceOrbit T := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_globalW_ge_of_dualCore_span n h hmany hV hnon d B eQ hfield hn hspan

/-- The original Hermitian chosen orbit satisfies w >= n when n > 1.
The dual-core span premise is discharged by the root-space calculation. -/
theorem sourceOrbit_hermitian_globalW_ge
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) :
    (n : ℕ∞) ≤ globalW D.sourceOrbit T := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  exact Chapter8.Section02.HermitianSource.globalW_ge_of_hermitian_coordinates D.sourceOrbit T n
    (D.hermitianOrbitCoordinates n d) j hj he D.sourceOrbit_weakClosure_setup
    (Or.inr (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon))
    (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn)

/-- The literal half-field tensor marking gives w >= n on the original
chosen orbit and original Sylow subgroup for n > 1. -/
theorem sourceOrbit_hermitian_tensor_globalW_ge
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) :
    (n : ℕ∞) ≤ globalW D.sourceOrbit T := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
