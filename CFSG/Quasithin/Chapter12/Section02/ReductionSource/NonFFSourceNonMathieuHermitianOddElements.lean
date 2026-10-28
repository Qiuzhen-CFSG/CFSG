module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceOddElements
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# Odd-element displacement on the original Hermitian chosen orbit

The original automizer embeds faithfully in the binary Hermitian normalizer.
The odd-element estimate therefore applies to its literal cyclic subgroups.
Tensor descent supplies the coordinates from the given half-field marking,
including n = 1. No fixed-space or odd-element estimate is an extra premise.

This supplies beta >= 4n in the source 7.4.1 argument. Ambient odd-normalizer
control, selection, the weak-closure bounds and the terminal exclusions remain
with qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2 and
7.4.1, printed pp.382,699–700 (refs/quasithin.pdf).
-/

public noncomputable section
open scoped Classical IsMulCommutative MatrixGroups
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (n : ℕ) [NeZero n]

/-- Every nonidentity odd automizer of the original chosen orbit moves at least 4n dimensions. -/
theorem sourceOrbit_hermitian_odd_fixedCodim
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (a : Automizer D.sourceOrbit) (ho : Odd (orderOf a)) (hne : a ≠ 1) :
    4*n ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.odd_fixedCodim_ge_four_mul_of_equivariant n
    (automizerRepresentation D.sourceOrbit) j hj (D.hermitianOrbitCoordinates n d) he a ho hne

/-- The literal half-field tensor input discharges the odd-element bound,
without changing the chosen module, action, component or original Sylow. -/
theorem sourceOrbit_hermitian_tensor_odd_fixedCodim
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (a : Automizer D.sourceOrbit) (ho : Odd (orderOf a)) (hne : a ≠ 1) :
    4*n ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_odd_fixedCodim n d h a ho hne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
