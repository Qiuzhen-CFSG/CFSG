module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceThompson
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneSetup

/-!
# Hermitian higher Thompson control on the original chosen orbit

The literal automizer embedding transfers the Hermitian J₁ argument to
J₁(T) and to N_G(L) intersect C_G(U), preserving the original Sylow and orbit.
The local-centralizer conclusion holds for all positive half-degrees, including
n = 1. Tensor descent constructs the required coordinates from the original
inflated action, so the alpha input has no model or Thompson callback.

This proves the higher Thompson input in the actual E.6.27 centralizer
argument. The odd-element codimension bound and abelian odd-normalizer control
still need proofs before r >= 4n follows. Those inputs, selection, n <= w,
k <= n, the torus argument and the field-four endgame remain with
qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.4.4–5,
7.3.2, 7.4.1 and E.6.27, printed pp.381–382,698–700,257
(refs/quasithin.pdf).
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
  (D : ChosenModule T L V)
variable (n : ℕ) [NeZero n]
  (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (overgroupAction n (binaryImage n)))

include d in
/-- For n > 1, the actual J₁(T) fixes the original chosen orbit. -/
theorem sourceOrbit_hermitian_thompson_one_centralizes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hn : 1 < n) :
    thompsonJ (T : Subgroup G) 1 ≤ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.thompson_one_centralizes_of_one_lt
    D.sourceOrbit T n (D.hermitianOrbitCoordinates n d) j hj he
    D.sourceOrbit_weakClosure_setup.le_sylow D.sourceOrbit_weakClosure_setup.normalizes hn

include d in
/-- The alpha premise of E.6.27 on the literal local centralizer, including n = 1. -/
theorem sourceOrbit_hermitian_localCentralizer_thompson_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ D.sourceOrbit)
    (hc : subgroupCorank D.sourceOrbit U < 4*n) :
    thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) 1 ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  exact Chapter8.Section02.HermitianSource.localCentralizer_thompson_one D.sourceOrbit n
    (D.hermitianOrbitCoordinates n d) j hj he
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon) hU hUV hc

/-- Literal tensor descent discharges the alpha input for all the small
subspaces, preserving the original T and the field-four case. -/
theorem sourceOrbit_hermitian_tensor_localCentralizer_thompson_one
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUV : U ≤ D.sourceOrbit)
    (hc : subgroupCorank D.sourceOrbit U < 4*n) :
    thompsonJ (normalizer (L : Set G) ⊓ centralizer (U : Set G)) 1 ≤
      normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_localCentralizer_thompson_one n d h hmany hV hnon hU hUV hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
