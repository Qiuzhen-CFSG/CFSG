module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourClosure
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourReciprocal

/-!
# Reciprocal zero-closure geometry on the original chosen orbit

The field-four coordinate marking transfers the plane fixed-subgroup and
reciprocal quadraticity arguments to the literal chosen orbit. Its returning
whole conjugate fixes a Sylow-normal subgroup of rank four; the forward kernel
has rank five and the reverse normalizer has rank at most five. An elementary
enlargement consequently forces the original Sylow subgroup to have two-rank
at least ten.

Tensor descent and the checked higher-field exclusion supply the marking,
retaining half-degree one and every original action. This refines the zero
weak-closure alternative; it does not yet exclude it or complete the
normalizer/centralizer argument through 8.2.13.

Source: Aschbacher--Smith E.3.28--32, H.4.4--5 and 7.5.6,
printed pp.237--238,381--382,701; compare 8.2.5, pp.716--717,
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
open Chapter8.Section02.Offenders.Parabolic.Construction Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  (D : ChosenModule T L V)

/-- The zero-closure reciprocal geometry on the literal chosen orbit,
with the original Sylow and its normal fixed subgroup retained. -/
theorem sourceOrbit_hermitian_field_four_zero_reciprocal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    10 ≤ primeRank 2 T ∧
      ∃ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T ∧
        IsWOffenderAt D.sourceOrbit T g ∧
        rank (D.sourceOrbit ⊓ centralizer
          (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G)) = 4 ∧
        (T : Subgroup G) ≤ normalizer (D.sourceOrbit ⊓ centralizer
          (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) : Set G) ∧
        rank (D.sourceOrbit.map (MulAut.conj g).toMonoidHom ⊓
          centralizer (D.sourceOrbit : Set G)) = 5 ∧
        rank (D.sourceOrbit ⊓ normalizer
          (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G)) ≤ 5 ∧
        ¬ D.sourceOrbit ≤ normalizer
          (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  exact field_four_zero_reciprocal_geometry D.sourceOrbit
    (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw

/-- The actual tensor input in the zero-closure branch forces field four
and a rank-ten elementary subgroup in the original Sylow subgroup. -/
theorem sourceOrbit_hermitian_tensor_zero_sylow_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : globalW D.sourceOrbit T = 0) :
    n = 1 ∧ B.degree = 2 ∧ 10 ≤ primeRank 2 T := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  exact (D.sourceOrbit_hermitian_field_four_zero_reciprocal h hmany hV hnon d hw).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
