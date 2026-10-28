module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourWeakImage
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourIntersection

/-!
# Strict intersections in the original zero-closure configuration

The plane's fixed subgroup cannot lie in a moving whole conjugate: its
quadratic hyperplane would make the reverse normalizer too large. Every
such conjugate therefore meets the original orbit in rank at most three.
Joining the orbit to the retained rank-five centralizer kernel gives an
elementary subgroup of the original Sylow of rank at least eleven.

These conclusions use the literal chosen orbit, its original automizer and
its original T. The tensor application supplies the field-four coordinates
by the checked descent and higher-field exclusion. The remaining zero-case
contradiction and the normalizer/centralizer argument through 8.2.13 are
not asserted here.

Source: the Hermitian realization and paired-action argument in
Aschbacher--Smith H.4.2--5, E.3.28--32 and 7.5.6, printed pp.380--382,
237--238,701; refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every moving whole conjugate has strict fixed-subgroup noncontainment
and intersection rank at most three; the original Sylow has rank at least eleven. -/
theorem sourceOrbit_hermitian_zero_intersections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    11 ≤ primeRank 2 T ∧
      ∀ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T →
        ¬ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (D.sourceOrbit : Set G) →
          (¬ D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G) ≤
            D.sourceOrbit.map (MulAut.conj g).toMonoidHom) ∧
          rank (D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom) ≤ 3 := by
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  let e := D.hermitianOrbitCoordinates 1 d
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  refine ⟨field_four_zero_sylow_rank_ge_eleven D.sourceOrbit e j hj he T
    D.sourceOrbit_weakClosure_setup hFF hr hm hw,fun g hg hmove => ?_⟩
  exact ⟨field_four_zero_fixed_not_le_return D.sourceOrbit e j hj he T
      D.sourceOrbit_weakClosure_setup hFF hr hm hw g hg hmove,
    field_four_zero_intersection_rank D.sourceOrbit e j hj he T
      D.sourceOrbit_weakClosure_setup hFF hr hm hw g hg hmove⟩

/-- The half-field tensor input gives the strict intersection geometry on
its actual original orbit and Sylow, retaining the half-degree-one branch. -/
theorem sourceOrbit_hermitian_tensor_zero_intersections
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
    n = 1 ∧ B.degree = 2 ∧ 11 ≤ primeRank 2 T ∧
      ∀ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T →
        ¬ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (D.sourceOrbit : Set G) →
          (¬ D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G) ≤
            D.sourceOrbit.map (MulAut.conj g).toMonoidHom) ∧
          rank (D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj g).toMonoidHom) ≤ 3 := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_zero_intersections h hmany hV hnon d hw

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
