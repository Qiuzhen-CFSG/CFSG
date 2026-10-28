module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianNormalizedTorus
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianNormalizedTorus

/-!
# The original field-four selected actor and fixed subgroup

The selected parameter one makes the original core actor a near-offender.
Its literal Hermitian coordinates force rank four and identify its fixed
subgroup with the original conjugate intersection. The same plane marking
gives relative normality in the original Sylow subgroup and centralization
by the original selected group. The tensor consumer first applies the
torus exclusion, then supplies these conclusions without extra r or w bounds.

The earlier E.2/selection and actor-degree premises remain explicit. The
normalizer and centralizer argument through 8.2.13 still has to exclude this
configuration; no full Hermitian exclusion or equality r = 5 is asserted.
Source: Aschbacher–Smith 8.2.4–5, printed pp.716–717
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The original parameter-one actor and its fixed subgroup, retaining the
original Sylow subgroup, selected group and tensor coordinates. -/
theorem sourceOrbit_hermitian_selected_one_fixed_subgroup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    n = 1 ∧ A ≤ T ∧ rank (inducedAutomizer D.sourceOrbit A) = 4 ∧ rank U = 4 ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR D.sourceOrbit ≤ 5 ∧
      ∃ c : Cover n, ((inducedAutomizer D.sourceOrbit A).map
        (coordinateHom (automizerRepresentation D.sourceOrbit) n
          (D.hermitianOrbitCoordinates n d))).map
        (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  have hh := Chapter8.Section02.HermitianSource.selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
  have hf : (binaryNormalizer n).subtype.comp j =
      coordinateHom (automizerRepresentation D.sourceOrbit) n
        (D.hermitianOrbitCoordinates n d) := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  rwa [hf] at hh

/-- The original half-field tensor and the selected-torus reduction supply
the rank-four fixed subgroup, its relative normality and its centralizing
selected group. Earlier selection inputs and the final exclusion remain. -/
theorem sourceOrbit_hermitian_tensor_selected_fixed_subgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hd : k ∣ rank (inducedAutomizer D.sourceOrbit
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    n = 1 ∧ k = 1 ∧ B.degree = 2 ∧ A ≤ T ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4 ∧ rank U = 4 ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR D.sourceOrbit ≤ 5 := by
  have hcoords : Nonempty (ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :=
    tensor_coordinates_nonempty_normalized (A := D.orbitActor) (U := D.orbitSpace)
      D.orbitRepresentation D.orbitComponent hs B C n hdegree hfield hmodel
  let d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)) := Classical.choice hcoords
  obtain ⟨hn,hk,hB⟩ := D.sourceOrbit_hermitian_selected_field_four_parameters h hmany hV hnon
    eR eT h28 hchar s n d B eQ hfield hd
  subst k
  obtain ⟨_,hAT,ha,hu,hU,hUT,hTN,hIC,hr,_⟩ :=
    D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s n d
  exact ⟨hn,rfl,hB,hAT,ha,hu,hU,hUT,hTN,hIC,hr⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
