module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceGeometricTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourSelection
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianNormalizedTorus

/-!
# The original Hermitian tensor reduction without actor-degree assumptions

The strengthened fixed-plane calculation excludes the intermediate selected
parameter on the actual chosen orbit. Combining it with the checked endpoint
and saturated exclusions forces n=k=1 and field degree two. Tensor descent
then gives the original rank-four fixed subgroup, its literal conjugate
intersection, relative Sylow normality and centralization by the selected I.
Its normalizer is a characteristic-two local overgroup of the original T.

The actor-degree disjunction is discharged geometrically, not imposed on the
selected quotient. Selection and the earlier E.2.14 rank and torus clauses
remain explicit; the normalizer/centralizer argument through 8.2.13 remains
open. These exports do not assert r=5 or the full Hermitian source exclusion.

Source: Aschbacher–Smith 8.2.3–5 and the introduction to 8.2.6,
printed pp.715–717 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The selected-rank argument and the previously proved r-bound remove
the rank, actor-degree and geometric premises from the literal intermediate-torus argument. -/
theorem sourceOrbit_hermitian_selected_not_intermediate_geometric
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (x : Automizer D.sourceOrbit) (ho : orderOf x = 2^k-1)
    (hfixed : automizerFixedGroup D.sourceOrbit (zpowers x) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hnk : n < k) (hkn : k < 2*n) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  exact Chapter8.Section02.HermitianSource.selected_not_intermediate_of_fixed_plane s n
    (D.hermitianOrbitCoordinates n d) j hj he
    (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn)
    x ho hfixed hnk hkn

/-- The endpoint, intermediate and saturated torus cases exclude n > 1
without an actor-degree, geometric-marking, parameter-bound or separate TI premise. -/
theorem sourceOrbit_hermitian_selected_excluded_geometric
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) :
    False := by
  have hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit := by
    intro g hg
    exact (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti g hg.1
  have hk := D.sourceOrbit_hermitian_selected_parameter_upper h.toHypothesis1221
    eR h28 hchar hTI s n d
  by_cases hkn : k ≤ n
  · exact D.sourceOrbit_hermitian_selected_saturated_excluded h hmany hV hnon
      eT h28 hchar hTI s n d B eQ hfield hn hkn
  · by_cases he : k = 2*n
    · exact D.sourceOrbit_hermitian_selected_not_endpoint h.toHypothesis1221
        eR eT h28 hchar hTI s n he d
    · obtain ⟨x,_,ho,_,hf⟩ :=
        D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s (by omega)
      exact D.sourceOrbit_hermitian_selected_not_intermediate_geometric h hmany hV hnon
        s n d B eQ hfield hn x ho hf (by omega) (by omega)

/-- The coordinate-marked selection has n = k = 1 and field degree two.
The endpoint argument retains n = 1 and forces the selected parameter to one. -/
theorem sourceOrbit_hermitian_selected_field_four_parameters_geometric
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) :
    n = 1 ∧ k = 1 ∧ B.degree = 2 := by
  have hn : n = 1 := by
    by_contra hn
    have hn' : 1 < n := by have hnpos := NeZero.pos n; omega
    exact D.sourceOrbit_hermitian_selected_excluded_geometric h hmany hV hnon eR eT
      h28 hchar s n d B eQ hfield hn'
  have hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit := by
    intro g hg
    exact (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti g hg.1
  have hk := D.sourceOrbit_hermitian_selected_parameter_upper h.toHypothesis1221
    eR h28 hchar hTI s n d
  have hkne : k ≠ 2*n := fun he =>
    D.sourceOrbit_hermitian_selected_not_endpoint h.toHypothesis1221
      eR eT h28 hchar hTI s n he d
  exact ⟨hn,by have hp := s.positive; omega,by omega⟩

/-- The original half-field tensor and the selected-torus reduction supply
the rank-four fixed subgroup, its relative normality and its centralizing
selected group. Earlier selection inputs and the final exclusion remain. -/
theorem sourceOrbit_hermitian_tensor_selected_fixed_subgroup_geometric
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
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
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
  obtain ⟨hn,hk,hB⟩ := D.sourceOrbit_hermitian_selected_field_four_parameters_geometric h hmany hV hnon
    eR eT h28 hchar s n d B eQ hfield
  subst k
  obtain ⟨_,hAT,ha,hu,hU,hUT,hTN,hIC,hr,_⟩ :=
    D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s n d
  exact ⟨hn,rfl,hB,hAT,ha,hu,hU,hUT,hTN,hIC,hr⟩

/-- The literal field-four fixed subgroup supplies the next characteristic-two
local normalizer, without a lower bound on either weak-closure parameter. -/
theorem sourceOrbit_hermitian_selected_one_local_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    U ≠ ⊥ ∧ normalizer (U : Set G) ∈ Chapter1.HeOver G (T : Set G) ∧
      HasCharacteristicTwo (normalizer (U : Set G)) ∧ I ≤ centralizer (U : Set G) := by
  obtain ⟨_,_,_,hU,_,_,hTN,hIC,_,_⟩ :=
    D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s n d
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  have hne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hU
    rw [hz,Representation.BinaryOffender.rank_bot] at hU
    omega
  have hUT : U ≤ T := inf_le_left.trans D.sourceOrbit_weakClosure_setup.le_sylow
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hne,T.isPGroup'.to_le hUT,rfl⟩
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T
    (h.simpleQTKE.evenCharacteristic T) hlocal hTN
  exact ⟨hne,⟨hHe,Chapter1.mem_H_of_isTwoLocal hlocal,hTN⟩,
    Chapter1.mem_He_iff.mp hHe,hIC⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
