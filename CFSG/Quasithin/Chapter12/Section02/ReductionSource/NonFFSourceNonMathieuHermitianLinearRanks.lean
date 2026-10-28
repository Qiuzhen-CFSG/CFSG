module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearRanks
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelectionCenter

/-!
# Removing the E.2.14 rank premise from the chosen Hermitian tensor

The actual selected actor has rank at least twice its parameter. Its embedding
in the original Hermitian automizer bounds that parameter by 2n, and the
natural-sum calculation excludes equality. The checked intermediate and
saturated torus arguments then force n = k = 1. The literal rank-four fixed
subgroup, relative Sylow normality and selected-group centralization follow.

The final tensor theorem constructs selection for n > 1 from its remaining
witness and symplectic-exclusion clauses. Only these selection clauses and
the E.2.14 torus clause remain explicit; the rank clause is proved here.
This retains every original action and n = 1. The field-four argument
through 8.2.13, and hence the full Hermitian exclusion, remain unfinished.
Source: Aschbacher–Smith E.2.14(3,7), pp.226–228, and 8.2.2–5,
pp.714–717 (refs/quasithin.pdf).
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
open Chapter8.Section02.Offenders.Parabolic.Construction Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The literal selected parameter bound, with the E.2.14 rank premise discharged. -/
theorem sourceOrbit_hermitian_selected_parameter_upper_of_natural_sum
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) : k ≤ 2*n := by
  obtain ⟨j,hj,_,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact selected_parameter_le_twice_half_degree s n j hj

/-- The actual chosen action excludes k = 2n, including n = 1. Only the
source torus clause remains explicit. -/
theorem sourceOrbit_hermitian_selected_not_endpoint_of_natural_sum
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n] (hkn : k = 2*n)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  obtain ⟨x,hx,ho,_,hf⟩ := D.sourceOrbit_hermitian_selected_torus_fixed
    eT h28 hchar hTI s (by have hn := NeZero.pos n; omega)
  exact selected_not_endpoint_of_natural_sum s n hkn (D.hermitianOrbitCoordinates n d)
    j hj he x ho hx hf

/-- The endpoint, intermediate and saturated torus cases exclude n > 1
without an E.2.14 rank, actor-degree, geometric-marking or separate TI premise. -/
theorem sourceOrbit_hermitian_selected_excluded_of_natural_sum
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
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
  have hk := D.sourceOrbit_hermitian_selected_parameter_upper_of_natural_sum h.toHypothesis1221 s n d
  by_cases hkn : k ≤ n
  · exact D.sourceOrbit_hermitian_selected_saturated_excluded h hmany hV hnon
      eT h28 hchar hTI s n d B eQ hfield hn hkn
  · by_cases he : k = 2*n
    · exact D.sourceOrbit_hermitian_selected_not_endpoint_of_natural_sum h.toHypothesis1221
        eT h28 hchar hTI s n he d
    · obtain ⟨x,_,ho,_,hf⟩ :=
        D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s (by omega)
      exact D.sourceOrbit_hermitian_selected_not_intermediate_geometric h hmany hV hnon
        s n d B eQ hfield hn x ho hf (by omega) (by omega)

/-- The coordinate-marked selection has n = k = 1 and field degree two.
The endpoint argument retains n = 1 and forces the selected parameter to one. -/
theorem sourceOrbit_hermitian_selected_field_four_parameters_of_natural_sum
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
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
    exact D.sourceOrbit_hermitian_selected_excluded_of_natural_sum h hmany hV hnon eT
      h28 hchar s n d B eQ hfield hn'
  have hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit := by
    intro g hg
    exact (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti g hg.1
  have hk := D.sourceOrbit_hermitian_selected_parameter_upper_of_natural_sum h.toHypothesis1221 s n d
  have hkne : k ≠ 2*n := fun he =>
    D.sourceOrbit_hermitian_selected_not_endpoint_of_natural_sum h.toHypothesis1221
      eT h28 hchar hTI s n he d
  exact ⟨hn,by have hp := s.positive; omega,by omega⟩

/-- The original half-field tensor and the selected-torus reduction supply
the rank-four fixed subgroup, its relative normality and its centralizing
selected group. Earlier selection inputs and the final exclusion remain. -/
theorem sourceOrbit_hermitian_tensor_selected_fixed_subgroup_of_natural_sum
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
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
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_tensor_hstar_setup
    h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  obtain ⟨hn,hk,hB⟩ := D.sourceOrbit_hermitian_selected_field_four_parameters_of_natural_sum h hmany hV hnon
    eT h28 hchar s n d B eQ hfield
  subst k
  obtain ⟨_,hAT,ha,hu,hU,hUT,hTN,hIC,hr,_⟩ :=
    D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s n d
  exact ⟨hn,rfl,hB,hAT,ha,hu,hU,hUT,hTN,hIC,hr⟩


/-- The original tensor reduces to field four from the remaining selection
and torus sources. No E.2.14 rank premise or chosen replacement action remains. -/
theorem sourceOrbit_hermitian_tensor_field_four_of_selection_and_torus
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionWitnessSources (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hn : n = 1 := by
    by_contra hn
    have hn' : 1 < n := by have hp := NeZero.pos n; omega
    have hw := D.sourceOrbit_hermitian_tensor_globalW_ge n h hmany hV hs hnon
      B C eQ hdegree hfield hmodel hn'
    have hwpos : 0 < globalW D.sourceOrbit T :=
      (show (0 : ℕ∞) < (n : ℕ∞) by exact_mod_cast NeZero.pos n).trans_le hw
    have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
      refine ⟨B,C,⟨eQ⟩,?_⟩
      dsimp only
      rw [hdegree]
      exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
    obtain ⟨H,I,k,i,S,_,h28,hchar,s⟩ :=
      D.sourceOrbit_hermitian_exists_selected_of_witness_sources h hmany hV hnon hs hrow earlier hwpos
    exact D.sourceOrbit_hermitian_selected_excluded_of_natural_sum h hmany hV hnon
      eT h28 hchar s n d B eQ hfield hn'
  exact ⟨hn,by omega⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
