module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceNormalizedTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelectedTorusExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelectedTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianStrongBounds

/-!
# The Hermitian selected-torus exclusion with geometric inputs discharged

On the literal chosen orbit, the selected torus normalizes its core actor.
In the intermediate range the actor is large and inner, so the natural
fixed-space calculation supplies the parabolic exponent with no additional
geometric marking. E.2.14 and the automizer rank also give k ≤ 2n. The
original many-overgroups hypothesis supplies TI under N_G(L).

Thus the selected exclusion retains only the earlier E.2.14/local selection
inputs and the rank-one actor degree. The tensor wrapper constructs the
actual coordinates and forces n = k = 1 and field degree two. Constructing selection,
discharging the earlier module inputs, and the field-four 8.2.13 endgame remain
with this task; no full Hermitian exclusion is asserted here.

Source: Aschbacher–Smith 8.2.3–4, printed pp.715–716 (1 March 2004
manuscript, refs/quasithin.pdf).
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
private theorem tensor_coordinates_nonempty_normalized
    {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) A U) (Q : Subgroup A)
    (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (B : BinaryField) (C : LinearCover B 3 Q) (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible ρ C hs.irreducible
      schurDegree (inflated ρ C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible ρ C hs.irreducible
      HasAbsoluteTwistedModel (inflated ρ C) n) :
    Nonempty (ActionEquiv (ρ.comp Q.subtype) (overgroupAction n (binaryImage n))) :=
  ⟨(Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := ρ) (Q := Q) hs B C n hdegree hfield hmodel).choose⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The original non-FF hypothesis, retaining the literal normalizer action.
This exposed definition keeps the large dependent representation out of the
theorem-suggestion index's argument traversal during module export. -/
@[expose] def SourceOrbitNonFF : Prop :=
  ¬ IsFFModule D.sourceOrbitNormalizerRepresentation

/-- The selected-rank argument and the previously proved r-bound remove
the rank, large-actor and preserved-parabolic inputs from the literal intermediate-torus argument. -/
theorem sourceOrbit_hermitian_selected_not_intermediate_of_normalizer
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
    (hx : x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I))
    (hd : k ∣ rank (inducedAutomizer D.sourceOrbit
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k)
    (hnk : n < k) (hkn : k < 2*n) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  exact Chapter8.Section02.HermitianSource.selected_not_intermediate_of_normalizing_torus s n
    (D.hermitianOrbitCoordinates n d) j hj he
    (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn)
    x ho hfixed hx hd hnk hkn

/-- The original automizer rank and E.2.14 imply the upper parameter bound,
including half-degree one. -/
theorem sourceOrbit_hermitian_selected_parameter_upper
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T
      (normalizer (L : Set G)) D.sourceOrbit)
    (hchar : HasCharacteristicTwo H)
    (hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) : k ≤ 2*n := by
  obtain ⟨j,hj,_,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  exact Chapter8.Section02.HermitianSource.selected_parameter_le_two_mul
    KnownSimple.IsKnownSimple eR h28 hchar hTI s n j hj

/-- The endpoint, intermediate and saturated torus cases exclude n > 1
without a geometric marking, a parameter-bound premise or a separate TI input. -/
theorem sourceOrbit_hermitian_selected_excluded_of_rank_degree
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
    (hfield : B.degree = 2*n) (hn : 1 < n)
    (hd : k ∣ rank (inducedAutomizer D.sourceOrbit
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k) :
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
    · obtain ⟨x,hx,ho,_,hf⟩ :=
        D.sourceOrbit_hermitian_selected_torus_fixed eT h28 hchar hTI s (by omega)
      exact D.sourceOrbit_hermitian_selected_not_intermediate_of_normalizer h hmany hV hnon
        s n d B eQ hfield hn x ho hf hx hd (by omega) (by omega)

/-- The coordinate-marked selection has n = k = 1 and field degree two.
The endpoint argument retains n = 1 and forces the selected parameter to one. -/
theorem sourceOrbit_hermitian_selected_field_four_parameters
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
    (hfield : B.degree = 2*n)
    (hd : k ∣ rank (inducedAutomizer D.sourceOrbit
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ∨ Odd k) :
    n = 1 ∧ k = 1 ∧ B.degree = 2 := by
  have hn : n = 1 := by
    by_contra hn
    have hn' : 1 < n := by have hnpos := NeZero.pos n; omega
    exact D.sourceOrbit_hermitian_selected_excluded_of_rank_degree h hmany hV hnon eR eT
      h28 hchar s n d B eQ hfield hn' hd
  have hTI : LocalTI H (normalizer (L : Set G)) D.sourceOrbit := by
    intro g hg
    exact (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti g hg.1
  have hk := D.sourceOrbit_hermitian_selected_parameter_upper h.toHypothesis1221
    eR h28 hchar hTI s n d
  have hkne : k ≠ 2*n := fun he =>
    D.sourceOrbit_hermitian_selected_not_endpoint h.toHypothesis1221
      eR eT h28 hchar hTI s n he d
  exact ⟨hn,by have hp := s.positive; omega,by omega⟩

/-- The literal half-field tensor forces n = k = 1 and field degree two, with all intermediate
geometric inputs discharged. Earlier selection and rank-one module premises
remain explicit; this is not the field-four exclusion. -/
theorem sourceOrbit_hermitian_tensor_selected_field_four_parameters
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
    n = 1 ∧ k = 1 ∧ B.degree = 2 := by
  have hcoords : Nonempty (ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :=
    tensor_coordinates_nonempty_normalized (A := D.orbitActor) (U := D.orbitSpace)
      D.orbitRepresentation D.orbitComponent hs B C n hdegree hfield hmodel
  let d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)) := Classical.choice hcoords
  exact D.sourceOrbit_hermitian_selected_field_four_parameters h hmany hV hnon eR eT
    h28 hchar s n d B eQ hfield hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
