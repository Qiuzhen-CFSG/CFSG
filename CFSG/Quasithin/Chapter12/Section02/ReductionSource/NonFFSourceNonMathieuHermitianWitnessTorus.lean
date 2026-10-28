module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianWitnessGeometry
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessSaturation

/-!
# The original Hermitian half-field tensor has field four

The actual witnesses construct geometric selections without assuming that their
field degree divides the ambient generation parameter. The linear torus excludes
the endpoint and intermediate degrees. For odd degree, centrality of the original
intersection gives the needed parameter bound. In the remaining saturated range,
the original two-local SQTK normalizer excludes the determinant norm of the same
torus. Thus every geometric selection has parameter one and half-degree one.

Applying this to the constructed higher-field witnesses proves n = 1 and
B.degree = 2 from the original chosen-module tensor input, with no selection,
rank, torus or generation-parameter premise. The field-four fixed-subgroup
application retains the original conjugator, quotient, Sylow and automizer.
The field-four normalizer/centralizer contradiction through 8.2.13 remains;
this module does not assert the complete Hermitian exclusion.

Source: Aschbacher--Smith 8.2.2--5, printed pp.714--717,
using E.2.14, H.4.4 and A.1.31, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

theorem sourceOrbit_hermitian_geometric_saturated_excluded_of_centrality
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) (hn : 1 < n) (hk : k ≤ n)
    (x : Automizer D.sourceOrbit)
    (hx : x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I))
    (ho : orderOf x = 2^k-1) : False := by
  obtain ⟨j,hj,he,hmark⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hw := D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn
  have hr := D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn
  obtain ⟨c,g,_,hg,_,hord⟩ := GeometricSelected.saturated_torus_det_norm_of_centrality s
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
    hw hk hr x hx ho
  let f₀ := coordinateHom (automizerRepresentation D.sourceOrbit) n
    (D.hermitianOrbitCoordinates n d)
  have hc : (binaryNormalizer n).subtype.comp j = f₀ := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  have hinner₀ : binaryImage n ≤ f₀.range := by
    intro a ha
    obtain ⟨q,hq⟩ := d.groupEquiv.surjective ⟨a,ha⟩
    obtain ⟨l,hl⟩ := D.orbitComponentHom_surjective q
    refine ⟨D.hermitianComponentAutomizer l,?_⟩
    rw [←hc]
    change (j (D.hermitianComponentAutomizer l)).val = a
    exact (hmark l).trans (congrArg Subtype.val ((congrArg d.groupEquiv hl).trans hq))
  let N := normalizer (D.sourceOrbit : Set G)
  let qN : N →* Automizer D.sourceOrbit := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  have hqN : Function.Surjective qN := D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
  let u := binaryActionHom n c
  let z := (MulAut.conj u).toMonoidHom
  let f : N →* BinaryAut n := z.comp (f₀.comp qN)
  have hu : u ∈ binaryImage n := ⟨c,rfl⟩
  have hinner : binaryImage n ≤ f.range := by
    intro a ha
    have ha' : u⁻¹*a*u ∈ binaryImage n :=
      (binaryImage n).mul_mem ((binaryImage n).mul_mem ((binaryImage n).inv_mem hu) ha) hu
    obtain ⟨b,hb⟩ := hinner₀ ha'
    obtain ⟨v,hv⟩ := hqN b
    refine ⟨v,?_⟩
    change u * f₀ (qN v) * u⁻¹ = a
    rw [hv,hb]
    simp [mul_assoc]
  have hgim : binaryCongruence n g ∈ f.range := by
    obtain ⟨v,hv⟩ := hqN x
    refine ⟨v,?_⟩
    change z (f₀ (qN v)) = binaryCongruence n g
    rw [hv]
    rw [←hc]
    exact hg.symm
  have hN : IsSQTK KnownSimple.IsKnownSimple N :=
    h.toHypothesis1221.simpleQTKE.twoLocal_sqtk
      ⟨D.sourceOrbit,D.sourceOrbit_weakClosure_setup.nontrivial,
        IsElementaryAbelian.isPGroup 2 D.sourceOrbit,rfl⟩
  exact no_split_det_norm_in_rank_two_cover n f hinner hN.stronglyQuasithin g hgim hord hn

theorem sourceOrbit_hermitian_geometric_odd_parameter_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (hk : 1 < k) (hodd : Odd k)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hu := GeometricSelected.parameter_le_twice_half_degree s n j hj
  have hk3 : 3 ≤ k := by obtain ⟨m,hm⟩ := hodd; omega
  have hn : 1 < n := by omega
  have hr := D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn
  have hkn := GeometricSelected.odd_parameter_le_half_degree s hodd n
    (D.hermitianOrbitCoordinates n d) j hj he hr
  obtain ⟨_,x,_,_,_,hx,ho⟩ := GeometricSelected.exists_automizer_torus s (by omega)
  exact D.sourceOrbit_hermitian_geometric_saturated_excluded_of_centrality
    h hmany hV hnon s n d B eQ hfield hn hkn x hx ho

/-- The actual geometric linear quotient is impossible, without any
ambient generation-parameter or E.2.14 callback. Half-degree one is included. -/
theorem sourceOrbit_hermitian_geometric_linear_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (hk : 1 < k) (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k))
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  obtain ⟨_,x,_,_,_,hx,ho,hf⟩ := s.linear_exists_torus_fixed hk ξ
  have hku := s.parameter_le_twice_half_degree n j hj
  have hendpoint : k ≠ 2*n := fun heq => s.not_endpoint n heq
    (D.hermitianOrbitCoordinates n d) j hj he x ho hx hf
  have hn : 1 < n := by have hp := NeZero.pos n; omega
  by_cases hkn : k ≤ n
  · exact D.sourceOrbit_hermitian_geometric_saturated_excluded_of_centrality
      h hmany hV hnon s n d B eQ hfield hn hkn x hx ho
  · exact s.not_intermediate_of_fixed_plane n (D.hermitianOrbitCoordinates n d) j hj he
      (D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn)
      x ho hf (by omega) (by omega)

/-- All actual geometric families force field four and parameter one.
The parameter-one conversion uses only the tautological divisibility 1 ∣ n(H). -/
theorem sourceOrbit_hermitian_geometric_field_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) : n = 1 ∧ k = 1 ∧ B.degree = 2 := by
  rcases s.models with ⟨hk,ξ,_⟩ | ⟨m,hm,hk,ξ,_⟩ | ⟨hk,_⟩
  · exact (D.sourceOrbit_hermitian_geometric_linear_excluded
      h hmany hV hnon s hk ξ n d B eQ hfield).elim
  · exact (D.sourceOrbit_hermitian_geometric_odd_parameter_excluded
      h hmany hV hnon s (by omega) ⟨m,hk⟩ n d B eQ hfield).elim
  · subst k
    have hn := (D.sourceOrbit_hermitian_selected_one_fixed_subgroup
      h.toHypothesis1221 (s.toSelected (one_dvd _)) n d).1
    exact ⟨hn,rfl,by omega⟩

/-- The selected rank-four actor and fixed subgroup on the actual action.
This uses no generation-parameter divisibility beyond the proved k = 1. -/
theorem sourceOrbit_hermitian_geometric_fixed_subgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    n = 1 ∧ k = 1 ∧ B.degree = 2 ∧ A ≤ T ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4 ∧ rank U = 4 ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR D.sourceOrbit ≤ 5 := by
  obtain ⟨hn,hk,hB⟩ := D.sourceOrbit_hermitian_geometric_field_four h hmany hV hnon s n d B eQ hfield
  subst k
  obtain ⟨_,hAT,ha,hu,hU,hUT,hTN,hIC,hr,_⟩ :=
    D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221
      (s.toSelected (one_dvd _)) n d
  exact ⟨hn,rfl,hB,hAT,ha,hu,hU,hUT,hTN,hIC,hr⟩

/-- The original half-field tensor is over field four. Actual higher-field
witnesses discharge selection; the geometric torus proof discharges every
additional rank, torus and generation-parameter premise. The field-four
normalizer/centralizer exclusion is a separate remaining source obligation. -/
theorem sourceOrbit_hermitian_tensor_field_four
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
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 := by
  rcases D.sourceOrbit_hermitian_tensor_field_four_or_geometric_selection
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel with hf | ⟨H,_,I,k,i,S,s,hk,_⟩
  · exact hf
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have he := D.sourceOrbit_hermitian_geometric_field_four h hmany hV hnon s n d B eQ hfield
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
