module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceCentralTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSelectionSymplectic

/-!
# Closing the selected Suzuki branch on the original Hermitian tensor

Centrality of the original intersection suffices to bound an odd selected
parameter by the half-field degree. Saturation then makes the constructed
torus fix the full actor-fixed plane. The literal chosen-orbit normalizer,
with its original component image and SQTK hypothesis, excludes the resulting
determinant norm. Thus every selected Suzuki quotient is impossible without
an E.2.14(9) premise.

Combined with the checked linear-two exclusion, any selected pair forces
field four and parameter one. The tensor application retains the rank-four
actor and fixed subgroup, the actual conjugate intersection, and normality
relative to the original Sylow. Selection now needs only source-family
existence to reduce the tensor to field four. This does not finish the
field-four normalizer/centralizer argument through 8.2.13.

Source: Aschbacher–Smith 8.2.2–5, printed pp.714–717,
using H.4.4 and A.1.31 (refs/quasithin.pdf).
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

/-- The original SQTK normalizer excludes a saturated selected torus using
only its centralization of the original intersection. -/
theorem sourceOrbit_hermitian_selected_saturated_excluded_of_centrality
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
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
  obtain ⟨c,g,_,hg,_,hord⟩ := selected_saturated_torus_det_norm_of_centrality s
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


/-- Every odd selected parameter greater than one is excluded, including
the actual Suzuki family, without the source torus fixed-space clause. -/
theorem sourceOrbit_hermitian_selected_odd_parameter_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (hk : 1 < k) (hodd : Odd k)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hu := selected_parameter_le_twice_half_degree s n j hj
  have hk3 : 3 ≤ k := by obtain ⟨m,hm⟩ := hodd; omega
  have hn : 1 < n := by omega
  have hr := D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn
  have hkn := selected_odd_parameter_le_half_degree s hodd n
    (D.hermitianOrbitCoordinates n d) j hj he hr
  obtain ⟨_,x,_,_,_,hx,ho⟩ := selected_exists_automizer_torus s (by omega)
  exact D.sourceOrbit_hermitian_selected_saturated_excluded_of_centrality
    h hmany hV hnon s n d B eQ hfield hn hkn x hx ho

/-- All nonsymplectic selected families on the original tensor force field four. -/
theorem sourceOrbit_hermitian_selected_field_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) : n = 1 ∧ k = 1 ∧ B.degree = 2 := by
  rcases D.sourceOrbit_hermitian_selected_suzuki_or_field_four h hmany hV hnon s n d B eQ hfield with
    hf | ⟨_,m,hm,hk,⟨ξ⟩⟩
  · exact hf
  · exact (D.sourceOrbit_hermitian_selected_odd_parameter_excluded h hmany hV hnon s (by omega) ⟨m,hk⟩ n d B eQ hfield).elim

/-- The selected literal tensor has the field-four fixed subgroup, retaining
its exact intersection, actor rank and normality relative to the original T. -/
theorem sourceOrbit_hermitian_tensor_selected_field_four_fixed_subgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
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
    (n = 1 ∧ k = 1 ∧ B.degree = 2 ∧ A ≤ T ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4 ∧ rank U = 4 ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧ globalR D.sourceOrbit ≤ 5) := by
  rcases D.sourceOrbit_hermitian_tensor_selected_suzuki_or_fixed_subgroup
    h hmany hV hs hnon s B C eQ n hdegree hfield hmodel with
    hf | ⟨_,m,hm,hk,⟨ξ⟩⟩
  · exact hf
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact (D.sourceOrbit_hermitian_selected_odd_parameter_excluded h hmany hV hnon s
    (by omega) ⟨m,hk⟩ n d B eQ hfield).elim

/-- The literal chosen half-field tensor reduces to field four assuming only
family existence. Every torus, actor-rank and symplectic-exclusion premise is discharged. -/
theorem sourceOrbit_hermitian_tensor_field_four_of_family_existence
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : ∀ H : Subgroup G,
      HypothesisE28 KnownSimple.IsKnownSimple H T (normalizer (L : Set G)) D.sourceOrbit →
        ∃ I k, Family H T (normalizer (L : Set G)) D.sourceOrbit I k)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 := by
  rcases D.sourceOrbit_hermitian_tensor_field_four_or_suzuki_of_family_existence
    h hmany hV hs hnon earlier B C eQ n hdegree hfield hmodel with
    hf | ⟨H,I,k,i,S,m,_,s,_,hm,hk,⟨ξ⟩⟩
  · exact hf
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  exact (D.sourceOrbit_hermitian_selected_odd_parameter_excluded h hmany hV hnon s (by omega) ⟨m,hk⟩ n d B eQ hfield).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
