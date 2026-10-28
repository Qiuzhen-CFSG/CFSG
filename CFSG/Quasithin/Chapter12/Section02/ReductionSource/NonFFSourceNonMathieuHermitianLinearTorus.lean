module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearTorus
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianLinearRanks

/-!
# Eliminating the selected PSL₂ family on the original Hermitian tensor

The proved torus fixed subgroup removes E.2.14(9) from the linear-two case.
The actual actor-rank bound excludes the endpoint k = 2n. Fixed-plane geometry
excludes n < k < 2n. In the saturated range k ≤ n, the original normalizer's
SQTK hypothesis excludes the determinant norm forced by the same torus.
This rules out every selected PSL₂ quotient, including half-degree one.

The remaining selected alternatives are field four with k = 1, or an actual
Suzuki quotient with n > 1. The tensor application retains the original orbit,
Sylow, action and quotient maps and supplies the rank-four fixed subgroup in
the field-four case. The final application retains only the two undischarged
selection clauses, returning the literal selected Suzuki pair in higher degree.
Witness existence, symplectic exclusion, the Suzuki torus calculation and the
field-four normalizer/centralizer argument through 8.2.13 remain unfinished.

Source: Aschbacher–Smith E.2.14(9), pp.226–227, and 8.2.2–5,
pp.714–717 (refs/quasithin.pdf).
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

/-- The linear-two torus on the actual chosen orbit, without an E.2.14 input. -/
theorem sourceOrbit_hermitian_selected_linear_torus_fixed
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k)) :
    ∃ x : Automizer D.sourceOrbit,
      x ∈ inducedAutomizer D.sourceOrbit (normalizer (L : Set G) ⊓ I) ∧
      orderOf x = 2^k-1 ∧
      automizerFixedGroup D.sourceOrbit (zpowers x) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨_,x,_,_,_,hx,ho,hfixed⟩ := selected_linear_exists_torus_fixed s hk ξ
  exact ⟨x,hx,ho,hfixed⟩

private theorem saturated_excluded_with_torus
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
    (ho : orderOf x = 2^k-1)
    (hf : automizerFixedGroup D.sourceOrbit (zpowers x) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom) : False := by
  obtain ⟨j,hj,he,hmark⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  have hw := D.sourceOrbit_hermitian_globalW_ge n h hmany hV hnon d B eQ hfield hn
  have hr := D.sourceOrbit_hermitian_globalR_ge_four_mul n h hmany hV hnon d B eQ hfield hn
  obtain ⟨c,g,_,hg,_,hord,_⟩ := selected_saturated_torus_det_norm_order s
    D.sourceOrbit_weakClosure_setup n hn (D.hermitianOrbitCoordinates n d) j hj he
    hw hk hr x hx ho hf
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

/-- Every selected PSL₂ family is excluded on the original Hermitian action.
The torus fixed-space and actor-rank clauses are both proved, including n = 1. -/
theorem sourceOrbit_hermitian_selected_linear_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (hk : 1 < k) (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k))
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) : False := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  obtain ⟨x,hx,ho,hf⟩ := D.sourceOrbit_hermitian_selected_linear_torus_fixed s hk ξ
  have hku := selected_parameter_le_twice_half_degree s n j hj
  have hendpoint : k ≠ 2*n := fun heq => selected_not_endpoint_of_natural_sum s n heq
    (D.hermitianOrbitCoordinates n d) j hj he x ho hx hf
  have hn : 1 < n := by have hp := NeZero.pos n; omega
  by_cases hkn : k ≤ n
  · exact D.saturated_excluded_with_torus h hmany hV hnon s n d B eQ hfield hn hkn x hx ho hf
  · exact D.sourceOrbit_hermitian_selected_not_intermediate_geometric h hmany hV hnon
      s n d B eQ hfield hn x ho hf (by omega) (by omega)

/-- After excluding the linear family, the original selected pair either has
field-four parameter one or has an actual Suzuki quotient. No torus source
clause remains in this reduction. -/
theorem sourceOrbit_hermitian_selected_suzuki_or_field_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2*n) :
    (n = 1 ∧ k = 1 ∧ B.degree = 2) ∨
      (1 < n ∧ ∃ m : ℕ, 0 < m ∧ k = 2*m+1 ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m)) := by
  rcases s.models with ⟨hk,ξ,_⟩ | ⟨m,hm,hk,ξ,_⟩ | ⟨hk,_⟩
  · exact (D.sourceOrbit_hermitian_selected_linear_excluded h hmany hV hnon s hk ξ n d B eQ hfield).elim
  · have hu := D.sourceOrbit_hermitian_selected_parameter_upper_of_natural_sum h.toHypothesis1221 s n d
    exact Or.inr ⟨by omega,m,hm,hk,⟨ξ⟩⟩
  · subst k
    have hn := (D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s n d).1
    exact Or.inl ⟨hn,rfl,by omega⟩

/-- The literal half-field tensor supplies the same dichotomy, with the
rank-four fixed subgroup and its relative normality in the field-four branch.
The genuine Suzuki branch and witness selection remain to be discharged. -/
theorem sourceOrbit_hermitian_tensor_selected_suzuki_or_fixed_subgroup
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
      I ≤ centralizer (U : Set G) ∧ globalR D.sourceOrbit ≤ 5) ∨
    (1 < n ∧ ∃ m : ℕ, 0 < m ∧ k = 2*m+1 ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m)) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  rcases D.sourceOrbit_hermitian_selected_suzuki_or_field_four h hmany hV hnon s n d B eQ hfield with
    ⟨hn,hk,hB⟩ | hsz
  · subst k
    obtain ⟨_,hAT,ha,hu,hU,hUT,hTN,hIC,hr,_⟩ :=
      D.sourceOrbit_hermitian_selected_one_fixed_subgroup h.toHypothesis1221 s n d
    exact Or.inl ⟨hn,rfl,hB,hAT,ha,hu,hU,hUT,hTN,hIC,hr⟩
  · exact Or.inr hsz

/-- The original tensor and the two remaining selection clauses reduce the
higher-degree source branch to a literal selected Suzuki quotient. The linear
torus clause has been discharged and is not assumed in this application. -/
theorem sourceOrbit_hermitian_tensor_field_four_or_suzuki_of_selection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (earlier : SelectionWitnessSources (G := G) KnownSimple.IsKnownSimple)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    (n = 1 ∧ B.degree = 2) ∨
      ∃ (H I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I) (m : ℕ),
        H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S ∧
        1 < n ∧ 0 < m ∧ k = 2*m+1 ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* SuzukiMatrixGroup m) := by
  by_cases hn : n = 1
  · exact Or.inl ⟨hn,by omega⟩
  have hn' : 1 < n := by have hp := NeZero.pos n; omega
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hw := D.sourceOrbit_hermitian_tensor_globalW_ge n h hmany hV hs hnon
    B C eQ hdegree hfield hmodel hn'
  have hwpos : 0 < globalW D.sourceOrbit T :=
    (show (0 : ℕ∞) < (n : ℕ∞) by exact_mod_cast NeZero.pos n).trans_le hw
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨H,I,k,i,S,hH,_,_,s⟩ :=
    D.sourceOrbit_hermitian_exists_selected_of_witness_sources h hmany hV hnon hs hrow earlier hwpos
  rcases D.sourceOrbit_hermitian_selected_suzuki_or_field_four h hmany hV hnon s n d B eQ hfield with
    ⟨he,_,_⟩ | ⟨hn,m,hm,hk,he⟩
  · exact (hn he).elim
  · exact Or.inr ⟨H,I,k,i,S,m,hH,s,hn,hm,hk,he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
