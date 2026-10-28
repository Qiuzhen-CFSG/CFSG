module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianWitnessTorus
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourClosure

/-!
# The remaining weak-closure alternatives for the field-four Hermitian tensor

The checked higher-field exclusion first forces n = 1. Positive weak closure
then constructs an original witness in every H-star subgroup; geometric
selection and the torus exclusions give parameter one, with no divisibility
premise. Its actual core actor attains w = 1.

The zero branch is kept explicit. It forces r = s = m = 3, an outer
involution in the original automizer and a returning whole conjugate whose
inner actor has rank four and whose centralizer kernel has rank five.
Thus field-four selection follows from r >= 4; that remaining bound is not
silently imported from the higher-field theorem. The full normalizer and
centralizer exclusion through 8.2.13 is still required.

Source: Aschbacher--Smith 7.3.2,7.5.6 and 8.2.2--5, pp.698,701,714--717,
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

/-- Positive weak closure constructs the literal parameter-one pair, including
half-degree one. No selection or generation-parameter premise remains. -/
theorem sourceOrbit_hermitian_tensor_selected_of_positive
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
    (hw : 0 < globalW D.sourceOrbit T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_tensor_hstar_setup
    h hmany hV hs hnon hH B C eQ n hdegree hfield hmodel
  obtain ⟨R,hR,f,⟨w⟩⟩ := exists_original_witness_of_positive_weak_closure h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar)
    (D.sourceOrbit_hstar_intersection_normalizes h hmany hV hnon hH) hw
  obtain ⟨I,i,S,s⟩ := geometric_selected_of_original_witness h28
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar) R hR w
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hk := (D.sourceOrbit_hermitian_geometric_field_four
    h hmany hV hnon s n d B eQ hfield).2.1
  have hwu := (s.core_actor_data D.sourceOrbit_weakClosure_setup).2.2.2.2
  rw [hk] at hwu
  have hw1 : globalW D.sourceOrbit T = 1 := le_antisymm hwu
    (Order.one_le_iff_pos.mpr hw)
  have s' : GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := hk ▸ s
  exact ⟨hw1,I,i,S,s'.toSelected (one_dvd _)⟩

/-- At field four the zero branch forces an actual outer involution and a
returning whole conjugate with a rank-four inner actor and rank-five kernel. -/
theorem sourceOrbit_hermitian_field_four_zero_configuration
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    globalR D.sourceOrbit = 3 ∧ globalS D.sourceOrbit = 3 ∧ localM D.sourceOrbit = 3 ∧
      (∃ a : Automizer D.sourceOrbit, orderOf a = 2 ∧
        coordinateHom (automizerRepresentation D.sourceOrbit) 1
          (D.hermitianOrbitCoordinates 1 d) a ∉ binaryImage 1 ∧
        fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) = 3) ∧
      ∃ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T ∧
        IsWOffenderAt D.sourceOrbit T g ∧
        rank (inducedAutomizer D.sourceOrbit (D.sourceOrbit.map (MulAut.conj g).toMonoidHom)) = 4 ∧
        (inducedAutomizer D.sourceOrbit (D.sourceOrbit.map (MulAut.conj g).toMonoidHom)).map
          (coordinateHom (automizerRepresentation D.sourceOrbit) 1
            (D.hermitianOrbitCoordinates 1 d)) ≤ binaryImage 1 ∧
        rank (D.sourceOrbit.map (MulAut.conj g).toMonoidHom ⊓
          centralizer (D.sourceOrbit : Set G)) = 5 := by
  obtain ⟨hr,_,_,_,_⟩ := D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨hr3,hs3,g,hg,hOff,ha,hi,hker⟩ := field_four_zero_weak_closure
    D.sourceOrbit (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw
  have hjc : (binaryNormalizer 1).subtype.comp j =
      coordinateHom (automizerRepresentation D.sourceOrbit) 1
        (D.hermitianOrbitCoordinates 1 d) := by
    apply MonoidHom.ext
    intro a
    apply LinearEquiv.ext
    intro v
    rw [coordinateHom_apply,he,LinearEquiv.apply_symm_apply]
    rfl
  rw [hjc] at hi
  obtain ⟨hm3,a,ha2,hao,hac⟩ := D.sourceOrbit_hermitian_outer_involution_of_small_globalR
    1 d h hmany hV hnon (by rw [hr3]; decide)
  exact ⟨hr3,hs3,hm3,⟨a,ha2,hao,hac⟩,g,hg,hOff,ha,hi,hker⟩

/-- The original tensor has exactly the remaining field-four alternatives:
a zero-closure configuration with r = m = 3, or parameter-one selections
inside every actual H-star subgroup. All witnesses retain the original action. -/
theorem sourceOrbit_hermitian_tensor_field_four_closure_cases
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
    n = 1 ∧ B.degree = 2 ∧
      ((globalW D.sourceOrbit T = 0 ∧ globalR D.sourceOrbit = 3 ∧
        globalS D.sourceOrbit = 3 ∧ localM D.sourceOrbit = 3 ∧
        (∃ a : Automizer D.sourceOrbit, orderOf a = 2 ∧
          fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a) = 3) ∧
        ∃ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T ∧
          IsWOffenderAt D.sourceOrbit T g ∧
          rank (inducedAutomizer D.sourceOrbit
            (D.sourceOrbit.map (MulAut.conj g).toMonoidHom)) = 4 ∧
          rank (D.sourceOrbit.map (MulAut.conj g).toMonoidHom ⊓
            centralizer (D.sourceOrbit : Set G)) = 5) ∨
      (globalW D.sourceOrbit T = 1 ∧
        ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
          ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
            Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)) := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  by_cases hw : globalW D.sourceOrbit T = 0
  · obtain ⟨hr,hs',hm,⟨a,ha,_,hac⟩,g,hg,hOff,har,_,hker⟩ :=
      D.sourceOrbit_hermitian_field_four_zero_configuration h hmany hV hnon d hw
    exact Or.inl ⟨hw,hr,hs',hm,⟨a,ha,hac⟩,g,hg,hOff,har,hker⟩
  · have hpos : 0 < globalW D.sourceOrbit T := pos_iff_ne_zero.mpr hw
    have hall : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        globalW D.sourceOrbit T = 1 ∧
        ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
          Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := by
      intro H hH
      exact D.sourceOrbit_hermitian_tensor_selected_of_positive h hmany hV hs hnon
        B C eQ 1 hdegree hfield hmodel hpos hH
    have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
      refine ⟨B,C,⟨eQ⟩,?_⟩
      dsimp only
      rw [hdegree]
      exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
    obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
    exact Or.inr ⟨(hall H hH).1,fun H hH => (hall H hH).2⟩

/-- The source lower bound r >= 4 suffices for field-four selection on the
original tensor, with all local selection and numerical premises discharged. -/
theorem sourceOrbit_hermitian_tensor_selected_of_four_le_globalR
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
    (hr : 4 ≤ globalR D.sourceOrbit) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
          Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := by
  obtain ⟨hn,hB,hcases⟩ := D.sourceOrbit_hermitian_tensor_field_four_closure_cases
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  rcases hcases with hz | hp
  · rw [hz.2.1] at hr
    norm_num at hr
  · exact hp

/-- Unconditional parameter bounds on the original tensor. The weak-closure
upper bound is now one also at field four, without a generation parameter. -/
theorem sourceOrbit_hermitian_tensor_small_parameters
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
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T ≤ 1 ∧
      3 ≤ globalR D.sourceOrbit ∧ globalR D.sourceOrbit ≤ 5 := by
  obtain ⟨hn,hB,hcases⟩ := D.sourceOrbit_hermitian_tensor_field_four_closure_cases
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  have hw : globalW D.sourceOrbit T ≤ 1 := by
    rcases hcases with hz | hp
    · rw [hz.1]
      exact zero_le
    · exact hp.1.le
  refine ⟨hn,hB,hw,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  obtain ⟨j,hj,_,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  have hq : primeRank 2 (Automizer D.sourceOrbit) ≤ 4 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 j hj).trans
      (OuterRank.normalizer_twoRank_le 1 (normalizerCoverage 1)
        ⟨FieldSections.centralizerEquiv 1⟩)
  have hfw := lemma_E_3_29 D.sourceOrbit_weakClosure_setup
    (Or.inr (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon))
  have hq' : (primeRank 2 (Automizer D.sourceOrbit) : ℕ∞) ≤ 4 := by exact_mod_cast hq
  exact ⟨hr,hfw.trans (add_le_add hq' hw)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
