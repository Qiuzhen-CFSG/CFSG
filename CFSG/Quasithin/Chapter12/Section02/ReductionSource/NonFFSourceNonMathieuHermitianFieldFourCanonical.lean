module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourClosure
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCanonical

/-!
# A common normalizer on the original field-four chosen orbit

Uniqueness of the saturated plane actor makes the rank-four fixed subgroup
independent of every parameter-one selection. Positive weak closure supplies
such a selection in each original H-star subgroup, so all those subgroups
normalize the same U and their two-residuals centralize U. Each selected pair
still identifies U with the literal intersection of the two original conjugates.

In the zero branch the canonical subgroup is C_V(W₀(T,V)); every moving whole
conjugate in the original Sylow has that fixed subgroup. Tensor descent and
the checked higher-field exclusion give both alternatives directly from the
original tensor input, retaining half-degree one, the automizer and T.

This supplies a common subgroup for the normalizer analysis. It does not
exclude zero closure or complete the normalizer/centralizer argument through
8.2.13; these remain obligations of this task.
Source: Aschbacher--Smith E.3.13, H.4.4--5 and 8.2.5, printed pp.233,
381--382,716--717, refs/quasithin.pdf (1 March 2004 manuscript).
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
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Zero closure gives the canonical rank-four fixed subgroup of the literal
zeroth weak closure, with the original Sylow and every moving conjugate. -/
theorem sourceOrbit_hermitian_zero_closure_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
    rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ∀ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T →
        ¬ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (D.sourceOrbit : Set G) →
          D.sourceOrbit ⊓ centralizer (D.sourceOrbit.map (MulAut.conj g).toMonoidHom : Set G) = U := by
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  exact field_four_zero_closure_fixed D.sourceOrbit (D.hermitianOrbitCoordinates 1 d)
    j hj he T D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw

/-- Positive weak closure puts every original H-star subgroup in one common
normalizer and its two-residual in the centralizer of the same rank-four U.
Each actual parameter-one pair has U as its original central intersection. -/
theorem sourceOrbit_hermitian_tensor_common_normalizer
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
    (hw : 0 < globalW D.sourceOrbit T) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ U : Subgroup G, U ≤ D.sourceOrbit ∧ rank U = 4 ∧
        (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
          H ≤ normalizer (U : Set G) ∧
          (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
          ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
            Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
            U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
  obtain ⟨H₀,hH₀,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨hw1,I₀,i₀,S₀,s₀⟩ := D.sourceOrbit_hermitian_tensor_selected_of_positive
    h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel hw hH₀
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  let e := D.hermitianOrbitCoordinates 1 d
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i₀.val⁻¹).toMonoidHom ⊓ I₀.pCoreIn 2 : Set G)
  obtain ⟨_,_,_,hu,_,_,hTN,_⟩ := selected_one_fixed_subgroup s₀
    D.sourceOrbit_weakClosure_setup 1 e j hj he
  refine ⟨hw1,U,inf_le_left,hu,hTN,?_⟩
  intro H hH
  obtain ⟨_,I,i,S,s⟩ := D.sourceOrbit_hermitian_tensor_selected_of_positive
    h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel hw hH
  have hsame := selected_one_fixed_subgroup_eq D.sourceOrbit e j hj he s₀ s
    D.sourceOrbit_weakClosure_setup
  have hnorm := selected_one_hstar_normalizer s hH D.sourceOrbit_weakClosure_setup 1 e j hj he
  obtain ⟨_,_,_,_,hint,_⟩ := selected_one_fixed_subgroup s D.sourceOrbit_weakClosure_setup 1 e j hj he
  change U = _ at hsame
  refine ⟨?_,?_,I,i,S,s,hsame.trans hint⟩
  · rw [hsame]
    exact hnorm.1
  · rw [hsame]
    exact hnorm.2


/-- The original tensor has a canonical rank-four subgroup in either remaining
weak-closure branch. Positive closure gives one common normalizer for all H-star
subgroups; zero closure identifies the fixed subgroup of the literal W₀. -/
theorem sourceOrbit_hermitian_tensor_canonical_cases
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
      ((globalW D.sourceOrbit T = 0 ∧
        let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
        rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G)) ∨
      (globalW D.sourceOrbit T = 1 ∧
        ∃ U : Subgroup G, U ≤ D.sourceOrbit ∧ rank U = 4 ∧
          (T : Subgroup G) ≤ normalizer (U : Set G) ∧
          ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
            H ≤ normalizer (U : Set G) ∧
            (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
            ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
              Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
              U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)) := by
  by_cases hw : globalW D.sourceOrbit T = 0
  · obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
    refine ⟨hn,hB,Or.inl ⟨hw,?_⟩⟩
    subst hn
    obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
      hs B C 1 hdegree hfield hmodel
    obtain ⟨hr,hN,_⟩ := D.sourceOrbit_hermitian_zero_closure_fixed h hmany hV hnon d hw
    exact ⟨hr,hN⟩
  · obtain ⟨hn,hB,hw1,hU⟩ := D.sourceOrbit_hermitian_tensor_common_normalizer
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel (pos_iff_ne_zero.mpr hw)
    exact ⟨hn,hB,Or.inr ⟨hw1,hU⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
