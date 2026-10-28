module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSolvableSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourMovement

/-!
# Solvable H-star groups on the actual Hermitian tensor

Every solvable original H-star subgroup now supplies its own E.2.9 family
and selected parameter-one pair. No family-existence, positive-weak-closure,
E.2.14 or separate action premise is needed. The original half-field tensor
then gives field four, the rank-four actor and fixed subgroup, its relative
normality, H-normalization and exact residual movement in the selected core.

In particular the higher-field branch has no solvable H-star subgroup.
The nonsolvable selection branch and the field-four normalizer/centralizer
argument through 8.2.13 remain unfinished.
Source: Aschbacher–Smith E.2.9, 8.2.2–5 and the opening of 8.2.7,
printed pp.221–222,714–718 (1 March 2004 manuscript, refs/quasithin.pdf).
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

/-- The original solvable H-star subgroup supplies an actual selected pair;
no family witness or weak-closure positivity is assumed. -/
theorem sourceOrbit_hermitian_selected_of_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsol : Group.IsSolvable H) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  exact exists_selected_of_solvable h28 hsol
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar)
    (D.sourceOrbit_restricted_quadraticRatio_gt_one h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)

/-- Solvable selection on the literal tensor, with the original actor,
intersection, Sylow and residuals retained through the field-four reduction. -/
theorem sourceOrbit_hermitian_tensor_solvable_hstar
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsol : Group.IsSolvable H)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      n = 1 ∧ B.degree = 2 ∧ A ≤ T ∧
      rank (inducedAutomizer D.sourceOrbit A) = 4 ∧ rank U = 4 ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧ H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U ∧
      I.pCoreIn 2 ⊓ centralizer ((pResidual 2 I).map I.subtype : Set G) = U := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨I,i,S,s⟩ := D.sourceOrbit_hermitian_selected_of_solvable h hmany hV hnon hs hrow hH hsol
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h.toHypothesis1221
  obtain ⟨hn,hAT,ha,hu,hU,hUT,hTN,hIC,_,_⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
  have hnorm := selected_one_hstar_normalizer s hH
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
  have hmove := D.sourceOrbit_hermitian_selected_one_residual_core h.toHypothesis1221 s n d
  exact ⟨I,i,S,s,hn,by omega,hAT,ha,hu,hU,hUT,hTN,hIC,
    selected_generates_hstar s hH,hnorm.1,hnorm.2,hmove⟩

/-- Every original H-star group in the higher-field tensor branch is
nonsolvable. The solvable family witness is constructed in the proof. -/
theorem sourceOrbit_hermitian_tensor_hstar_not_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hn : 1 < n) : ¬ Group.IsSolvable H := by
  intro hsol
  obtain ⟨I,i,S,s,hn',_⟩ := D.sourceOrbit_hermitian_tensor_solvable_hstar
    h hmany hV hs hnon hH hsol B C eQ n hdegree hfield hmodel
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
