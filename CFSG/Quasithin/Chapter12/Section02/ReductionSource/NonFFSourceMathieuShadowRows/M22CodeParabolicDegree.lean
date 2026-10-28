module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodePair
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeParabolicDegree
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodePair
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair

/-!
# Case I for the original selected M22 code pair

The original full automizer, TI action and parabolic setup discharge the
degree/image argument on the supplied selected pair. The cubic pair model
and the two odd-rank bounds are precisely those supplied by the original
parabolic-image consumer. Both solvable and nonsolvable branches identify
the actual two-core intersection and give n(H)=1, retaining I and i.

Source: Aschbacher--Smith 8.2.9, printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same original selected pair satisfies case I and has generation
parameter one; no point, actor or quotient is reselected. -/
theorem sourceOrbit_m22_code_pair_core_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (h3 : primeRank 3 H ≤ 1) (h5 : primeRank 5 H ≤ 1)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    I.pCoreIn 2 = I ⊓ H.pCoreIn 2 ∧
      D.sourceOrbit ⊓ I.pCoreIn 2 = D.sourceOrbit ⊓ H.pCoreIn 2 ∧
      Nat.card ((D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 ∧
      IsEGenerated 1 H ∧ generationParameter H = 1 := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH
  have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar
  have hrank := D.sourceOrbit_m22_automizer_twoRank_le_five h hmany hV
    (D.code_component_quotient d) hnon
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  obtain ⟨a,hai,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  exact selected_m22_code_core_image s h28 hfit hH
    (D.m24_hstar_normalizes h hmany hV hnon hH)
    (D.m24_restricted_quadraticRatio h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221) hrank a hai E hE h3 h5 hpair

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
