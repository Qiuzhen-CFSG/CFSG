module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeFiveAction
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeMultiplicity

/-!
# The original M22-code cubic quotient

The faithful binary multiplicity action reduces the odd prime-power
rotation of the selected pair to order three. This application retains
its original quintet map, exact kernel and full product action.
Source: Aschbacher--Smith 8.2.8(4), printed pp.718--719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.MathieuShadowRows MathieuCode.M22Quintet.CocodeTransfer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

theorem sourceOrbit_m22_code_cubic_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let B := D.sourceOrbit ⊓ I.pCoreIn 2
      let R := localResidual L U
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      A = D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      A ≤ T ∧ U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧ I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 5 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      (∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
        (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
        normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
        R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G)) ∧
      ∃ f : (L ⊓ normalizer (U : Set G) : Subgroup G) →* M22Quintet.Q,
        f.ker = D.orbitComponentHom.ker.comap
          (inclusion (show (L ⊓ normalizer (U : Set G) : Subgroup G) ≤ L from inf_le_left)) ∧
        M22FiveSection R B U (f.comp (inclusion (localResidual_le L U))) ∧
        M22CodePairProductAction R I D.sourceOrbit U ∧
        M22CodePairAction R I D.sourceOrbit U i (f.comp (inclusion (localResidual_le L U))) ∧
        M22CodePairMultiplicityAction R I D.sourceOrbit U i (f.comp (inclusion (localResidual_le L U))) ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) := by
  have hex := @sourceOrbit_m22_code_product_pair G _ _ T L V D h hmany hV hnon d H hH
  rcases hex with ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,
    f,hfk,hsection,hprod,hpair⟩
  have hcommI : ⁅localResidual L
      (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)),I⁆ ≤
      (localResidual L (D.sourceOrbit ⊓ centralizer
        (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G))).pCoreIn 2 :=
    (commutator_mono le_rfl hcent).trans hcomm
  obtain ⟨hm,hc⟩ := selected_m22_code_multiplicity_cubic s hprod hpair hcommI
  exact ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,
    f,hfk,hsection,hprod,hpair,hm,hc⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

