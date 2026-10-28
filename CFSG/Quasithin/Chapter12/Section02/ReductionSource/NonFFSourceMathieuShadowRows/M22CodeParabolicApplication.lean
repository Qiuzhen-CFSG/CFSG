module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeTensorApplication
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeParabolicSolvable

/-!
# The original M22-code parabolic image consumer

The same selected pair carries its cubic tensor, original quintet quotient,
parabolic image bound and odd-rank bounds. The quotient of V retains both
source alternatives until the nonsolvable order-four exclusion is proved.
Source: Aschbacher--Smith 8.2.9, printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.SmallOvergroups
open Chapter8.Section02.MathieuShadowRows MathieuCode.M22Quintet.CocodeTransfer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 600000 in
theorem sourceOrbit_m22_code_parabolic_pair
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
        Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∧
        PairCubicTensor R I D.sourceOrbit U ∧
        R.pCoreIn 2 ⊔ U ≤ H.pCoreIn 2 ∧
        Nat.card ((B.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 ∧
        ((B = D.sourceOrbit ⊓ H.pCoreIn 2 ∧
          Nat.card ((D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2) ∨
          Nat.card ((D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
        primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 := by
  have hex := @sourceOrbit_m22_code_tensor_pair G _ _ T L V D h hmany hV hnon d H hH
  rcases hex with ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,
    f,hfk,hsection,hprod,hpair,hm,hc,ht⟩
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hfour
    rw [hz,Representation.BinaryOffender.rank_bot] at hfour
    omega
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le inf_le_left,rfl⟩
  have hthin := (h.simpleQTKE.twoLocal_sqtk hlocal).stronglyQuasithin
  obtain ⟨hcore,hsmall,hcases⟩ := selected_m22_code_parabolic_image (L := L) (U := U)
    (f := f.comp (inclusion (localResidual_le L U))) s hH hfix hcent
    D.sylow_normalizes_component hTU hcomm hsection
  obtain ⟨h3,h5⟩ := selected_m22_code_parabolic_odd_ranks (L := L) (U := U)
    (f := f.comp (inclusion (localResidual_le L U))) s hH D.sylow_normalizes_component
    hcent D.sylow_normalizes_component hTU hcomm hsection hthin
  exact ⟨I,i,S,s,hA,hAT,hfix,hker,hcent,hfive,hfour,hUT,hTU,hcomm,hRI,hRP,hK,
    f,hfk,hsection,hprod,hpair,hm,hc,ht,hcore,hsmall,hcases,h3,h5⟩


/-- Solvability discharges 8.2.9 on the supplied original cubic pair. All
local setup comes from the same marked orbit; the pair is not reselected. -/
theorem sourceOrbit_m22_code_solvable_of_cubic_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hsol : Group.IsSolvable H) (h3 : primeRank 3 H ≤ 1)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2))) :
    Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∧
      (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
      (H : Set G) = (I : Set G) * (T : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
        (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G) := by
  have h28 := (D.sourceOrbit_m22_code_hstar_setup h hmany hV hnon d hH).1
  exact selected_m22_code_solvable_parabolic s h28 hH hsol
    D.sourceOrbit_weakClosure_setup.normalizes h3 hpair

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
