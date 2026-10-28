module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeTensor
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CoreImage

/-!
# The order-two image of the original M24 code

The already constructed central cubic acts fixed-point-freely on the
same selected pair's literal P/U. Its full commutator lies in O₂(L_U),
so P lies in O₂(L_U)U and hence in O₂(H). The selected degree-one
quotient then identifies the original V ∩ O₂(H) and its order-two image
in H/O₂(H). The original pair, four-space and intrinsic kernels remain
unchanged; no containment or fixed-space estimate is assumed.

Source: Aschbacher--Smith 8.2.8(5), 8.2.9(3), printed pp.719--720,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open MathieuCode.SextetLayers.CoordinateTransport
open Chapter7.NormalizedSource.MathieuShadowRows
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original code image has order two, with its selected pair and
full two-core containment constructed from the original hypotheses. -/
theorem sourceOrbit_m24_code_parabolic_image_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      rank U = 4 ∧ H ≤ normalizer (U : Set G) ∧
      I.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      D.sourceOrbit ⊓ I.pCoreIn 2 = D.sourceOrbit ⊓ H.pCoreIn 2 ∧
      Nat.card ((D.sourceOrbit.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hu,hUT,hTU,hmodel,hcomm,hRI,hRP,
    hgen,hHN,hres,hresR,hcore,h3,h5,hn,hcenter,hjoin,hmeet,hBA,hUU,hIK,hsec,
    hp,hnat,hm,hD,hquint,hcubic,hrest⟩ :=
    D.sourceOrbit_m24_code_tensor_pair_of_many h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  let P := I.pCoreIn 2
  obtain ⟨hYP,hYU,hUP,eR,z,hz,hzmark,hzc,hfree,_⟩ := hcubic
  let := hUP
  have hspan : P ≤ ⁅P,R⁆ ⊔ U :=
    section_le_commutator_sup_of_fixedFree (R ⊔ I) P U R hYP hYU
      (inclusion le_sup_left z) z.property hfree
  have hPR : ⁅P,R⁆ ≤ R.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl ((pCoreIn_le 2 I).trans hIC)).trans hcomm
  have hPH : P ≤ H.pCoreIn 2 :=
    hspan.trans ((sup_le_sup_right hPR U).trans hcore)
  exact ⟨I,i,S,s,hu,hHN,hPH,selected_one_image_two_of_core_le s hPH⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
