module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeBlockCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeJoinAction
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeCentralizerMarking
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointClosure
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointCrossing
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointExclusion
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Point-centralizer exclusion for the selected M22-code pair

The supplied pair and its full code marking identify the point closure with
the ambient centralizer two-core. Its literal residual image has two-core
order 32 and full alternating-six quotient, contradicting the local carrier
exclusion. The 8.2.9 normalization is the remaining explicit source input.
Source: Aschbacher--Smith 8.2.10--13, printed pp.721--723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

theorem sourceOrbit_m22_code_selected_exclusion
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hA : offenderNormalizer D.sourceOrbit i.val⁻¹ =
      D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2)
    (hAT : offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T)
    (hfix : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) =
      D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hker : D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) =
      offenderNormalizer D.sourceOrbit i.val⁻¹ ⊓ centralizer (D.sourceOrbit : Set G))
    (hcent : I ≤ centralizer ((D.sourceOrbit ⊓ centralizer
      (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) : Subgroup G) : Set G))
    (hfour : rank (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) = 4)
    (hfive : rank (inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)) = 5)
    (hcomm : let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
      ⁅localResidual L U,centralizer (U : Set G)⁆ ≤ (localResidual L U).pCoreIn 2)
    (hRP : localResidual L (D.sourceOrbit ⊓ centralizer
      (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) ≤ normalizer (I.pCoreIn 2 : Set G))
    (hTVA : (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
      offenderNormalizer D.sourceOrbit i.val⁻¹ : Subgroup G) : Set G)) : False := by
  obtain ⟨hcommJ,hcommL,hcomponentker,hcore⟩ :=
    D.sourceOrbit_m22_code_selected_block_core h hmany hV hnon d s hA hAT hfix hker hcent
      hfour hfive hcomm hRP hTVA
  obtain ⟨f,hfk,hsection,hfull,p,q,F,hp,hqsur,hqker,hF,hpA,hq,hval⟩ :=
    D.sourceOrbit_m22_code_five_section_full h.toHypothesis1221 d s hA hAT hfix hfour hfive
  have hqkerV : q.ker = D.sourceOrbit.subgroupOf L := by
    rw [hqker,hcomponentker,hcore]
    exact (comap_map_eq_self_of_injective L.subtype_injective _).symm
  have hFL (l : L) (v : Additive D.sourceOrbit) :
      F (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) v) =
      m22CodeRepresentation (q l) (F v) := by
    rw [hF,←hq]
    exact m22OuterCodeRepresentation_restrict (q l) (F v)
  have hAN : D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ≤
      normalizer (D.sourceOrbit : Set G) :=
    hA ▸ hAT.trans D.sourceOrbit_weakClosure_setup.normalizes
  have hfix' := hfix
  have hpA' := hpA
  have hfour' := hfour
  rw [hA] at hfix' hpA' hfour'
  obtain ⟨hU,hB⟩ := selected_m22_code_section_coordinates s F p hF hAN hfix' hpA' hfour'
  have hB' (v : Additive D.sourceOrbit) : (v.toMul : G) ∈ D.sourceOrbit ⊓ I.pCoreIn 2 ↔
      F v ∈ MathieuCode.Hexad.ChiefFlag.quintetHyperplane := by
    rw [←MathieuCode.NormalizedShadowRows.M22CodePointCrossing.quintet_hyperplane_eq]
    exact hB v
  obtain ⟨z,hzne,hzo,hTC,hHC,_⟩ :=
    D.sourceOrbit_m22_code_exists_centralizer_component h.toHypothesis1221 hnon d hH
  have hzT : (z : G) ∈ centralizer (T : Set G) :=
    fun t ht => mem_centralizer_singleton_iff.mp (hTC ht)
  have hzU : (z : G) ∈ D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) := by
    refine ⟨z.property,?_⟩
    intro a ha
    exact mem_centralizer_singleton_iff.mp
      (hHC (s.family.le_ambient (pCoreIn_le 2 I ha.2)))
  obtain ⟨B,hBmem,hzB,c,hcsur,hcval,hck,hcpre,hce⟩ :=
    m22_marking_centralizer_cover L D.sourceOrbit D.sourceOrbit_component_normalizes
      q hqsur hqkerV F hFL T D.sylow_normalizes_component z hzT hzne
  have hcp : IsPGroup 2 c.ker :=
    hck ▸ (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).comap_subtype
  let j := inclusion (Chapter8.Section02.Centralizer.localResidual_le L (z : G))
  let cR := c.comp j
  obtain ⟨hcR,hcRker⟩ := m22_point_full_residual_cover L z hBmem c hcsur hcp
  have hRC := (m22_point_full_centralizer L D.sourceOrbit z
    (hV ▸ D.le_component) D.sourceOrbit_component_normalizes hBmem F c hcsur hck hzB hce).1
  have hceR : ∀ r v, F (automizerRepresentation D.sourceOrbit
      (D.sourceOrbit.normalizerMonoidHom.rangeRestrict (inclusion
        (((Chapter8.Section02.Centralizer.localResidual_le L z).trans inf_le_left).trans
          D.sourceOrbit_component_normalizes) r)) v) =
        m22CodeRepresentation (cR r).val (F v) := fun r v => hce (j r) v
  have hout := selected_m22_point_closure_crossing s D.sourceOrbit_weakClosure_setup L
    ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Subgroup G) z D.sourceOrbit_component_normalizes
    (hV ▸ D.le_core) (hV ▸ D.core_centralizes) hfix' hzU hBmem F cR hcR hcRker hzB
    hceR hU hB'
  have hlocal := D.sourceOrbit_m22_code_point_local_core h.toHypothesis1221 d
    hcomponentker z hzT hzne hRC
  have hpointker := m22_marking_point_kernel L D.sourceOrbit D.sourceOrbit_component_normalizes
    q hqkerV F hFL (z : G)
  have hchar : centralizer (pCore 2 (centralizer ({(z : G)} : Set G)) :
      Set (centralizer ({(z : G)} : Set G))) ≤ pCore 2 (centralizer ({(z : G)} : Set G)) :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) (isTwoLocal_involution_centralizer hzo) hTC)
  obtain ⟨_,_,_,_,_,himagecore,himagequot⟩ := m22_point_closure_core L D.sourceOrbit T z hchar
    (hV ▸ D.le_component) D.sourceOrbit_component_normalizes D.sylow_normalizes_component
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.le_sylow
    hTC hzo (hV ▸ D.le_core) (hV ▸ D.core_centralizes)
    (D.sourceOrbit_elementary_join_core_of_core_commutator h hmany hV hnon hcommJ)
    hcommJ.le (D.sourceOrbit_nonFF_sylow_centralizer h hmany hV hnon).1
    hBmem F c hcsur hck hzB hce hpointker hlocal hout
  let Cz := centralizer ({(z : G)} : Set G)
  have hC : IsSQTK KnownSimple.IsKnownSimple Cz := h.simpleQTKE.involution_centralizer_sqtk hzo
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Cz ⧸ pCore 2 Cz) := by
    refine ⟨?_,hC.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hC.stronglyQuasithin p hp ho)
  exact m22_point_quotient_exclusion L T z hQ D.sylow_normalizes_component hTC
    (D.sourceOrbit_m22_code_centralizer_component h.toHypothesis1221 d z hzT hzne).1
    himagecore himagequot

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
