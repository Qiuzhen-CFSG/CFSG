module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureDegreeFourParabolic
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureInnerChiefBudget
public import Theory.SpecificGroups.BinaryLinear.FourNodeCubicCore
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.NormalizedCoreBudget
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The degree-four cubic residual centralizes the original core modulo W

The actual marked cubic lifts through the original J action. The same
map sends its two-core onto the marked residual core, which uses two
cubic layers. The literal W supplies a third moved layer. The proved
original chief budget is therefore exhausted on O2(H) joined with O2(J),
forcing the whole original J to centralize O2(H)/W.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation NoncentralChiefRefinement
open NoncentralChiefRefinement.CubicComparison
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The entire original two-core is centralized modulo the unchanged W
by the actual original point residual in the degree-four branch. -/
theorem original_tripleSix_central_closure_degreeFour_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    (hW32 : Nat.card (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))=32) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    ⁅H.pCoreIn 2,J⁆≤W := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hr⟩ := original_tripleSix_central_closure_degreeFour_parabolic
    h structural D a z hz hzT hnot hinner hW32
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,e,r,hr,hformula,hker,hR,hU,b,hT,i,hJi⟩ := hr
  let := he
  let JH := J.subgroupOf H
  let WH := W.subgroupOf H
  let Q := pCore 2 H
  let LinearActor := BinaryLinear.OuterCyclic.LinearGroup 4
  let : Finite LinearActor := Finite.of_injective (fun g : LinearActor => (g : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2)))
    DFunLike.coe_injective
  let c := BinaryLinear.OrderedResidualConjugators.cubic b i.castSucc i.succ (by simp [Fin.ext_iff])
  have hcm := BinaryLinear.OrderedResidualConjugators.four_node_cubic_core_length b i
  have hcorder : orderOf c=3 := hcm.1
  have hc1 : c≠1 := by intro hh; rw [hh,orderOf_one] at hcorder; contradiction
  have hcJ : c∈JH.map r := hJi.symm ▸ hcm.2.1
  have hJH : J≤H := le_sup_right.trans le_sup_left
  let eJ := subgroupOfEquivOfLe hJH
  have hj := original_tripleSix_weightFour_cubic_residual D a z hz hzT
  have hpJ : IsPPerfect 2 JH := hj.2.2.1.of_surjective eJ.symm.toMonoidHom eJ.symm.surjective
  have hcJH : Nat.card (JH ⧸ pCore 2 JH)=3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)).toEquiv).trans hj.2.2.2.1
  let f := r.subgroupMap JH
  have hf : Function.Surjective f := r.subgroupMap_surjective JH
  have hfn : f≠1 := by
    intro hh
    obtain ⟨g,hg⟩ := hf ⟨c,hcJ⟩
    have heq : f g=1 := congrArg (fun k : JH →* JH.map r=>k g) hh
    exact hc1 (congrArg Subtype.val (hg.symm.trans heq))
  have hkf := f.kernel_isTwoGroup_of_twoPerfect_cubic hpJ hcJH hfn
  obtain ⟨g,hgodd,hgc⟩ := f.exists_pRegular_lift hf 2 Nat.prime_two ⟨c,hcJ⟩
    (by rw [←Subgroup.orderOf_coe,hcm.1]; decide)
  have hgorder : orderOf g=3 := by
    have hh := f.orderOf_map_eq_of_coprime_of_isPGroup_ker hkf g
      (Nat.prime_two.coprime_iff_not_dvd.mpr hgodd)
    rw [hgc,←Subgroup.orderOf_coe,hcm.1] at hh
    exact hh.symm
  let A : Subgroup H := zpowers (g:H)
  have hA : Nat.card A=3 := by rw [Nat.card_zpowers,Subgroup.orderOf_coe,hgorder]
  have hAJ : A≤JH := zpowers_le.mpr g.property
  have hAc : A.map r=zpowers c := by
    rw [MonoidHom.map_zpowers]
    exact congrArg zpowers (congrArg Subtype.val hgc)
  have hcfg := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hWQ : WH≤Q := by
    intro w hw
    have hh : (w:G)∈H.pCoreIn 2 := hcfg.2.2.1 hw
    obtain ⟨v,hv,heq⟩ := hh
    exact (Subtype.ext heq : v=w) ▸ hv
  have hWH : W≤H := hcfg.2.2.1.trans (pCoreIn_le 2 H)
  let : WH.Normal := normal_subgroupOf_of_le_normalizer hHW
  have hQker : Q≤r.ker := by
    intro q hq
    apply (hker q).mpr
    intro w hw
    exact hcfg.2.2.2.2.1 (commutator_mem_commutator hw ⟨q,hq,rfl⟩)
  have hQJ : Q≤normalizer (JH : Set H) := by
    have hQT := pCore_isPGroup.le_sylow_of_normal (T.subtype (show (T : Subgroup G)≤H from le_sup_right))
    exact hQT.trans ((comap_mono hj.2.1).trans (le_normalizer_comap H.subtype))
  have hmove : ⁅WH,A⁆≠⊥ := by
    intro hzcomm
    have hgker : (g:H)∈r.ker := by
      apply (hker g).mpr
      intro w hw
      have hc : ⁅(⟨w,hWH hw⟩ : H),(g:H)⁆=1 := mem_bot.mp
        (hzcomm ▸ commutator_mem_commutator (show (⟨w,hWH hw⟩ : H)∈WH from hw) (mem_zpowers _))
      have hcg : ⁅w,((g:H):G)⁆=1 := congrArg Subtype.val hc
      rw [hcg]
      exact one_mem _
    exact hc1 ((congrArg Subtype.val hgc).symm.trans hgker)
  have hcore : (JH.pCoreIn 2).map r=(JH.map r).pCoreIn 2 := by
    have hi := f.comap_pCore_of_ker_isPGroup hf hkf
    have hm : (pCore 2 JH).map f=pCore 2 (JH.map r) := by
      rw [←hi,map_comap_eq_self]
      rw [MonoidHom.range_eq_top.mpr hf]
      exact le_top
    change ((pCore 2 JH).map JH.subtype).map r=_
    rw [map_map]
    change (pCore 2 JH).map ((JH.map r).subtype.comp f)=_
    rw [←map_map,hm]
    rfl
  have houter : 2≤conjugationCubicLength (A.map r) ((Q ⊔ JH.pCoreIn 2).map r) := by
    rw [Subgroup.map_sup,(map_eq_bot_iff Q).mpr hQker,bot_sup_eq,hcore,hJi,hAc]
    exact hcm.2.2
  have hbudget (s : ChiefSeries JH) (h0 : s.head=⊥) (h1 : s.last=⊤) :
      s.noncentralTwoCount≤3 := by
    have hs := s.mapActor_complete eJ h0 h1
    have hh := original_tripleSix_central_closure_inner_chief_budget h structural D a z hz hzT hnot hinner
      (s.mapActor eJ) hs.1 hs.2
    rwa [s.mapActor_noncentralTwoCount eJ] at hh
  have hcomm := normalized_core_commutator_le_of_three_layer_budget JH Q WH A
    hpJ hcJH pCore_isPGroup hQJ hWQ hA hAJ hmove hbudget r hQker houter
  have hh := map_mono (f:=H.subtype) hcomm
  rw [map_commutator,map_subgroupOf_eq_of_le hJH,map_subgroupOf_eq_of_le hWH] at hh
  exact hh

end CFSG.Quasithin.Chapter12.Section07
