module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightMarkedEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCenter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Double.Geometry
public import Theory.GroupTheory.PResidual.CentralizerCorrection
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Original Sylow action and replacement movement at distance eight

A Sylow-central element lies in the original two-core. Its displacement by
the two-perfect component lies in [Z(Q),L]. Odd-index averaging corrects it
inside this natural summand, retaining the actual component Sylow fixed line.
A matrix fixing that line moves the common-axis replacement image. Its lift
therefore centralizes the original Sylow centralizer and moves the replacement.

This proves the action needed for C.1.34(4)'s original radical inequality,
without a whole-fixed-factor or original fixed-factor centrality premise.
The literal SmallMSPair application is in LinearThree.DistanceEightOriginalAction.
Source: MS93 (4.4), p.890 and the final Main Theorem remark, p.831;
Aschbacher--Smith C.1.34(4), pp.136--137.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
local notation "msCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L R : Subgroup J} {h : Input κ L R}

private theorem component_sylow_image (P : Sylow 2 J) (β : SL ≃* SL) :
    ((P : Subgroup J) ⊓ L).map (β.toMonoidHom.comp h.coreProjection) =
      (P : Subgroup J).map (β.toMonoidHom.comp h.coreProjection) := by
  let a := β.toMonoidHom.comp h.coreProjection
  apply le_antisymm (map_mono inf_le_left)
  rintro _ ⟨s,hs,rfl⟩
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L)
    (h.quotientEquiv.symm (h.coreProjection s))
  have hal : a l = a s := by
    change β (h.coreProjection l) = β (h.coreProjection s)
    rw [h.coreProjection_component l,hl,MulEquiv.apply_symm_apply]
  have hc : (l : J) * s⁻¹ ∈ pCore 2 J := by
    rw [← h.coreProjection_kernel]
    change h.coreProjection ((l : J) * s⁻¹) = 1
    rw [map_mul,map_inv,h.coreProjection_component l,hl,MulEquiv.apply_symm_apply,mul_inv_cancel]
  have hlP : (l : J) ∈ (P : Subgroup J) := by
    have hh := (P : Subgroup J).mul_mem ((pCore_isPGroup.le_sylow_of_normal P) hc) hs
    simpa only [inv_mul_cancel_right] using hh
  exact ⟨l,⟨hlP,l.property⟩,hal⟩

/-- A Sylow in the original group and the replacement image use one frame. -/
theorem distance_eight_marked_sylow (t : InputSetup h)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (P : Sylow 2 J) (hRP : R ≤ (P : Subgroup J)) :
    ∃ g : SL,
      ((P : Subgroup J) ⊓ L).map
        (common.natural.marking.toMonoidHom.comp h.coreProjection) =
          Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom ∧
      t.reduction.ambient.map
        (common.natural.marking.toMonoidHom.comp h.coreProjection) =
          BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom := by
  let a := common.natural.marking.toMonoidHom.comp h.coreProjection
  let Q : Sylow 2 SL := P.mapSurjective (f := a)
    (common.natural.marking.surjective.comp h.coreProjection_surjective)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL Matrix.PSL3Two.SourceFlag.flagSylow Q
  have hPg : (P : Subgroup J).map a =
      Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom := by
    change (Q : Subgroup SL) = _
    rw [← hg,Sylow.coe_subgroup_smul]
    rfl
  have he : t.reduction.radical.map
      (common.natural.marking.toMonoidHom.comp t.source.projection) =
        t.reduction.ambient.map a := by
    have ha : common.natural.marking.toMonoidHom.comp t.source.projection =
        a.comp t.reduction.overgroup.subtype := by
      apply MonoidHom.ext
      intro x
      exact congrArg common.natural.marking (DFunLike.congr_fun t.projection_eq x)
    rw [ha]
    rw [← map_map,map_subgroupOf_eq_of_le (show t.reduction.ambient ≤ t.reduction.overgroup from le_sup_right)]
  refine ⟨g,(component_sylow_image P common.natural.marking).trans hPg,?_⟩
  apply (BinaryLinearThree.DoubledOffenders.offender_borel_conjugate_iff g _ ?_).mp
  · exact he ▸ DistanceEight.marked_edge_offender common
      (DistanceEight.PathCentrality.Source44.OriginalEarlier.earlier common hb)
  · rw [← hPg]
    exact map_mono ((map_subtype_le _).trans hRP)

private theorem natural_point_fixer_moving_axis (g : SL) :
    ∃ c : SL,
      (∀ v ∈ fixedSpace BinaryLinearThree.W
        (Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom),
        BinaryLinearThree.W c v = v) ∧
      c ∉ normalizer (BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom : Set SL) := by
  obtain ⟨c,hfix,hmove⟩ := BinaryLinearThree.DoubledOffenders.exists_point_fixer_moving_axis g
  refine ⟨c,?_,?_⟩
  · intro v hv
    have hpair : (v,0) ∈ fixedSpace BinaryLinearThree.DoubledOffenders.τ
        ((Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom).map
          BinaryLinearThree.DoubledOffenders.δ) := by
      rw [← fixedSpace_comp_map]
      intro a
      apply Prod.ext (hv a)
      change BinaryLinearThree.W a.val 0 = 0
      exact map_zero _
    exact congrArg Prod.fst (hfix (v,0) hpair)
  · intro hc
    exact hmove ((BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom).le_normalizer_map
      BinaryLinearThree.DoubledOffenders.δ
      (mem_map_of_mem BinaryLinearThree.DoubledOffenders.δ hc))

/-- A component element fixes the original Sylow centralizer and moves the
literal characteristic replacement. No fixed-factor equality is required. -/
theorem distance_eight_replacement_movement (t : InputSetup h)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : 4 < t.geometry.b t.reduction.radical)
    (P : Sylow 2 J) (hRP : R ≤ (P : Subgroup J)) :
    ¬ L ⊓ centralizer (centralizer (P : Set J) : Set J) ≤
      normalizer (t.reduction.ambient : Set J) := by
  let := h.component_normal
  let a := common.natural.marking.toMonoidHom.comp h.coreProjection
  let e := h.quotientEquiv.trans common.natural.marking
  obtain ⟨g,hPg,hRg⟩ := t.distance_eight_marked_sylow common hb P hRP
  obtain ⟨c,hfix,hmove⟩ := natural_point_fixer_moving_axis g
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm c)
  have hlc : a l = c := by
    change common.natural.marking (h.coreProjection l) = c
    rw [h.coreProjection_component l]
    change e (QuotientGroup.mk' _ l) = c
    rw [hl,e.apply_symm_apply]
  have ha (l : L) : linearThreeActor e l = a l := by
    change common.natural.marking (h.quotientEquiv (QuotientGroup.mk' _ l)) = _
    rw [← h.coreProjection_component]
    rfl
  obtain ⟨heZ,hsplit,_,hU⟩ := t.center_source_sections common hb
  let U := ⁅msCenter (msQ L R),L⁆
  have hUZ : U ≤ msCenter (msQ L R) := hsplit.symm ▸ le_sup_right
  let := heZ
  let heU : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.of_injective (inclusion hUZ) (inclusion_injective hUZ)
  obtain ⟨_,hnorm,_,hn,f,hf⟩ := hU
  let := hn
  let q : U ≃* Multiplicative BinaryLinearThree.Vector :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf U).symm).trans f)
  have hq (x : U) : q x = f (QuotientGroup.mk' _ x) := rfl
  have hlfix : (l : J) ∈ centralizer
      (U ⊓ centralizer ((P : Subgroup J) ⊓ L : Set J) : Set J) := by
    intro x hx
    let xU : U := ⟨x,hx.1⟩
    have hfixed : (q xU).toAdd ∈ fixedSpace BinaryLinearThree.W
        (Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom) := by
      rw [← hPg]
      rintro ⟨_,s,hs,rfl⟩
      have hh := hf ⟨s,hs.2⟩ xU xU (by
        change x = s * x * s⁻¹
        rw [hx.2 s hs,mul_inv_cancel_right])
      rw [ha] at hh
      exact hh.symm
    let y : U := ⟨(l : J) * x * (l : J)⁻¹,
      (mem_normalizer_iff.mp (hnorm l.property) x).mp hx.1⟩
    have hy : y = xU := q.injective (Multiplicative.toAdd.injective (by
      rw [hq, hf l xU y rfl, ha, hlc]
      exact hfix _ hfixed))
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hy)).symm
  have hQ : msQ L R = commutatorCore L := by
    rw [msQ,h.sup_eq_top]
    rw [show (⊤ : Subgroup J).pCoreIn 2 = pCore 2 J from pCore_map_iso 2 topEquiv]
  have hp : IsPPerfect 2 L := by rw [← h.residual_eq]; exact isPPerfect_pResidual 2
  obtain ⟨P₀,hP₀⟩ := P.exists_subgroupOf_eq_of_normal L
  have hPimage : (P₀ : Subgroup L).map L.subtype = (P : Subgroup J) ⊓ L := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨?_,x.property⟩
      change x ∈ (P : Subgroup J).subgroupOf L
      rwa [← hP₀]
    · rintro x ⟨hxP,hxL⟩
      refine ⟨⟨x,hxL⟩,?_,rfl⟩
      rw [hP₀]
      exact hxP
  have hlC : (l : J) ∈ centralizer (centralizer (P : Set J) : Set J) := by
    intro z hz
    have hzE : z ∈ pCore 2 J := h.core_selfCentralizing
      (centralizer_le (pCore_isPGroup.le_sylow_of_normal P) hz)
    have hzQ : z ∈ centralizer (commutatorCore L : Set J) :=
      centralizer_le ((commutator_le_left _ _).trans (pCore_isPGroup.le_sylow_of_normal P)) hz
    obtain ⟨u,hu,huc⟩ := fixed_correction_of_center_commutator L (pCore 2 J) U
      hp pCore_isPGroup le_normalizer_of_normal hnorm
      (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu)
      (by change ⁅msCenter (commutatorCore L),L⁆ ≤ U; rw [← hQ])
      P₀ z hzE hzQ (centralizer_le (hPimage.le.trans inf_le_left) hz)
    rw [hPimage] at hu
    have he : u * (u⁻¹ * z) = z := mul_inv_cancel_left u z
    calc
      z * l = (u * (u⁻¹ * z)) * l := by rw [he]
      _ = u * ((u⁻¹ * z) * l) := mul_assoc _ _ _
      _ = u * (l * (u⁻¹ * z)) := by rw [(huc l l.property).symm]
      _ = (u * l) * (u⁻¹ * z) := (mul_assoc _ _ _).symm
      _ = (l * u) * (u⁻¹ * z) := by rw [hlfix u hu]
      _ = l * z := by rw [mul_assoc,he]
  intro hn
  have hm := t.reduction.ambient.le_normalizer_map a
    (mem_map_of_mem a (hn ⟨l.property,hlC⟩))
  rw [hRg,hlc] at hm
  exact hmove hm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
