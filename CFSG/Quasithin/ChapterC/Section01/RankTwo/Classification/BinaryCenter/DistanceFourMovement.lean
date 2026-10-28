module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.ExactDistanceFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceFourMarkedEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Double.Geometry

/-!
# Movement of the literal distance-four characteristic replacement

The component intersection of an original Sylow has the same matrix image
as that whole Sylow. The genuine edge offender is its common-axis four-group,
with the same conjugator marking both subgroups. A matrix fixing the natural
Sylow-fixed line moves this four-group. Its component lift fixes the original
Sylow-fixed core center, but cannot normalize the characteristic replacement.

The consumer LinearThree.DistanceFourComplete combines this movement with
Sylow-fixed central correction to prove the complete C.1.34(3) alternative
on the original small MS pair. Every edge-action premise is discharged here.
The remaining distance-eight branch and full classification stay with
qt-rank-two-ms93.

Source: Meierfrankenfeld--Stellmacher (1993), final remark on cases (11)--(13),
p.831, and (4.6.5)--(4.6.6), p.903; Aschbacher--Smith C.1.34(3), pp.136--137.
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
theorem distance_four_marked_sylow (t : InputSetup h)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
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
  · exact he ▸ DistanceFour.marked_edge_offender common
      (DistanceFour.earlyFacts t.source t.geometry common hb)
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

/-- An element fixing the original Sylow-fixed natural center moves the
literal characteristic replacement. The edge action is supplied in its
original marking, not by an independently chosen quotient isomorphism. -/
theorem distance_four_replacement_movement (t : InputSetup h)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (hb : t.geometry.b t.reduction.radical = 4)
    (P : Sylow 2 J) (hRP : R ≤ (P : Subgroup J)) :
    ¬ L ⊓ centralizer (msCenter (msQ L R) ⊓ centralizer (P : Set J) : Set J) ≤
      normalizer (t.reduction.ambient : Set J) := by
  let a := common.natural.marking.toMonoidHom.comp h.coreProjection
  let e := h.quotientEquiv.trans common.natural.marking
  obtain ⟨g,hPg,hRg⟩ := t.distance_four_marked_sylow common hb P hRP
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
  obtain ⟨hZ,_⟩ := t.sectionModels_of_distance_four common hb
  obtain ⟨_,hnorm,_,hn,f,hf⟩ := hZ
  let := hn
  let Z := msCenter (msQ L R)
  let q : Z ≃* Multiplicative BinaryLinearThree.Vector :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf Z).symm).trans f)
  have hq (x : Z) : q x = f (QuotientGroup.mk' _ x) := rfl
  have hlfix : (l : J) ∈ centralizer (Z ⊓ centralizer (P : Set J) : Set J) := by
    intro x hx
    let xZ : Z := ⟨x,hx.1⟩
    have hfixed : (q xZ).toAdd ∈ fixedSpace BinaryLinearThree.W
        (Matrix.PSL3Two.borelSL.map (MulAut.conj g).toMonoidHom) := by
      rw [← hPg]
      rintro ⟨_,s,hs,rfl⟩
      have hh := hf ⟨s,hs.2⟩ xZ xZ (by
        change x = s * x * s⁻¹
        rw [hx.2 s hs.1,mul_inv_cancel_right])
      rw [ha] at hh
      exact hh.symm
    let y : Z := ⟨(l : J) * x * (l : J)⁻¹,
      (mem_normalizer_iff.mp (hnorm l.property) x).mp hx.1⟩
    have hy : y = xZ := q.injective (Multiplicative.toAdd.injective (by
      rw [hq, hf l xZ y rfl, ha, hlc]
      exact hfix _ hfixed))
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hy)).symm
  intro hn
  have hm := t.reduction.ambient.le_normalizer_map a
    (mem_map_of_mem a (hn ⟨l.property,hlfix⟩))
  rw [hRg,hlc] at hm
  exact hmove hm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup