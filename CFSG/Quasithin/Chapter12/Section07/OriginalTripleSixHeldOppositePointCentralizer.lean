module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeAction
public import Theory.SpecificGroups.PSL3Four.CentralCover.FullPlanePointCentralizer
-- Reuse the proved original conjugated cover map with its whole kernel.
import all CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldOppositeAction

/-!
# The marked central point in the original opposite component parabolic

The marked z belongs to W through Z(P), but is outside the conjugated
component center since it is central in the original T. The whole opposite
component parabolic centralizer of z is therefore a two-group. It contains
the retained component Sylow R and consequently equals R. In particular it
normalizes the same P, not a newly chosen extraspecial subgroup.

This does not identify the centralizer of z in the full ambient normalizer
of W; that larger local comparison remains a separate source duty.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

theorem original_tripleSix_escaping_opposite_point_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (π : T→*DihedralGroup 4) [IsExtraspecial 2 π.ker] (hP : Nat.card π.ker=128)
    (z : G) (hz : z∈centerIn (T : Subgroup G)) (hzne : z≠1)
    (hZ : centerIn (π.ker.map (T : Subgroup G).subtype)=zpowers z) :
    let P := π.ker.map (T : Subgroup G).subtype
    let H := centralizer ({(t:G)} : Set G)
    let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
    let B := conjugateSpanBy Lt H
    ∃ k∈K, ∃ S : Sylow 2 B, ∃ W : Subgroup G,
      let Bk := B.map (MulAut.conj k).toMonoidHom
      let R := ((S : Subgroup B).map B.subtype).map (MulAut.conj k).toMonoidHom
      let L := (normalizer (W.subgroupOf Bk : Set Bk)).map Bk.subtype
      IsElementaryAbelian 2 W ∧ Nat.card W=64 ∧ U⊔W=R ∧
      U⊓W=centerIn R ∧ Nat.card (centerIn R)=16 ∧
      W≤R ∧ R≤(T : Subgroup G) ∧ R≤L ∧ Nat.card R=256 ∧
      (T : Subgroup G)≤normalizer (R : Set G)⊓normalizer (W : Set G) ∧
      L.pCoreIn 2=W ∧ L⊓centralizer ({z} : Set G)=R ∧
      L⊓centralizer ({z} : Set G)≤normalizer (P : Set G) ∧
      Nat.card (W⊓P : Subgroup G)=16 ∧ centerIn P≤W ∧
      (U⊓P : Subgroup G)≠W⊓P := by
  let P := π.ker.map (T : Subgroup G).subtype
  let H := centralizer ({(t:G)} : Set G)
  let Lt := (pResidual 2 (K⊓H : Subgroup G)).map (K⊓H).subtype
  let B := conjugateSpanBy Lt H
  obtain ⟨k,hk,S,W,hUR,hWR,hRT,hRc,hWe,hWc,_,hgen,hint,hZc,hTN,
    _,hLc,hcore,_,hLC,_,hdis,hLW,_,_,hIc,hZW,hneq⟩ :=
    original_tripleSix_escaping_opposite_parabolic h structural D a t ht heven hout π hP
  let := hWe
  let c := MulAut.conj k
  let Bk := B.map c.toMonoidHom
  let R := ((S : Subgroup B).map B.subtype).map c.toMonoidHom
  let N := normalizer (W.subgroupOf Bk : Set Bk)
  let L := N.map Bk.subtype
  have hRB : R≤Bk := map_mono (map_subtype_le _)
  have hWB : W≤Bk := hWR.trans hRB
  have hRL : R≤L := by
    intro x hx
    refine ⟨⟨x,hRB hx⟩,?_,rfl⟩
    change (⟨x,hRB hx⟩:Bk)∈normalizer (W.subgroupOf Bk : Set Bk)
    rw [←subgroupOf_normalizer_eq hWB]
    exact (hTN.trans inf_le_right) (hRT hx)
  obtain ⟨f,hf,hfk,hfkc,hBkC⟩ := component_conjugate_cover h structural D a t ht heven hout k
  have hCZ : centerIn Bk=centerIn L := hBkC.trans hLC.symm
  have hzW : z∈W := hZW (hZ.symm ▸ mem_zpowers z)
  have hzB : z∈Bk := hWB hzW
  have hzn : (⟨z,hzB⟩:Bk)∉f.ker := by
    intro hh
    rw [hfk] at hh
    have hzC : z∈centerIn L := hCZ ▸ (show z∈centerIn Bk by
      rw [centerIn_eq_map_center]; exact ⟨⟨z,hzB⟩,hh,rfl⟩)
    exact hzne (mem_bot.mp (hdis ▸ (show z∈centerIn L⊓centerIn (T : Subgroup G) from ⟨hzC,hz⟩)))
  let : Group.IsPerfect Lt := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect B := conjugateSpanBy_isPerfect Lt H
  let eb := B.equivMapOfInjective c.toMonoidHom c.injective
  let : Group.IsPerfect Bk := Group.IsPerfect.ofSurjective (f := eb.toMonoidHom) eb.surjective
  let Q := W.subgroupOf Bk
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf hWB
  have hQ : Nat.card Q=64 := (Nat.card_congr (subgroupOfEquivOfLe hWB).toEquiv).trans hWc
  have hU : U.map c.toMonoidHom=U := mem_normalizer_iff_map_conj_eq.mp (D.normalizes hk)
  have hCU : centerIn Bk≤U := by
    rw [hBkC]
    exact (map_mono (f := c.toMonoidHom) (tripleSixPoint_properties D a t ht).2.1).trans_eq hU
  have hCW : centerIn Bk≤W := by
    have hh : centerIn Bk≤centerIn R := fun x hx =>
      ⟨hUR (hCU hx),fun y hy => hx.2 y (hRB hy)⟩
    rw [←hint] at hh
    exact hh.trans inf_le_right
  have hkQ : f.ker≤Q := by
    rw [hfk]
    intro x hx
    exact hCW (by rw [centerIn_eq_map_center]; exact ⟨x,hx,rfl⟩)
  have hCP := Matrix.PSL3Four.FullPlaneNormalizer.full_plane_point_centralizer_isPGroup
    f hf hfk.le hfkc Q hkQ hQ (⟨z,hzB⟩:Bk) hzW hzn
  let C := L⊓centralizer ({z} : Set G)
  have hmapC : (N⊓centralizer ({(⟨z,hzB⟩:Bk)} : Set Bk)).map Bk.subtype=C := by
    ext x
    constructor
    · rintro ⟨y,⟨hy,hc⟩,rfl⟩
      exact ⟨mem_map_of_mem _ hy,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩
    · rintro ⟨⟨y,hy,rfl⟩,hc⟩
      exact ⟨y,⟨hy,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc))⟩,rfl⟩
  have hCp : IsPGroup 2 C := hmapC ▸ hCP.map Bk.subtype
  have hRC : R≤C := by
    intro x hx
    exact ⟨hRL hx,mem_centralizer_singleton_iff.mpr (hz.2 x (hRT hx))⟩
  let S' : Sylow 2 L := Sylow.ofCard (R.subgroupOf L) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv,hRc,hLc]
    decide +kernel)
  have hEq : C=R := by
    have he := S'.is_maximal' (hCp.comap_of_injective L.subtype L.subtype_injective)
      (subgroupOf_mono L hRC)
    change C.subgroupOf L=R.subgroupOf L at he
    have hh := congrArg (Subgroup.map L.subtype) he
    simpa only [map_subgroupOf_eq_of_le (show C≤L from inf_le_left),
      map_subgroupOf_eq_of_le hRL] using hh
  have hTP : (T : Subgroup G)≤normalizer (P : Set G) := by
    intro x hx
    exact π.ker.le_normalizer_map (T : Subgroup G).subtype
      (mem_map_of_mem _ (show (⟨x,hx⟩:T)∈normalizer (π.ker : Set T) by
        rw [normalizer_eq_top]; exact mem_top _))
  exact ⟨k,hk,S,W,hWe,hWc,hgen,hint,hZc,hWR,hRT,hRL,hRc,hTN,hcore,hEq,
    hEq.le.trans (hRT.trans hTP),hIc,hZW,hneq⟩

end CFSG.Quasithin.Chapter12.Section07
