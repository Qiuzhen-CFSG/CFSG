module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOrbit
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureRank
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAutomizer
public import CFSG.Quasithin.ChapterG.Section03.CommonCenterSource
import Theory.Representation.HexacodeAction.WeightFourEvenNormalTwo
import Theory.Representation.HexacodeAction.WeightFourVectorCore
import Theory.GroupTheory.SylowNormalizedResidual
import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Maximal
import Theory.GroupTheory.QuotientActionCentralizer

/-!
# The original inner-automizer branch has a common transvection center

The actual closure image in the even hexacode group is the weight-four
vector stabilizer's two-core. Its whole-module commutator is the original
four-group V1. Thus the original U-image on W/<z> fixes the binary point
V1/<z> and has all displacements in that point. Its order is four or sixteen,
so the genuine common-center source theorem supplies G.3.1 on its orbit.

Source: Aschbacher--Smith 12.7.15--16, printed pp.843--844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- In the actual inner-automizer branch, all commutators of the original
whole U with the smaller closure lie in the original scalar four-group. -/
theorem original_tripleSix_central_closure_inner_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    ⁅U,conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))⁆ ≤ tripleSixPoint D a z := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let c := tripleSixPointCoordinates D a
  let v := (c z).toAdd
  obtain ⟨hWT,f,hf,hfk,hK,hchart,hN,hp,hne,_⟩ :=
    original_tripleSix_central_closure_automizer h structural D a z hz hzT hnot
  let N := (inducedAutomizer U W).map f
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) := ((structural K h).2.2 U D).1
  have hWN : W ≤ normalizer (U : Set G) := hWT.trans hTN
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hWH : W = conjugateSpanBy V1 H := hc.2.1
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [hWH]
    exact le_normalizer_conjugateSpanBy V1 H
  have hCK : K ⊓ C ≤ H :=
    (le_embedded_pResidual_sup_sylow_of_normalizes T (K ⊓ C)
      ((le_inf D.sylow_normalizes_component (hzT.trans C.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf)).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hCKimage : (inducedAutomizer U (K ⊓ C)).map f =
      (Hexacode.fullWeightVectorStabilizer v).map hexSign.ker.subtype := by
    apply le_antisymm
    · rintro _ ⟨_,⟨k,hk,rfl⟩,rfl⟩
      rw [hfk ⟨k,hk.1⟩]
      exact ⟨(tripleSixPointCentralizerProjection D a z ⟨k,hk⟩).val,
        (tripleSixPointCentralizerProjection D a z ⟨k,hk⟩).property,rfl⟩
    · rintro _ ⟨g,hg,rfl⟩
      obtain ⟨k,hk⟩ := tripleSixPointCentralizerProjection_surjective D a z ⟨g,hg⟩
      refine ⟨U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property.1⟩,
        ⟨⟨k,D.normalizes k.property.1⟩,k.property,rfl⟩,?_⟩
      rw [hfk ⟨k,k.property.1⟩]
      exact congrArg (fun q => q.val.val) hk
  have hn : (Hexacode.fullWeightVectorStabilizer v).map hexSign.ker.subtype ≤
      normalizer (N : Set HexAutomorphisms) := by
    rw [←hCKimage]
    exact (map_mono (ChapterE.Section06.inducedAutomizer_normalized hWN
      (hCK.trans hHW))).trans (le_normalizer_map f)
  have heven : N ≤ hexSign.ker := by
    rw [←hK]
    exact map_mono hinner
  have hv := tripleSix_sylow_fixed_weightFour D a z hz hzT
  have hcore := Hexacode.weightFour_even_normal_two_eq_core v hv N hN hp hne hn heven
  rw [commutator_comm]
  apply commutator_le.mpr
  intro w hw u hu
  let b := U.normalizerMonoidHom.rangeRestrict ⟨w,hWN hw⟩
  have hb : f b ∈ N := mem_map.mpr ⟨b,⟨⟨w,hWN hw⟩,hw,rfl⟩,rfl⟩
  rw [hcore] at hb
  obtain ⟨g,hg,hgmark⟩ := hb
  have hd : Hexacode.evenAction g (c ⟨u,hu⟩).toAdd - (c ⟨u,hu⟩).toAdd ∈
      (Submodule.span Hexacode.F {v}).restrictScalars (ZMod 2) := by
    rw [←Hexacode.weightFourVectorCore_commutator v hv]
    exact Submodule.subset_span ⟨g,hg,(c ⟨u,hu⟩).toAdd,Submodule.mem_top,rfl⟩
  let d : U := b.val ⟨u,hu⟩ * (⟨u,hu⟩ : U)⁻¹
  have hdchart : (c d).toAdd =
      Hexacode.evenAction g (c ⟨u,hu⟩).toAdd - (c ⟨u,hu⟩).toAdd := by
    change (c (b.val ⟨u,hu⟩ * (⟨u,hu⟩ : U)⁻¹)).toAdd = _
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
    rw [hchart b ⟨u,hu⟩,←hgmark]
    rfl
  refine ⟨d,?_,rfl⟩
  change (c d).toAdd ∈ Submodule.span Hexacode.F {v}
  rw [hdchart]
  exact hd

omit [Finite G] in
private theorem quotient_common_center
    (H W V1 Z : Subgroup G) (hVU : V1 ≤ U)
    (hHW : H ≤ normalizer (W : Set G))
    (hcomm : ⁅U,W⁆ ≤ V1) [IsElementaryAbelian 2 U]
    [(Z.subgroupOf W).Normal] [IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W)]
    (φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)))
    (hformula : ∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
        ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩))
    (x : Additive (W ⧸ Z.subgroupOf W))
    (hspan : Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
      (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W))))) :
    (∀ g ∈ (U.subgroupOf H).map φ, g x = x) ∧
      (∀ g ∈ (U.subgroupOf H).map φ, ∀ y, g y-y ∈ BinaryTransvectionGroups.centerLine x) := by
  let q := QuotientGroup.mk' (Z.subgroupOf W)
  constructor
  · rintro _ ⟨u,hu,rfl⟩
    have hx : x.toMul ∈ (V1.subgroupOf W).map q := by
      have hh := Submodule.mem_span_singleton_self (R := ZMod 2) x
      rw [hspan] at hh
      exact hh
    obtain ⟨v,hv,hvx⟩ := hx
    have he : (u:G)*(v:G)*(u:G)⁻¹ = v := by
      have hh : (⟨u,hu⟩ : U) * ⟨v,hVU hv⟩ = ⟨v,hVU hv⟩ * ⟨u,hu⟩ := mul_comm _ _
      exact mul_inv_eq_of_eq_mul (congrArg (fun q : U => (q:G)) hh)
    have hx' : Additive.ofMul (q v) = x := congrArg Additive.ofMul hvx
    rw [←hx',hformula]
    congr 2
    exact Subtype.ext he
  · rintro _ ⟨u,hu,rfl⟩ y
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) y.toMul
    have hy : Additive.ofMul (q w) = y := congrArg Additive.ofMul hw
    rw [←hy,hformula]
    rw [←ofMul_div]
    change Additive.ofMul (q _ / q w) ∈ Submodule.span (ZMod 2) {x}
    rw [hspan,←map_div]
    change q _ ∈ (V1.subgroupOf W).map q
    refine mem_map.mpr ⟨_,?_,rfl⟩
    have hm := hcomm (commutator_mem_commutator (show (u:G) ∈ U from hu) w.property)
    simpa only [mem_subgroupOf,coe_div,commutatorElement_def,div_eq_mul_inv,
      coe_mul,coe_inv] using hm

/-- The genuine first branch of the original closure action satisfies the
common-center transvection source, on the orbit of the original point. -/
theorem original_tripleSix_central_closure_transvections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    let Z := zpowers (z:G)
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧ pCore 2 φ.range = ⊥ ∧
          (Nat.card ((U.subgroupOf H).map φ) = 4 ∨ Nat.card ((U.subgroupOf H).map φ) = 16) ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ ∧
            (∀ g ∈ (U.subgroupOf H).map φ, g x = x) ∧
            (∀ g ∈ (U.subgroupOf H).map φ, ∀ y, g y-y ∈ BinaryTransvectionGroups.centerLine x) ∧
            ChapterG.Section03.FullAction φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.Decomposition φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.LocalStructure φ.range (MulAction.orbit φ.range x) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_orbit h structural D a z hz hzT hnot
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore,x,hx,hspan,horbit⟩ := hrest
  let := he
  obtain ⟨N,hN,hmem,_,_,_,_,hcard,_,_⟩ :=
    original_tripleSix_central_closure_rank h structural D a z hz hzT hnot
  let : N.Normal := hN
  have hk : φ.ker = N := by ext g; exact (hker g).trans (hmem g).symm
  have heq : Nat.card ((U.subgroupOf H).map φ) =
      Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N)) := by
    apply le_antisymm
    · apply card_map_le_card_map_of_ker_le
      rw [QuotientGroup.ker_mk',hk]
    · apply card_map_le_card_map_of_ker_le
      rw [QuotientGroup.ker_mk',hk]
  have hcard' : Nat.card ((U.subgroupOf H).map φ) = 4 ∨ Nat.card ((U.subgroupOf H).map φ) = 16 :=
    heq.symm ▸ hcard
  have hcomm := original_tripleSix_central_closure_inner_commutator h structural D a z hz hzT hnot hinner
  let := D.elementary
  obtain ⟨hfix,hmove⟩ := quotient_common_center H W V1 Z
    (tripleSixPoint_properties D a z hz).2.1 hHW hcomm φ hformula x hspan
  have hAH : (U.subgroupOf H).map φ ≤ φ.range := by
    rintro _ ⟨g,_,rfl⟩
    exact ⟨g,rfl⟩
  have hlarge : 2 < Nat.card ((U.subgroupOf H).map φ) := by rcases hcard' with hc | hc <;> omega
  have hs := ChapterG.Section03.source_conclusions_of_common_center hcore x hx
    ((U.subgroupOf H).map φ) hAH hlarge hfix hmove
  exact ⟨hHW,hZN,he,φ,hformula,hker,hcore,hcard',x,hx,hspan,horbit,hfix,hmove,hs⟩

end CFSG.Quasithin.Chapter12.Section07
