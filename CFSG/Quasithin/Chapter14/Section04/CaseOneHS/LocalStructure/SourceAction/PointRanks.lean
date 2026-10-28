module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.EarlierNontrivial
public import CFSG.Quasithin.Chapter12.Section08.Terminal.ThreeRank
public import CFSG.Quasithin.Chapter12.Section08.Terminal.Centers
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer

/-!
# Point-centralizer three-rank in the original HS action

The actual I₂ quotient and its relative normality give the source bound
m₃(C_H(V₂/V₁)) ≤ 1. A cube-one lift fixing the marked point and centralizing
Z(U) fixes V₂: its central displacement has both odd and two-power order.
The restricted action kernel is a two-group, so the bound descends to the
point stabilizer inside the dotted image of C_H(Z(U)).

Under the preceding centerlessness premise, the two conjugate centers
commute. Their normal closure has nontrivial dotted image, forcing every
self-centralizing nonabelian simple normal subgroup into that center-centralizer
image. `CatalogueExclusions` applies both facts to the literal split-six row.

The lifting calculation is adapted from the rank-two terminal source, with
all closure, quotient and plane hypotheses proved here for the original
rank-three flag. No natural coordinates or action-kernel equality is assumed.
Source: Aschbacher--Smith, 12.8.10, 12.8.13(8), and 14.3.23--24,32,
printed pp.853,855--856,999--1000,1003--1004.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- Source 12.8.13(8) on the original rank-three flag. -/
theorem source_tilde_plane_three_rank_le_one
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    primeRank 3 F.terminalTildePlaneCentralizer ≤ 1 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := CaseOneLarge.source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨e,_,_,_,hIG,hIN,_,_,_,_,hIC,_⟩ := F.binary_generation (by decide) L
    chosen.normalizes (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
    hcomm hsquare hspan hne g hgP hgH
  exact F.lemma_12_8_13_eight d.qtke.quasithin (by decide) L hIG hIN hIC ⟨e⟩

/-- Fixing both Z(U) and U/Z(U) leaves a two-group in the original H. -/
theorem source_center_centralizing_kernel_le_core :
    (centralizer (F.ZU : Set G)).subgroupOf F.H ⊓ F.terminalHatAction.ker ≤ pCore 2 F.H := by
  let := chosen.elementary
  let c := CaseOneLarge.source_closure_geometry F d earlier hq chosen structural alternatives hne
  have huk : F.uAction.ker ≤ pCore 2 F.H := by
    rw [← c.tilde_kernel]
    intro h hh
    apply (F.mem_localTildeAction_ker_iff F.H le_rfl h).mpr
    intro u hu
    have he := congrArg (fun a : MulAut F.U => (a ⟨u,hu⟩ : G)) hh
    change (h : G) * u * (h : G)⁻¹ = u at he
    have hz : ⁅(h : G),u⁆ = 1 := by
      rw [commutatorElement_def,he,mul_inv_cancel]
    exact hz ▸ (F.Vi 1).one_mem
  let a := (automorphismPair (center F.U)).comp F.uAction
  have hp : IsPGroup 2 a.ker :=
    (isPGroup_automorphism_pair_kernel (center F.U) (c.two.to_subgroup _)).comap_of_ker_isPGroup
      F.uAction (pCore_isPGroup.to_le huk)
  have ha : a.ker ≤ pCore 2 F.H := le_sSup ⟨inferInstance,hp⟩
  apply le_trans _ ha
  intro h hh
  change automorphismPair (center F.U) (F.uAction h) = 1
  rw [automorphismPair_apply]
  apply Prod.ext
  · apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change (h : G) * (z : G) * (h : G)⁻¹ = (z : G)
    have hz := hh.1 (z : G) (mem_map_of_mem F.U.subtype z.property)
    exact mul_inv_eq_iff_eq_mul.mpr hz.symm
  · exact hh.2

section Marked
variable [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat) (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
include hline
theorem source_point_preimage_centralizes_plane_of_cube_one (a : F.H)
    (ha : QuotientGroup.mk' F.terminalHatAction.ker a ∈
      ChapterG.Section10.pointCentralizer F.terminalRepresentation v)
    (haZ : (a:G) ∈ centralizer (F.ZU : Set G)) (ha3 : a ^ 3 = 1) :
    (a:G) ∈ centralizer (F.Vi 2 : Set G) := by
  let := chosen.elementary
  let closureData := CaseOneLarge.source_closure_geometry F d earlier hq chosen structural alternatives hne
  intro b hb
  let bU : F.U := ⟨b,(F.le_seed 2).trans (le_conjugateSpanBy _ _) hb⟩
  have hbline : Additive.ofMul (QuotientGroup.mk' (center F.U) bU) ∈
      Submodule.span (ZMod 2) {v} := hline ▸ ⟨bU,hb,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hbline
  have hfix : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
      (Additive.ofMul (QuotientGroup.mk' (center F.U) bU)) =
      Additive.ofMul (QuotientGroup.mk' (center F.U) bU) := by
    rw [← hc,map_smul]
    exact congrArg (fun w => c • w) ha
  have hq : QuotientGroup.mk' (center F.U)
      (F.U.normalizerMonoidHom ⟨a,le_normalizer_conjugateSpanBy _ _ a.property⟩ bU) =
      QuotientGroup.mk' (center F.U) bU := by
    change F.terminalHatAction a (QuotientGroup.mk' (center F.U) bU) = _ at hfix
    rwa [F.terminalHatAction_apply_mk] at hfix
  have hz : (F.U.normalizerMonoidHom
      ⟨a,le_normalizer_conjugateSpanBy _ _ a.property⟩ bU) * bU⁻¹ ∈ center F.U := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center F.U) (_ * _) = 1
    rw [map_mul,map_inv,hq,mul_inv_cancel]
  let z := (a:G)*b*(a:G)⁻¹*b⁻¹
  have hzZ : z ∈ F.ZU := mem_map_of_mem F.U.subtype hz
  let α := MulAut.conj (a:G)
  have hαb : α b = z*b := by dsimp [α,z]; group
  have hαz : α z = z := by
    change (a:G)*z*(a:G)⁻¹=z
    exact mul_inv_eq_iff_eq_mul.mpr (haZ z hzZ).symm
  have hα3 : α^3 = 1 := by
    rw [show α^3 = MulAut.conj ((a:G)^3) from (map_pow _ _ _).symm]
    rw [show (a:G)^3=1 from congrArg Subtype.val ha3,map_one]
  have hcalc : α (α (α b)) = b := by
    have he := congrArg (fun t : MulAut G => t b) hα3
    simpa only [pow_succ,pow_zero,
      MulAut.mul_apply,MulAut.one_apply] using he
  simp only [hαb,map_mul,hαz] at hcalc
  have hz3 : z^3=1 := by
    apply mul_right_cancel (b := b)
    simpa only [pow_succ,pow_zero,
      one_mul,mul_assoc] using hcalc
  let zU : F.U := ⟨z,map_subtype_le (center F.U) hzZ⟩
  have hdv : orderOf zU ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hz3)
  have he : zU=1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (closureData.two.orderOf_coprime (by decide : Nat.Coprime 2 3) zU)
      (dvd_refl _) hdv)
  have hz1 : z=1 := congrArg Subtype.val he
  have hab : (a:G)*b=b*(a:G) :=
    commutatorElement_eq_one_iff_mul_comm.mp hz1
  exact hab.symm

/-- Three-elements in the source point lift which centralize Z(U) actually
centralize the marked plane. The elementary-rank criterion transfers the
source tilded-plane rank bound to this full point lift. -/
theorem source_center_centralizing_point_lift_three_rank_le_one
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    primeRank 3 ((ChapterG.Section10.pointCentralizer F.terminalRepresentation v).comap
      (QuotientGroup.mk' F.terminalHatAction.ker) ⊓
      (centralizer (F.ZU : Set G)).subgroupOf F.H : Subgroup F.H) ≤ 1 := by
  let P := (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).comap
    (QuotientGroup.mk' F.terminalHatAction.ker) ⊓
    (centralizer (F.ZU : Set G)).subgroupOf F.H
  change primeRank 3 P ≤ 1
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro E hE
  let := hE
  let f : E →* G := F.H.subtype.comp (P.subtype.comp E.subtype)
  have hf : Function.Injective f := F.H.subtype_injective.comp
    (P.subtype_injective.comp E.subtype_injective)
  have ht (e : E) : f e ∈ F.terminalTildePlaneCentralizer := by
    have he3 : e.val.val ^ 3 = 1 := congrArg (fun x : P => x.val)
      (elemPow_eq_one_of_isElementaryAbelian (A := E) e.val e.property)
    have hc := source_point_preimage_centralizes_plane_of_cube_one d earlier hq chosen structural alternatives F hne v hline e.val.val
      e.val.property.1 e.val.property.2 he3
    apply mem_map.mpr
    refine ⟨e.val.val,?_,rfl⟩
    change QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H) e.val.val ∈
      centralizer (F.tilde (F.Vi 2) : Set F.G₁tilde)
    rintro _ ⟨b,hb,rfl⟩
    exact congrArg (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H))
      (Subtype.ext (hc b hb))
  let j := f.codRestrict F.terminalTildePlaneCentralizer ht
  have hj : Function.Injective j := by
    intro a b he
    apply hf
    exact congrArg (fun z : F.terminalTildePlaneCentralizer => (z:G)) he
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 3 j hj).trans
    (source_tilde_plane_three_rank_le_one d earlier hq chosen structural alternatives F hne g hgP hgH)
  let : IsElementaryAbelian 3 (⊤ : Subgroup E) := IsElementaryAbelian.of_injective
    (⊤ : Subgroup E).subtype (⊤ : Subgroup E).subtype_injective
  simpa only [card_top] using (primeRank_le_iff_elementary_card_le E).mp hr
    (⊤ : Subgroup E) inferInstance

/-- The actual dotted image of the center-centralizer has point-stabilizer
three-rank at most one. The restricted quotient kernel is a two-group. -/
theorem source_center_centralizing_point_image_three_rank_le_one
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    primeRank 3 ((ChapterG.Section10.pointCentralizer F.terminalRepresentation v).subgroupOf
      (F.terminalDot (centralizer (F.ZU : Set G)))) ≤ 1 := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  let P := (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).comap q ⊓ C
  let D := (ChapterG.Section10.pointCentralizer F.terminalRepresentation v).subgroupOf (C.map q)
  let f : P →* D := {
    toFun := fun a => ⟨⟨q a,mem_map_of_mem q a.property.2⟩,a.property.1⟩
    map_one' := Subtype.ext (Subtype.ext (q.map_one))
    map_mul' := fun a b => Subtype.ext (Subtype.ext (q.map_mul a b)) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a,ha,he⟩ := y.val.property
    have hap : q a ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v :=
      he.symm ▸ y.property
    exact ⟨⟨a,⟨hap,ha⟩⟩,Subtype.ext (Subtype.ext he)⟩
  have hk : f.ker ≤ (pCore 2 F.H).subgroupOf P := by
    intro a ha
    apply source_center_centralizing_kernel_le_core d earlier hq chosen structural alternatives F hne
    refine ⟨a.property.2,?_⟩
    exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun z : D => z.val.val) ha)
  have hp : IsPGroup 2 f.ker :=
    (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf P)).to_le hk
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (primeRank_le_of_surjective_of_coprime 3 f hf hcop).trans
    (source_center_centralizing_point_lift_three_rank_le_one d earlier hq chosen structural alternatives F hne v hline g hgP hgH)


end Marked

/-- The original nontrivial conjugate-center image forces a self-centralizing
simple normal subgroup into the image of C_H(Z(U)). -/
theorem source_simple_normal_le_center_centralizer
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (K : Subgroup F.TerminalHdot) [K.Normal] [IsSimpleGroup K]
    (hKa : ¬ IsMulCommutative K) (hKc : centralizer (K : Set F.TerminalHdot) = ⊥) :
    K ≤ F.terminalDot (centralizer (F.ZU : Set G)) := by
  let N := conjugateSpanBy (conjugate F.ZU g) F.H
  have hNH : N ≤ F.H := conjugateSpanBy_le_self
    ((F.conjugate_ZU_le_X g).trans (F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)))
  have hc : ⁅F.ZU,conjugate F.ZU g⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (F.centers_commutator_le g (F.P_le_seed_normalizer L chosen.normalizes hgP)).trans
      ((source_center_intersections d earlier hq chosen structural alternatives F hne g hgP hgH).1.trans hI).le
  have hNC : N ≤ centralizer (F.ZU : Set G) := by
    apply le_centralizer_iff.mp
    exact le_centralizer_conjugateSpanBy_of_normalizes F.ZU (conjugate F.ZU g) F.H
      F.H_normalizes_ZU (commutator_eq_bot_iff_le_centralizer.mp hc)
  let : (N.subgroupOf F.H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_conjugateSpanBy _ _)
  let : (F.terminalDot N).Normal := Normal.map inferInstance
    (QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hN : F.terminalDot N ≠ ⊥ := by
    intro he
    apply source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives F hne hZ g hgP hgH
    exact le_bot_iff.mp ((map_mono (comap_mono (le_conjugateSpanBy _ _))).trans he.le)
  exact (simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot K hKa hKc _ hN).trans
    (map_mono (comap_mono hNC))
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
