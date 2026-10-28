module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5FullCore
public import Theory.GroupTheory.MinusExtraspecialCoreFusion
public import Theory.GroupTheory.InvolutionFusionCover
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.OutsideSizes.Extension

/-!
# Involution fusion in the original normalized A₅ component

The literal selected component K has self-centralizing minus extraspecial
core U and A₅ quotient. Its order is 1920, and its index in H and the
index of T∩K in T are each one or two. Thompson transfer in the original
simple group therefore puts every ambient involution into this same K.

The five-point core action and the original returning conjugate fuse every
core involution to the point z. Outside-core involutions form one K-class;
their centralizers in K have order sixteen. Thus G has one or two involution
classes even in the retained S₅ quotient branch. This does not construct the
separating outside involution needed to exclude that branch or recognize G
as an actual Janko model. The final ambient exclusion stays with the
terminal-solvability owner.

Source: Aschbacher, *Sporadic Groups* (1994), 46.1,46.11, pp.251,255;
Aschbacher–Smith 14.2.17 and 14.3.6,15, pp.986–987,991,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
section Source
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)

variable (hnot : ¬ ClassificationModels.IsTheoremEModel G) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
include hnot hgP hgH hyp hK


include hG hempty hM hu hmany hcard e hne

private theorem source_single_a5_core_fusion_inputs
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Nonempty (pCore 2 K ≃* MinusExtraspecial.Model) ∧
      centralizer (pCore 2 K : Set K) ≤ pCore 2 K ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
  have hUK := source_single_a5_component_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hUH := source_single_a5_full_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨eU⟩ := source_single_a5_minus_model_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hfit⟩ := source_single_a5_full_parabolic_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨heK,_⟩ := source_terminal_single_a5_parabolic_of_large_actor_degrees
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hK e5
    (fun _ => Or.inl hd) hnot hspan
  refine ⟨⟨((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective).trans
    ((MulEquiv.subgroupCongr hUK.symm).trans eU)⟩,?_,heK⟩
  have hcH : centralizer (pCore 2 F.H : Set F.H) ≤ pCore 2 F.H := by
    rw [←hfit]
    exact centralizer_generalizedFitting_le _
  intro x hx
  let xH : F.H := ⟨x,hK.le_pointNormalizer x.property⟩
  have hxH : xH ∈ pCore 2 F.H := hcH (by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hyU : (y:G) ∈ F.U := hUH.symm ▸ mem_map_of_mem F.H.subtype hy
    obtain ⟨k,hk,hky⟩ := hUK ▸ hyU
    apply Subtype.ext
    change (y:G)*(x:G)=(x:G)*(y:G)
    rw [←hky]
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx k hk))
  have hxU : (x:G) ∈ F.U := hUH.symm ▸ mem_map_of_mem F.H.subtype hxH
  obtain ⟨k,hk,hkx⟩ := hUK ▸ hxU
  exact (show k=x from Subtype.ext hkx) ▸ hk

/-- The selected component has order 1920 and index at most two in the
literal point centralizer. This does not identify K with that centralizer. -/
theorem source_single_a5_component_index_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Nat.card K = 1920 ∧
      ((K.subgroupOf F.H).index = 1 ∨ (K.subgroupOf F.H).index = 2) ∧
      ((K.subgroupOf (T : Subgroup G)).index = 1 ∨
        (K.subgroupOf (T : Subgroup G)).index = 2) := by
  obtain ⟨⟨eQ⟩,_,⟨eK⟩⟩ := source_single_a5_core_fusion_inputs hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hQ : Nat.card (pCore 2 K) = 32 := (Nat.card_congr eQ.toEquiv).trans MinusExtraspecial.card_model
  have hqc : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hkc : Nat.card K = 1920 := by
    rw [(pCore 2 K).card_eq_card_quotient_mul_card_subgroup,hqc,hQ]
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hUK := source_single_a5_component_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hUH := source_single_a5_full_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,_,_,hker⟩ := source_single_a5_extraspecial_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hqK : q.ker ≤ K.subgroupOf F.H := by
    rw [QuotientGroup.ker_mk',hker]
    intro x hx
    exact (hUK.le.trans (pCoreIn_le 2 K)) (hUH.symm ▸ mem_map_of_mem F.H.subtype hx)
  have hi : (K.subgroupOf F.H).index = 1 ∨ (K.subgroupOf F.H).index = 2 := by
    have hdc : Nat.card (F.terminalDot K) = 60 := by
      rw [Nat.card_congr e5.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hh := (F.terminalDot K).card_mul_index
    rw [hdc] at hh
    change 60 * ((K.subgroupOf F.H).map q).index = Nat.card F.TerminalHdot at hh
    rw [(K.subgroupOf F.H).index_map_eq (QuotientGroup.mk'_surjective _) hqK] at hh
    rcases source_single_a5_whole_group_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd with ha | ha
    · obtain ⟨a⟩ := ha
      have hfull : Nat.card F.TerminalHdot = 60 := by
        rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      rw [hfull] at hh
      omega
    · obtain ⟨a⟩ := ha
      have hfull : Nat.card F.TerminalHdot = 120 := by
        rw [Nat.card_congr a.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
        norm_num [Nat.factorial]
      rw [hfull] at hh
      omega
  have hn : (K.subgroupOf F.H).Normal := by
    have hh := hK.normal_span
    rwa [←hspan] at hh
  let := hn
  have hdvd := (K.subgroupOf F.H).relIndex_dvd_index_of_normal ((T : Subgroup G).subgroupOf F.H)
  rw [relIndex_subgroupOf (H:=K) (K:=(T:Subgroup G)) (L:=F.H) (F.invariant 1)] at hdvd
  refine ⟨hkc,hi,?_⟩
  rcases hi with hi | hi
  · exact Or.inl (Nat.eq_one_of_dvd_one (hi ▸ hdvd))
  · rw [hi] at hdvd
    exact (Nat.dvd_prime Nat.prime_two).mp hdvd

/-- Thompson transfer puts every ambient involution into the original
selected component, even when its point centralizer has quotient S₅. -/
theorem source_single_a5_involutions_into_component_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (x : G) (hx : orderOf x = 2) :
    ∃ y : K, orderOf y = 2 ∧ IsConj x (y:G) := by
  let := hG.simple
  obtain ⟨_,_,hidx⟩ := source_single_a5_component_index_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hc : ∃ y : T, y ∈ K.subgroupOf (T : Subgroup G) ∧ IsConj x (y:G) := by
    rcases hidx with h1 | h2
    · obtain ⟨y,hy⟩ := T.exists_isConj_of_orderOf_eq_prime_pow (n:=1) (by simpa using hx)
      exact ⟨y,(index_eq_one.mp h1) ▸ mem_top _,hy⟩
    · exact T.exists_isConj_mem_of_index_two_ambient
        (index_ne_two_of_nonabelian_simple hG.nonabelian) _ h2 x hx
  obtain ⟨y,hy,hxy⟩ := hc
  refine ⟨⟨y,hy⟩,?_,hxy⟩
  rw [←orderOf_coe]
  obtain ⟨a,ha⟩ := isConj_iff.mp hxy
  exact (congrArg orderOf ha).symm.trans (((MulAut.conj a).orderOf_eq x).trans hx)

/-- The two core orbits fuse through the original returning point. Outside
core involutions are one class inside K, with local centralizer order sixteen. -/
theorem source_single_a5_component_involution_fusion_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    ∃ z : G, orderOf z = 2 ∧ F.H = centralizer ({z} : Set G) ∧
      (∀ u ∈ F.U, orderOf u = 2 → IsConj z u) ∧
      (∀ u v : K, orderOf u = 2 → orderOf v = 2 →
        (u:G) ∉ F.U → (v:G) ∉ F.U → IsConj u v) ∧
      (∀ u : K, orderOf u = 2 → (u:G) ∉ F.U →
        Nat.card (centralizer ({u} : Set K)) = 16) := by
  obtain ⟨he,hc,⟨eK⟩⟩ := source_single_a5_core_fusion_inputs hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hUK := source_single_a5_component_core_of_four hG T hempty hM hu hmany
    hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  obtain ⟨_,z,hz,hHz,hamb,hmodel,⟨t,htU,hzt,htz⟩,_⟩ :=
    source_single_a5_involution_centralizer_of_four hG T hempty hM hu hmany
      hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hzU : z ∈ F.U := hamb ▸ Janko23.HTypeAt.involution_mem_core
  obtain ⟨zK,hzK,hzval⟩ := hUK ▸ hzU
  change (zK:G) = z at hzval
  let zQ : pCore 2 K := ⟨zK,hzK⟩
  have hzQ : orderOf zQ = 2 := by
    rw [←orderOf_coe,←orderOf_coe]
    change orderOf (zK:G) = 2
    rw [hzval,hz]
  have hzZ : zQ ∈ center (pCore 2 K) := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change ((y:K):G)*(zK:G)=(zK:G)*((y:K):G)
    rw [hzval]
    exact mem_centralizer_singleton_iff.mp (hHz ▸ hK.le_pointNormalizer (y:K).property)
  have hfive : 5 ∣ (pCore 2 K).index := by
    change 5 ∣ Nat.card (K ⧸ pCore 2 K)
    rw [Nat.card_congr eK.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  refine ⟨z,hz,hHz,?_,?_,?_⟩
  · intro u hu huo
    obtain ⟨uK,huK,huval⟩ := hUK ▸ hu
    change (uK:G) = u at huval
    have hreturn : ∃ tQ : pCore 2 K, IsConj (K.subtype zQ) (K.subtype tQ) ∧ tQ ≠ zQ := by
      obtain ⟨tK,htK,htval⟩ := hUK ▸ htU
      change (tK:G) = t at htval
      refine ⟨⟨tK,htK⟩,?_,?_⟩
      · change IsConj (zK:G) (tK:G)
        rwa [hzval,htval]
      · intro hEq
        apply htz
        exact htval.symm.trans ((congrArg (fun x : pCore 2 K => ((x:K):G)) hEq).trans hzval)
    have huQ : orderOf (⟨uK,huK⟩ : pCore 2 K) = 2 := by
      rw [←orderOf_coe,←orderOf_coe]
      change orderOf (uK:G) = 2
      rw [huval,huo]
    have hf := MinusExtraspecial.pCore_involution_isConj_of_returning K.subtype K.subtype_injective
      he hc hfive zQ hzQ hzZ hreturn ⟨uK,huK⟩ huQ
    change IsConj (zK:G) (uK:G) at hf
    rwa [hzval,huval] at hf
  · intro u v hu hv huQ hvQ
    exact MinusExtraspecial.pCore_outside_involutions_isConj he hc ⟨eK⟩ u v hu hv
      (fun hh => huQ (hUK.symm ▸ mem_map_of_mem K.subtype hh))
      (fun hh => hvQ (hUK.symm ▸ mem_map_of_mem K.subtype hh))
  · intro u hu huQ
    exact (J2OutsideSizesCalculation.extension_sizes (pCore 2 K) he.some hc eK u hu
      (fun hh => huQ (hUK.symm ▸ mem_map_of_mem K.subtype hh))).2

/-- There are at most two nonempty ambient involution classes, also in the
retained S₅ quotient branch. This is a fusion statement, not Janko recognition. -/
theorem source_single_a5_involution_classes_of_four
    (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
    (hspan : K = conjugateSpanBy K (T : Subgroup G))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    Janko23.OneInvolutionClass G ∨ Janko23.TwoInvolutionClasses G := by
  classical
  obtain ⟨z,hz,_,hcore,houtside,_⟩ := source_single_a5_component_involution_fusion_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  have hc := source_single_a5_involutions_into_component_of_four
    hG T hempty hM hu hmany hcard e F hne hnot g hgP hgH hyp hK e5 hspan hd
  by_cases hall : ∀ x : G, orderOf x = 2 → IsConj x z
  · exact Or.inl ⟨z,hz,hall⟩
  push Not at hall
  obtain ⟨t,ht,htz⟩ := hall
  obtain ⟨v,hv,htv⟩ := hc t ht
  have hvQ : (v:G) ∉ F.U := fun hh =>
    htz (htv.trans (hcore v hh ((orderOf_coe v).trans hv)).symm)
  refine Or.inr ⟨z,t,hz,ht,fun hh => htz hh.symm,?_⟩
  intro x hx
  obtain ⟨u,hu,hxu⟩ := hc x hx
  by_cases huQ : (u:G) ∈ F.U
  · exact Or.inl (hxu.trans (hcore u huQ ((orderOf_coe u).trans hu)).symm)
  · exact Or.inr ((hxu.trans (K.subtype.map_isConj
      (houtside u v hu hv huQ hvQ))).trans htv.symm)

end Source
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
