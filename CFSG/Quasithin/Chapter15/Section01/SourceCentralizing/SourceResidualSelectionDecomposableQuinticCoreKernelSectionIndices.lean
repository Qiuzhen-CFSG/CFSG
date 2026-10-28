module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreKernelPairing
-- Internal proof split: the original cyclic support index helper remains frozen.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore

/-!
# Original quintic support indices over a proper normal denominator

A proper Mc-normal denominator in F cannot contain either original marked
plane. Every nontrivial elementary support action has full displacement
onto its marked plane, so movement by V survives this denominator.
If the support action has two independent reflection bits, their isolated
actors give two independent nontrivial quotient coordinates. Otherwise
the action index is at most two. Thus the original V-image satisfies the
actual offender index comparison on any moving intermediate H/D.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem full_support_displacement (A Z : Subgroup G)
    [IsElementaryAbelian 2 A] (hZA:Z≤A) (hcA:Nat.card A=16) (hcZ:Nat.card Z=4)
    (f:G) (hfix:A⊓centralizer ({f}:Set G)≤Z)
    (hdisp:∀a∈A,⁅f,a⁆∈Z) : ∀z∈Z,∃a∈A,⁅f,a⁆=z := by
  let δ : A→*Z := {
    toFun := fun a=>⟨⁅f,(a:G)⁆,hdisp a a.property⟩
    map_one' := Subtype.ext (commutatorElement_one_right f)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅f,(a:G)*(b:G)⁆=⁅f,(a:G)⁆*⁅f,(b:G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hh : (a:G)*⁅f,(b:G)⁆=⁅f,(b:G)⁆*(a:G) :=
        (A.le_centralizer a.property _ (hZA (hdisp b b.property))).symm
      calc
        _=⁅f,(a:G)⁆*((a:G)*⁅f,(b:G)⁆)*(a:G)⁻¹ := by group
        _=_ := by rw [hh]; group }
  have hkerZ (a:δ.ker) : ((a:A):G)∈Z := by
    have hh : ⁅f,((a:A):G)⁆=1 := congrArg Subtype.val a.property
    exact hfix ⟨(a:A).property,mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hh).symm⟩
  let ι : δ.ker→Z := fun a=>⟨((a:A):G),hkerZ a⟩
  have hι : Function.Injective ι := by
    intro a b he
    have hh : ((a:A):G)=((b:A):G) := congrArg (fun z:Z=>(z:G)) he
    exact Subtype.ext (Subtype.ext hh)
  have hk : Nat.card δ.ker≤4 := (Nat.card_le_card_of_injective ι hι).trans_eq hcZ
  have hcount := δ.ker.card_mul_index
  rw [index_ker,hcA] at hcount
  have hr : 4≤Nat.card δ.range := by nlinarith
  have he : δ.range=⊤ := eq_of_le_of_card_ge le_top (by simpa only [card_top,hcZ] using hr)
  have hs : Function.Surjective δ := MonoidHom.range_eq_top.mp he
  intro z hz
  obtain ⟨a,ha⟩ := hs ⟨z,hz⟩
  exact ⟨a,a.property,congrArg Subtype.val ha⟩

private theorem proper_subgroup_card_le_half (A B:Subgroup G)
    (hAB:A≤B) (hn:¬B≤A) (hc:Nat.card B=16) : Nat.card A≤8 := by
  have hi : 1<A.relIndex B := by
    have hp : 0<A.relIndex B := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn1 : A.relIndex B≠1 := fun hh=>hn (relIndex_eq_one.mp hh)
    omega
  have hh:=relIndex_mul_card_of_le hAB
  rw [hc] at hh
  nlinarith

/-- Every actual moving normal intermediate section retains an offender
index comparison for the original V, with its exact denominator and kernel. -/
theorem PreparedChosenModule.decomposable_five_normal_section_indices
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc:Set G)
      let F := conjugateSpanBy E C
      ∀ H D:Subgroup G, D≤H → H≤F → D<F →
        Mc≤normalizer (D:Set G) → ¬H≤centralizer (V:Set G) →
        let K := commutatorPreimage Mc H D
        ¬⁅V,H⁆≤D ∧ 1<K.relIndex V ∧ (centralizer (V:Set G)).relIndex H≤K.relIndex V := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  dsimp only
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc:Set G)
  let F := conjugateSpanBy E C
  intro H D hDH hHF hDF hMcD hnH
  let K := commutatorPreimage Mc H D
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  obtain ⟨hCMc,_,hQT,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,hEA,hFA,hFel,_,_⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  let Q := C.pCoreIn 2
  let J := elementaryAbelianMaxJ Q
  have hJQ:J≤Q := sSup_le fun _ hA=>hA.1
  have hFJ:F≤J := fun f hf=>((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).1
  have hEJ:E≤J := fun e he=>((mem_omegaOneCenterAmbient_iff _ _).mp (hEA he)).1
  have hFC:F≤centralizer (J:Set G) := by
    intro f hf
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).2.2
  have hFT:F≤(T:Subgroup G) := hFJ.trans (hJQ.trans hQT)
  have hFE:F≤centralizer (E:Set G) := hFC.trans (centralizer_le hEJ)
  let : IsElementaryAbelian 2 F := hFel
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHF
  have hHT:H≤(T:Subgroup G) := hHF.trans hFT
  have hHN₁:H≤normalizer (V₁:Set G) := by
    intro f hf
    exact s.centralizer_le_stabilizer ⟨hHT hf,
      (hHF.trans hFE |>.trans (centralizer_le (show Z₁≤E from inf_le_right))) hf⟩
  have hHN₂:H≤normalizer (V₂:Set G) := fun f hf=>s.stabilizes_second ⟨hHT hf,hHN₁ hf⟩
  have hidx₁:(centralizer (V₁:Set G)).relIndex H≤2 :=
    elementary_support_action_index hM.1.2 h.normalized c d s π hp hs hfive H hHT s.first hHN₁
  have hidx₂:(centralizer (V₂:Set G)).relIndex H≤2 :=
    elementary_support_action_index hM.1.2 h.normalized c d s π hp hs hfive H hHT s.second hHN₂
  have hCV:centralizer (V:Set G)=centralizer (V₁:Set G)⊓centralizer (V₂:Set G) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (plane_le _)) (centralizer_le (plane_le _))
    · apply le_centralizer_iff.mpr
      rw [←s.complement]
      exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
  have hupper:(centralizer (V:Set G)).relIndex H≤4 := by
    rw [hCV]
    exact relIndex_inf_le.trans (Nat.mul_le_mul hidx₁ hidx₂)
  have hMcC:Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc:(T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz=>(centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTD:(T:Subgroup G)≤normalizer (D:Set G) := hTMc.trans hMcD
  let S₀:Subgroup G:=(T:Subgroup G)⊓normalizer (V₁:Set G)
  have hSne:S₀≠(T:Subgroup G) := by
    intro he
    have hh:S₀.relIndex (T:Subgroup G)=2 := s.stabilizer_index
    rw [he,relIndex_self] at hh
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt (lt_of_le_of_ne (show S₀≤(T:Subgroup G) from inf_le_left) hSne)
  have htout:t∉normalizer (V₁:Set G) := fun hh=>htS ⟨ht,hh⟩
  have hex:=s.thompson_exchanges t ht htout
  have hZi (i:d.Index) : ¬thompsonPlane T V (c.ambientFactor d i).space≤D := by
    intro hi
    have hpair:Z₁≤D ∧ Z₂≤D := by
      rcases s.covers i with he|he
      · have h1:Z₁≤D := by simpa only [he] using hi
        have hm:Z₁.map (MulAut.conj t).toMonoidHom≤D :=
          (map_mono h1).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hTD ht))
        rw [hex.1] at hm
        exact ⟨h1,hm⟩
      · have h2:Z₂≤D := by simpa only [he] using hi
        have hm:Z₂.map (MulAut.conj t).toMonoidHom≤D :=
          (map_mono h2).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hTD ht))
        rw [hex.2] at hm
        exact ⟨hm,h2⟩
    have hED:E≤D := by
      change thompsonFixed T V≤D
      rw [s.thompson_split]
      exact sup_le hpair.1 hpair.2
    exact hDF.not_ge (conjugateSpanBy_le hED (hCMc.trans hMcD))
  have hsurj (i:d.Index) (f:G) (hf:f∈H)
      (hn:f∉centralizer (plane V (c.ambientFactor d i).space:Set G)) :
      ∀z∈thompsonPlane T V (c.ambientFactor d i).space,
        ∃v∈plane V (c.ambientFactor d i).space,⁅f,v⁆=z := by
    obtain ⟨hfix,hdisp⟩ := s.involution_support_displacement_and_fixed hM.1.2 h.normalized c d π hp hs
      hfive f (hHT hf) (elemPow_eq_one_of_isElementaryAbelian (p:=2) f hf) (hHN₁ hf) i
    let Vi:=plane V (c.ambientFactor d i).space
    let :IsElementaryAbelian 2 Vi:=IsElementaryAbelian.of_le (plane_le _)
    exact full_support_displacement Vi (thompsonPlane T V (c.ambientFactor d i).space)
      inf_le_left (s.support_card i) (s.thompson_card i) f (hfix.resolve_left hn) hdisp
  have hnon (i:d.Index) (f:G) (hf:f∈H)
      (hn:f∉centralizer (plane V (c.ambientFactor d i).space:Set G)) :
      ∃v∈plane V (c.ambientFactor d i).space,⁅f,v⁆∉D := by
    obtain ⟨z,hz,hzD⟩:=Set.not_subset.mp (hZi i)
    obtain ⟨v,hv,hvz⟩:=hsurj i f hf hn z hz
    exact ⟨v,hv,fun hh=>hzD (hvz ▸ hh)⟩
  have hmove:¬⁅V,H⁆≤D := by
    intro hh
    obtain ⟨f,hf,hn⟩:=Set.not_subset.mp hnH
    have hex:∃i:d.Index,f∉centralizer (plane V (c.ambientFactor d i).space:Set G) := by
      by_contra hn'
      push Not at hn'
      apply hn
      rw [hCV]
      exact ⟨hn' s.first,hn' s.second⟩
    obtain ⟨i,hi⟩:=hex
    obtain ⟨v,hv,hvD⟩:=hnon i f hf hi
    rw [commutator_comm] at hh
    exact hvD (hh (commutator_mem_commutator hf (plane_le _ hv)))
  have hlarge:1<K.relIndex V := by
    have hp:0<K.relIndex V:=Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hn:K.relIndex V≠1 := by
      intro he
      exact hmove ((commutator_mono (relIndex_eq_one.mp he) le_rfl).trans
        (commutator_commutatorPreimage_le Mc H D hMcD))
    omega
  refine ⟨hmove,hlarge,?_⟩
  have hsmall (A B:Subgroup G) (he:centralizer (V:Set G)=A⊓B)
      (hi:B.relIndex H≤2) (hh:H⊓B≤A) : (centralizer (V:Set G)).relIndex H≤K.relIndex V := by
    have hidx:=relIndex_le_of_le_left (le_inf hh (show H⊓B≤B from inf_le_right))
      (show (H⊓B).relIndex H≠0 from index_ne_zero_of_finite)
    rw [inf_relIndex_left,←he] at hidx
    exact (hidx.trans hi).trans (by omega)
  by_cases hc1:H⊓centralizer (V₂:Set G)≤centralizer (V₁:Set G)
  · exact hsmall _ _ hCV hidx₂ hc1
  by_cases hc2:H⊓centralizer (V₁:Set G)≤centralizer (V₂:Set G)
  · exact hsmall _ _ (hCV.trans (inf_comm _ _)) hidx₁ hc2
  obtain ⟨f₁,hf₁,hf₁n⟩:=Set.not_subset.mp hc1
  obtain ⟨f₂,hf₂,hf₂n⟩:=Set.not_subset.mp hc2
  let C₁:=V₁⊓commutatorPreimage Mc (zpowers f₁) D
  let C₂:=V₂⊓commutatorPreimage Mc (zpowers f₂) D
  have hCproper (i:d.Index) (f:G) (hf:f∈H)
      (hn:f∉centralizer (plane V (c.ambientFactor d i).space:Set G)) :
      ¬plane V (c.ambientFactor d i).space≤commutatorPreimage Mc (zpowers f) D := by
    intro hh
    obtain ⟨v,hv,hvD⟩:=hnon i f hf hn
    apply hvD
    rw [←commutatorElement_inv]
    exact D.inv_mem (commutator_commutatorPreimage_le Mc (zpowers f) D hMcD
      (commutator_mem_commutator (hh hv) (mem_zpowers f)))
  have hc₁:Nat.card C₁≤8:=proper_subgroup_card_le_half C₁ V₁ inf_le_left
    (fun hh=>hCproper s.first f₁ hf₁.1 hf₁n (hh.trans inf_le_right)) (s.support_card s.first)
  have hc₂:Nat.card C₂≤8:=proper_subgroup_card_le_half C₂ V₂ inf_le_left
    (fun hh=>hCproper s.second f₂ hf₂.1 hf₂n (hh.trans inf_le_right)) (s.support_card s.second)
  have hcommU (f:G) (hf:f∈H) (v:G) (hv:v∈K):⁅f,v⁆∈D := by
    rw [←commutatorElement_inv]
    exact D.inv_mem (commutator_commutatorPreimage_le Mc H D hMcD (commutator_mem_commutator hv hf))
  have hpre (f:G) (hf:f∈H) (v:G) (hv:v∈V) (hh:⁅f,v⁆∈D):
      v∈commutatorPreimage Mc (zpowers f) D := by
    have hVMc:V≤Mc := (V.le_centralizer.trans
      (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))).trans hCMc
    let : (D.subgroupOf Mc).Normal:=normal_subgroupOf_of_le_normalizer hMcD
    let q:=QuotientGroup.mk' (D.subgroupOf Mc)
    let v₀:Mc:=⟨v,hVMc hv⟩
    let f₀:Mc:=⟨f,hTMc (hHT hf)⟩
    have hvD:⁅v,f⁆∈D := by rw [←commutatorElement_inv];exact D.inv_mem hh
    have hc:Commute (q v₀) (q f₀) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hvD
    apply le_commutatorPreimage (zpowers_le.mpr (hVMc hv)) ?_ (mem_zpowers v)
    apply commutator_le.mpr
    intro a ha b hb
    obtain ⟨m,rfl⟩:=ha
    obtain ⟨n,rfl⟩:=hb
    have he:q ⁅v₀^m,f₀^n⁆=1 := by
      rw [map_commutatorElement,map_zpow,map_zpow]
      exact (hc.zpow_zpow m n).commutator_eq
    exact (QuotientGroup.eq_one_iff (N:=D.subgroupOf Mc) ⁅v₀^m,f₀^n⁆).mp he
  have hthin:K⊓V≤C₁⊔C₂ := by
    obtain ⟨e,he⟩:=exists_mulEquiv_prod_sup_of_disjoint_of_commuting V₁ V₂
      (disjoint_iff.mpr s.disjoint) ((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _))))
    intro v hv
    obtain ⟨⟨a,b⟩,hab⟩:=e.surjective ⟨v,s.complement.symm ▸ hv.2⟩
    have hab':(a:G)*(b:G)=v := (he a b).symm.trans (congrArg Subtype.val hab)
    have haD:⁅f₁,(a:G)⁆∈D := by
      have hh:=hcommU f₁ hf₁.1 v hv.1
      rw [←hab',commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr (hf₁.2 b b.property).symm,mul_one,mul_inv_cancel_right] at hh
      exact hh
    have hbD:⁅f₂,(b:G)⁆∈D := by
      have hab'':(b:G)*(a:G)=v := (V.le_centralizer (plane_le _ a.property) b (plane_le _ b.property)).trans hab'
      have hh:=hcommU f₂ hf₂.1 v hv.1
      rw [←hab'',commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr (hf₂.2 a a.property).symm,mul_one,mul_inv_cancel_right] at hh
      exact hh
    rw [←hab']
    exact mul_mem_sup ⟨a.property,hpre f₁ hf₁.1 a (plane_le _ a.property) haD⟩
      ⟨b.property,hpre f₂ hf₂.1 b (plane_le _ b.property) hbD⟩
  have hdis:Disjoint C₁ C₂:=(disjoint_iff.mpr s.disjoint).mono inf_le_left inf_le_left
  have hnorm:C₂≤normalizer (C₁:Set G):=
    (inf_le_left.trans (plane_le _) |>.trans (V.le_centralizer.trans
      (centralizer_le (inf_le_left.trans (plane_le _))))).trans (Subgroup.centralizer_le_normalizer _)
  have hcK:Nat.card (K⊓V:Subgroup G)≤64 := (card_le_of_le hthin).trans (by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hnorm hdis]
    exact Nat.mul_le_mul hc₁ hc₂)
  have hcV:Nat.card V=256 := by
    rw [←s.complement,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (((plane_le _).trans (V.le_centralizer.trans (centralizer_le (plane_le _)))).trans
        (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr s.disjoint),s.support_card,s.support_card]
  have hc:=relIndex_mul_card_of_le (show K⊓V≤V from inf_le_right)
  rw [inf_relIndex_right,hcV] at hc
  have hfour:4≤K.relIndex V:=by nlinarith
  exact hupper.trans hfour

end CFSG.Quasithin.Chapter15.Section01
