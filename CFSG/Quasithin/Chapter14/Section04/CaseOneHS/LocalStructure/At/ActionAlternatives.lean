module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Terminal

/-!
# The earlier HS action alternatives at G,T

Apply the genuine marked representation classification to the original
action. The half-degree and point-centralizer rank bounds exclude the
exchanged and exceptional rows; the four-space parabolic calculation
retains exactly the literal natural-coordinate and whole-component
alternatives needed downstream. Centerlessness is used only by the
explicitly conditional later-action deductions.
Source: Aschbacher--Smith 14.3.23--24,32 and G.11, pp.999--1004,363--370.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/NonsolvableFive.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_symmetricFive_marked_center_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nat.card (dotImage F F.uhatAction (conjugate F.ZU g)) = 2 ∧
      dotImage F F.uhatAction (conjugate F.ZU g) ≤ solvableResidual (Hdot F F.uhatAction) := by
  let := chosen.elementary
  obtain ⟨_,hX,B,v,hyp,hline,hfix⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let : IsElementaryAbelian 2 (F.terminalDot (F.X g)) := hX
  obtain ⟨_,hE,_,_⟩ := source_four_marked_geometry_at d earlier hq chosen structural alternatives
    F hne hd g hgP hgH
  let S := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXS,hXN⟩ := source_earlier_actor_normal_in_sylow_at d earlier hq chosen structural alternatives
    F hne g hgP hgH
  have hSN : (S : Subgroup F.TerminalHdot) ≤
      normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) :=
    (normal_subgroupOf_iff_le_normalizer hXS).mp hXN
  have hSU : ∀ s ∈ S, ∀ w ∈ hatSpace F V, F.terminalRepresentation s w ∈ hatSpace F V := by
    rintro s ⟨a,ha,rfl⟩ w ⟨u,hu,heu⟩
    have hn : (a:G) ∈ normalizer (V : Set G) := by
      have hh : (a : G) ∈ normalizer (F.Vi 3 : Set G) := F.invariant 3 ha
      rwa [F.last] at hh
    refine ⟨F.uAction a u,(mem_normalizer_iff.mp hn (u:G)).mp hu,?_⟩
    change QuotientGroup.mk' (center F.U) (F.uAction a u) = F.uhatAction a w.toMul
    rw [←F.uhatAction_apply_mk,heu]
  have hnot : ¬ hatSpace F V ≤ BinaryOffender.fixedSpace F.terminalRepresentation
      (F.terminalDot (F.X g)) := by
    intro hh
    have he := congrArg (fun W : Submodule (ZMod 2) (Additive F.Uhat) => finrank (ZMod 2) W) hyp.fixedSpace_in_W
    rw [hE,inf_eq_left.mpr hh,seed_hat_dimension F
      (source_closure_at d earlier hq chosen structural alternatives F hne).2.2,
      finrank_span_singleton hyp.point_ne_zero] at he
    omega
  obtain ⟨e⟩ := model
  exact Theory.SpecificGroups.SymmetricFive.marked_plane_kernel (D := F.TerminalHdot)
    e F.terminalRepresentation
    (hatSpace F V) S (F.terminalDot (F.X g)) (F.terminalDot (conjugate F.ZU g))
    hXS hSN hSU (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
    (source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH)
    (source_conjugate_center_fixes_seed chosen F g hgP) hnot
theorem source_nonsolvable_five_seed_row_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : NonsolvableSeedRow F g := by
  obtain ⟨e⟩ := model
  have hm : (solvableResidual (Hdot F F.uhatAction)).map e.toMonoidHom =
      solvableResidual (Equiv.Perm (Fin 5)) := map_solvableResidual_eq _ e.surjective
  let r := (e.subgroupMap (solvableResidual (Hdot F F.uhatAction))).trans (MulEquiv.subgroupCongr hm)
  let := Theory.SpecificGroups.SymmetricFive.WreathComponents.symmetric_residual_quasisimple
  have hc : Nat.card (solvableResidual (Hdot F F.uhatAction)) = 60 := by
    rw [Nat.card_congr r.toEquiv,Theory.SpecificGroups.SymmetricFive.WreathComponents.symmetric_residual,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  refine ⟨IsQuasisimple.of_mulEquiv r.symm,?_,.inl hc,?_⟩
  · exact binary_four_irreducible_of_five_dvd
      (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
      (F.terminalRepresentation_injective.comp (solvableResidual F.TerminalHdot).subtype_injective)
      hd (by
        change 5 ∣ Nat.card (solvableResidual (Hdot F F.uhatAction))
        rw [hc]
        decide)
  · intro _
    exact (source_symmetricFive_marked_center_at d earlier hq chosen structural alternatives
      F hne hZ hd ⟨e⟩ g hgP hgH).symm
theorem source_seed_exclusion_of_five_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5))) : centralLTSeed F L = ⊥ := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide)
      (show 2^4 = 2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  obtain ⟨g,hgP,hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  exact source_seed_exclusion_of_dotted_row_at d earlier hq chosen structural alternatives
    classification F hne g hgP hgH
    (source_nonsolvable_five_seed_row_at d earlier hq chosen structural alternatives
      F hne hZ hd model g hgP hgH)
theorem source_centerless_of_symmetricFive_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ :=
  source_centerless_of_symmetricFive_at d earlier hq chosen structural alternatives F hne
    (source_seed_exclusion_of_five_model_at d earlier hq chosen structural alternatives
      classification F hne hZ hc model) model
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/PointRanks.lean. -/
section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_tilde_plane_three_rank_le_one_at
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    primeRank 3 F.terminalTildePlaneCentralizer ≤ 1 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := CaseOneLarge.source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨e,_,_,_,hIG,hIN,_,_,_,_,hIC,_⟩ := F.binary_generation (by decide) L
    chosen.normalizes (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
    hcomm hsquare hspan hne g hgP hgH
  exact F.lemma_12_8_13_eight d.qtke.quasithin (by decide) L hIG hIN hIC ⟨e⟩
theorem source_center_centralizing_kernel_le_core_at :
    (centralizer (F.ZU : Set G)).subgroupOf F.H ⊓ F.terminalHatAction.ker ≤ pCore 2 F.H := by
  let := chosen.elementary
  let c := CaseOneLarge.source_closure_geometry_at F d earlier hq chosen structural alternatives hne
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
theorem source_point_preimage_centralizes_plane_of_cube_one_at (a : F.H)
    (ha : QuotientGroup.mk' F.terminalHatAction.ker a ∈
      ChapterG.Section10.pointCentralizer F.terminalRepresentation v)
    (haZ : (a:G) ∈ centralizer (F.ZU : Set G)) (ha3 : a ^ 3 = 1) :
    (a:G) ∈ centralizer (F.Vi 2 : Set G) := by
  let := chosen.elementary
  let closureData := CaseOneLarge.source_closure_geometry_at F d earlier hq chosen structural alternatives hne
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
theorem source_center_centralizing_point_lift_three_rank_le_one_at
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
    have hc := source_point_preimage_centralizes_plane_of_cube_one_at d earlier hq chosen structural alternatives F hne v hline e.val.val
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
    (source_tilde_plane_three_rank_le_one_at d earlier hq chosen structural alternatives F hne g hgP hgH)
  let : IsElementaryAbelian 3 (⊤ : Subgroup E) := IsElementaryAbelian.of_injective
    (⊤ : Subgroup E).subtype (⊤ : Subgroup E).subtype_injective
  simpa only [card_top] using (primeRank_le_iff_elementary_card_le E).mp hr
    (⊤ : Subgroup E) inferInstance
theorem source_center_centralizing_point_image_three_rank_le_one_at
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
    apply source_center_centralizing_kernel_le_core_at d earlier hq chosen structural alternatives F hne
    refine ⟨a.property.2,?_⟩
    exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun z : D => z.val.val) ha)
  have hp : IsPGroup 2 f.ker :=
    (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf P)).to_le hk
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (primeRank_le_of_surjective_of_coprime 3 f hf hcop).trans
    (source_center_centralizing_point_lift_three_rank_le_one_at d earlier hq chosen structural alternatives F hne v hline g hgP hgH)
end Marked
theorem source_simple_normal_le_center_centralizer_at
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
      ((source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).1.trans hI).le
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
    apply source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH
    exact le_bot_iff.mp ((map_mono (comap_mono (le_conjugateSpanBy _ _))).trans he.le)
  exact (simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot K hKa hKc _ hN).trans
    (map_mono (comap_mono hNC))
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/EarlierClassification.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_earlier_center_le_section_centralizer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) ≤ Xdot₀ F F.terminalHatAction g := by
  let := chosen.elementary
  obtain ⟨htwo,hphi,hvc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm,_⟩ := CaseOneLarge.source_commutator_squares_at d earlier hq chosen structural alternatives F
  let C := F.localKernel_markedForm (by decide) htwo hphi hcomm
  have hb := F.center_commutator_le_plane (by decide) L chosen.normalizes hvc hcomm
    (F.plane_centralizer_center C) g hgP hgH
  rw [commutator_comm] at hb
  rintro x ⟨a,ha,rfl⟩
  exact mem_Xdot₀_of_displacement F F.terminalHatAction F.terminalHatAction_apply_mk g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) a (F.conjugate_ZU_le_X g ha)
    (fun w hw => hb (commutator_mem_commutator ha hw))
theorem source_earlier_lowRank_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let := chosen.elementary
  have hsec : Xdot₀ F F.terminalHatAction g ≠ ⊥ := by
    intro he
    exact source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH
      (le_bot_iff.mp (he ▸ source_earlier_center_le_section_centralizer_at d earlier hq chosen
        structural alternatives F hne g hgP hgH))
  obtain ⟨htwo,hphi,hvc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm,_⟩ := CaseOneLarge.source_commutator_squares_at d earlier hq chosen structural alternatives F
  let C := F.localKernel_markedForm (by decide) htwo hphi hcomm
  have hzero (a b : F.U) : C.form (hatElement F a) (hatElement F b) = 0 ↔ Commute a b := by
    rw [show C.form (hatElement F a) (hatElement F b) =
      (C.valueEquiv ⟨⁅(a:G),(b:G)⁆,hcomm (commutator_mem_commutator a.property b.property)⟩).toAdd
        from C.evaluation a b]
    change C.valueEquiv _ = 1 ↔ _
    rw [map_eq_one_iff C.valueEquiv C.valueEquiv.injective,Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm.trans (by
      change (a:G)*(b:G)=(b:G)*(a:G) ↔ a*b=b*a
      exact ⟨fun he => Subtype.ext he, fun he => congrArg (fun t : F.U => (t:G)) he⟩)
  have hi : ∀ (a : F.H) (u w : F.Uhat),
      C.form (Additive.ofMul (F.terminalHatAction a u)) (Additive.ofMul (F.terminalHatAction a w)) =
        C.form (Additive.ofMul u) (Additive.ofMul w) := by
    intro a u w
    change F.uhatBilinearForm (by decide) htwo hphi
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a w)) = _
    rw [F.uhatBilinearForm_apply,F.uhatCommutator_invariant (by decide) htwo hphi]
    rfl
  obtain ⟨x,hx,_,hr,hm⟩ := exists_lowRank_of_Xdot₀_ne_bot F (by decide) hvc
    F.terminalHatAction g C.form C.nondegenerate C.alternating hzero hi hsec
  exact ⟨x,hx,hr,hm (hline ▸ Submodule.mem_span_singleton_self v)⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/FullLinearExclusion.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem fullLinearExclusion_source_seed_stable_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (a : F.H) (ha : (a:G) ∈ normalizer (V : Set G)) (w : Additive F.Uhat)
    (hw : w ∈ hatSpace F V) :
    F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w ∈ hatSpace F V := by
  obtain ⟨b,hb,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction a b, (mem_normalizer_iff.mp ha (b:G)).mp hb, ?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.terminalHatAction a w.toMul
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.uhatAction a w.toMul
  rw [← F.uhatAction_apply_mk,he]
theorem source_seed_point_moved_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    ∃ k ∈ F.terminalDot (F.Li L 1), F.terminalRepresentation k v ≠ v := by
  let := chosen.elementary
  obtain ⟨hspan,_,hcenter⟩ := source_seed_geometry_at d earlier hq chosen F
  have hc := hcenter hne
  by_contra! hfix
  have hn : F.Li L 1 ≤ normalizer (F.Vi 2 : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk b hb
    let a : F.H := ⟨k,(F.Li_le L 1 hk).2⟩
    let bU : F.U := ⟨b,(F.le_seed 2).trans (le_conjugateSpanBy _ _) hb⟩
    let q := QuotientGroup.mk' (center F.U)
    have hbline : Additive.ofMul (q bU) ∈ Submodule.span (ZMod 2) {v} :=
      hline ▸ (show Additive.ofMul (q bU) ∈ hatSpace F (F.Vi 2) from ⟨bU,hb,rfl⟩)
    obtain ⟨c,hcb⟩ := Submodule.mem_span_singleton.mp hbline
    have hkdot : QuotientGroup.mk' F.terminalHatAction.ker a ∈ F.terminalDot (F.Li L 1) :=
      ⟨a,hk,rfl⟩
    have hq : F.terminalHatAction a (q bU) = q bU := by
      have he : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
          (Additive.ofMul (q bU)) = Additive.ofMul (q bU) := by
        rw [← hcb,map_smul,hfix _ hkdot]
      exact congrArg Additive.toMul he
    have hz : F.uAction a bU * bU⁻¹ ∈ center F.U := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (_ * _) = 1
      rw [map_mul,map_inv,← F.uhatAction_apply_mk]
      change F.terminalHatAction a (q bU) * (q bU)⁻¹ = 1
      rw [hq,mul_inv_cancel]
    have hbV := F.le_seed 2 hb
    have hkV := chosen.normalizes (F.Li_le L 1 hk).1
    have hzV : k*b*k⁻¹*b⁻¹ ∈ V :=
      V.mul_mem ((mem_normalizer_iff.mp hkV b).mp hbV) (V.inv_mem hbV)
    have hzZ : k*b*k⁻¹*b⁻¹ ∈ F.ZU := mem_map_of_mem F.U.subtype hz
    have hz1 : k*b*k⁻¹*b⁻¹ ∈ F.Vi 1 := hc ▸ ⟨hzV,hzZ⟩
    have he := (F.Vi 2).mul_mem (F.monotone (by decide : 1 ≤ 2) hz1) hb
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using he
  have hle : V ≤ F.Vi 2 := hspan.ge.trans (conjugateSpanBy_le le_rfl hn)
  have hh := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hcV : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [hcV,F.card 2 (by decide)] at hh
  norm_num at hh
theorem source_no_full_linear_model_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (H : Subgroup F.TerminalHdot) (I J : Submodule (ZMod 2) (Additive F.Uhat)) :
    ¬ Nonempty (ChapterG.Section11.FullLinearFour.WholeActionModel F.terminalRepresentation H I J) := by
  rintro ⟨m⟩
  let := chosen.elementary
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hP : (P : Subgroup F.TerminalHdot) = F.terminalDot (T : Subgroup G) := rfl
  have hs : ∀ a ∈ P, ∀ w ∈ hatSpace F V, F.terminalRepresentation a w ∈ hatSpace F V := by
    intro a ha w hw
    obtain ⟨b,hb,rfl⟩ := (show a ∈ F.terminalDot (T : Subgroup G) from hP ▸ ha)
    apply fullLinearExclusion_source_seed_stable_at F b _ w hw
    have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
      simpa only [F.last] using F.invariant 3
    exact hTV hb
  have hseed : hatSpace F (F.Vi 2) ≤ hatSpace F V := fun _ hw =>
    (show hatImage F (F.Vi 2) ≤ hatImage F V from map_mono (comap_mono (F.le_seed 2))) hw
  have hv : v ∈ hatSpace F V := hseed (hline ▸ Submodule.mem_span_singleton_self v)
  obtain ⟨k,hk,hm⟩ := source_seed_point_moved_at d earlier hq chosen F hne v hline
  apply hm
  apply BinaryNaturalDual.FourSeed.point_fixed_of_coordinates F.terminalRepresentation
    (BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl rfl))
    m.groupEquiv m.spaceEquiv m.equivariant P (hatSpace F V)
    (seed_hat_dimension F (source_closure_at d earlier hq chosen structural alternatives F hne).2.2)
    hs v hv (fun a ha => hfix a (hP ▸ ha)) k
  intro w hw
  obtain ⟨b,hb,rfl⟩ := hk
  exact fullLinearExclusion_source_seed_stable_at F b (chosen.normalizes (F.Li_le L 1 hb).1) w hw
theorem source_no_full_linear_alternative_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat)) (X : Subgroup F.TerminalHdot)
    (X₀ : Subgroup X) :
    ¬ ChapterG.Section11.FullLinearFour.MarkedAlternative F.terminalRepresentation B v W X X₀ := by
  rintro ⟨H,I,J,m,_⟩
  exact source_no_full_linear_model_at d earlier hq chosen structural alternatives F hne H I J ⟨m⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/ExchangedNatural.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_earlier_whole_component_reduction_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hcover,hn,_⟩ :=
    source_earlier_classification_input_at d earlier hq chosen structural alternatives F hne g hgP hgH
  let := heU
  let := heX
  have hw := source_earlier_lowRank_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH v hline
  have hlarge := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases corrected_conclusion_or_remaining hyp hcover hw hn with (hc | hex) | ⟨hi,hd,hs | ⟨hnon,hrem⟩⟩
  · exact Or.inl hc
  · exact (source_no_full_linear_alternative_at d earlier hq chosen structural alternatives F hne
      B v _ _ _ hex).elim
  · obtain ⟨_,hr,hd⟩ := hs
    omega
  · exact Or.inr ⟨hi,hd,hnon,whole_of_remaining_of_large hyp hcover hw hn hnon hlarge hrem⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/CatalogueReduction.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_earlier_remaining_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((CaseTwo F.terminalRepresentation B ∨ CaseFour F.terminalRepresentation ∨
          CaseFive F.terminalRepresentation B ∨ CaseSix F.terminalRepresentation) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_earlier_whole_component_reduction_at d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with hc | hwhole
  · left
    let := chosen.elementary
    obtain ⟨htwo,hphi,hvc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
    exact LargeActorCatalogue.remaining_rows
      (source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
        F g hne hZ hgP hgH) hyp (CaseOneLarge.source_terminal_cover F d chosen) hw
      (quotient_dimension F htwo hphi hvc).1 hc
  · obtain ⟨hi,hd,hnon,J,hJ,hm,horth,h9⟩ := hwhole
    exact .inr ⟨hi,hd,hnon,J,hJ,hm,horth,h9,
      WholeComponentCandidates.component_candidates hyp h9 hw hd
        (source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
          F g hne hZ hgP hgH)⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/CatalogueExclusions.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
include d earlier hq chosen structural alternatives hne hZ
theorem source_no_caseFour_at : ¬ CaseFour F.terminalRepresentation := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  exact not_caseFour_of_smaller_ne_bot hyp
    (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
    (source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH)
theorem source_no_caseFive_at (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) :
    ¬ CaseFive F.terminalRepresentation B := by
  intro h5
  obtain ⟨q,c,K,hKn,hKc,e,he⟩ := SplitSix.caseFive_selfcentralizing_marking h5
  let := hKn
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp : 5 ≤ Nat.card (Fin 8))
  let : IsSimpleGroup K := e.isSimpleGroup
  have hKa : ¬ IsMulCommutative K := by
    intro hc
    let := hc
    let : Group.IsPerfect (alternatingGroup (Fin 8)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 8))
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  have hKC := source_simple_normal_le_center_centralizer_at d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH K hKa hKc
  obtain ⟨heU,heX,B',v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hr : 2 ≤ primeRank 3 (C.subgroupOf K) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp K.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c.toLinearEquiv he v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let f : C.subgroupOf K →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hKC a.val.property⟩,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C.subgroupOf D => z.val.val) he))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hu := source_center_centralizing_point_image_three_rank_le_one_at d earlier hq chosen
    structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  omega
section
open ChapterG.Section11.ExchangedRecognition
omit d earlier hq chosen structural alternatives hne hZ
omit [IsElementaryAbelian 2 F.Uhat]
theorem source_remaining_action_of_centerless_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((CaseTwo F.terminalRepresentation B ∨ CaseSix F.terminalRepresentation) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_earlier_remaining_action_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with h2 | hwhole
  · left
    rcases h2 with h2 | h4 | h5 | h6
    · exact .inl h2
    · exact (source_no_caseFour_at d earlier hq chosen structural alternatives F hne hZ h4).elim
    · exact (source_no_caseFive_at d earlier hq chosen structural alternatives F hne hZ hI B h5).elim
    · exact .inr h6
  · exact .inr hwhole
end
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/Orders.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_intersection_card_le_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (r : ℕ) (hc : Nat.card F.Uhat = 2 ^ (2 * r))
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : Nat.card (F.E g) ≤ 2 ^ (r + 1) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hVZ⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let B := F.uhatBilinearForm (by decide) htwo hphi
  have hpU : F.Vi 1 ≤ F.U := (F.le_seed 1).trans (le_conjugateSpanBy V F.H)
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi, map_subgroupOf_eq_of_le hpU]
  have hgV := F.P_le_seed_normalizer L chosen.normalizes hgP
  have hdis := disjoint_iff.mpr (F.conjugate_point_inf_ZU (by decide) hVZ g hgV hgH)
  let : IsElementaryAbelian 2 (F.E g) := F.E_elementary (by decide) g htwo hPhi hdis
  have hi : ∀ x ∈ hatSpace F (F.E g), ∀ y ∈ hatSpace F (F.E g), B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, hea⟩ := (show x.toMul ∈ hatImage F (F.E g) from hx)
    obtain ⟨b, hb, heb⟩ := (show y.toMul ∈ hatImage F (F.E g) from hy)
    have hab : Commute a b := by
      apply Subtype.ext
      exact congrArg (fun v : F.E g => (v : G))
        (mul_comm (⟨a, ha⟩ : F.E g) ⟨b, hb⟩)
    have hz : F.uhatCommutator htwo (QuotientGroup.mk' (center F.U) a)
        (QuotientGroup.mk' (center F.U) b) = 1 := by
      apply Subtype.ext
      rw [F.uhatCommutator_apply_mk]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hab.eq
    change B (Additive.ofMul x.toMul) (Additive.ofMul y.toMul) = 0
    rw [← hea, ← heb, F.uhatBilinearForm_apply, hz]
    simp only [map_one]
    rfl
  have hb := B.twice_finrank_le_of_isotropic
    (F.uhatBilinearForm_nondegenerate (by decide) htwo hphi) (hatSpace F (F.E g)) hi
  have hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * r := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    rw [Nat.card_zmod] at hh
    have hh' : 2 ^ (2 * r) = 2 ^ Module.finrank (ZMod 2) (Additive F.Uhat) :=
      hc.symm.trans hh
    exact (Nat.pow_right_injective (by decide) hh').symm
  rw [hd] at hb
  have hVE := F.seed_le_E_of_normalizes g hgV
  have hEU : F.E g ≤ F.U := inf_le_left.trans inf_le_left
  have hEH := (hatMap F (F.E g) hEU).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (hatMap_surjective F (F.E g) hEU), card_top] at hEH
  have hk : (hatMap F (F.E g) hEU).ker =
      (F.Vi 1).subgroupOf (F.E g) := by
    rw [hatMap_ker]
    ext x
    change (x : G) ∈ F.ZU ↔ (x : G) ∈ F.Vi 1
    constructor
    · intro hz
      have hzu := (source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
      rw [hI, bot_sup_eq] at hzu
      rw [← hzu]
      exact ⟨hz, (map_mono (show F.W ≤ F.U from inf_le_left)) x.property.2⟩
    · intro hv
      exact (show F.Vi 1 ≤ F.ZU from hVZ ▸ inf_le_right) hv
  have hkc : Nat.card (hatMap F (F.E g) hEU).ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe ((F.le_seed 1).trans hVE)).toEquiv]
    simpa using F.card 1 (by decide)
  rw [hkc] at hEH
  have himg : Nat.card (hatImage F (F.E g)) ≤ 2 ^ r := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := hatSpace F (F.E g))
    rw [Nat.card_zmod] at hh
    change Nat.card (hatSpace F (F.E g)) ≤ 2 ^ r
    rw [hh]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  rw [pow_succ]
  omega
theorem source_intersection_eq_seed_of_card_sixteen_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : F.E g = V := by
  let := chosen.elementary
  have hb := source_intersection_card_le_at d earlier hq chosen structural alternatives F hne hI
    2 hc g hgP hgH
  have hVE := F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L chosen.normalizes hgP)
  have hvc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  exact (eq_of_le_of_card_ge hVE (by simpa [hvc] using hb)).symm
theorem source_actor_order_identity_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    2 * Nat.card (F.E g) * Nat.card (dotImage F F.uhatAction (F.X g)) =
      Nat.card F.Uhat * Nat.card (center F.U) := by
  let := chosen.elementary
  have ha := source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH
  have hXH := F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
  have hk : (dotMap F F.uhatAction (F.X g) hXH).ker = (F.E g).subgroupOf (F.X g) := by
    rw [dotMap_ker]
    change (F.xHatAction g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)).ker = _
    rw [← ha.2.1]
    exact (comap_map_eq_self_of_injective (F.X g).subtype_injective _).symm
  have hXc := (dotMap F F.uhatAction (F.X g) hXH).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (dotMap_surjective F F.uhatAction (F.X g) hXH),
    card_top, hk, Nat.card_congr (subgroupOfEquivOfLe (show F.E g ≤ F.X g from inf_le_right)).toEquiv] at hXc
  have hWc := (F.W.subgroupOf F.U).index_mul_card
  rw [show (F.W.subgroupOf F.U).index = F.W.relIndex F.U from rfl,
    ha.2.2.2, Nat.card_congr (subgroupOfEquivOfLe (show F.W ≤ F.U from inf_le_left)).toEquiv] at hWc
  have hXW : Nat.card (F.X g) = Nat.card F.W :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  rw [mul_assoc, hXc, hXW, hWc]
  exact (center F.U).card_eq_card_quotient_mul_card_subgroup
theorem source_center_card_ge_four_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) : 4 ≤ Nat.card (center F.U) := by
  have hn := source_conjugate_center_image_nontrivial_at d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH
  have ho := source_conjugate_center_image_order_at d earlier hq chosen structural alternatives
    F hne hI g hgP hgH
  have hcard := Nat.card_pos (α := (F.uhatAction.comp
    (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range)
  have hneone : Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≠ 1 := by
    intro he
    exact hn ((Subgroup.card_eq_one).mp he)
  omega
theorem source_actor_order_eq_center_of_card_sixteen_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nat.card (dotImage F F.uhatAction (F.X g)) = Nat.card (center F.U) := by
  have he := source_intersection_eq_seed_of_card_sixteen_at d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hi := source_actor_order_identity_at d earlier hq chosen structural alternatives F hne g hgP hgH
  have hvc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  rw [he, hvc, hc] at hi
  omega
theorem source_six_dimensional_orders_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 64)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hX : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 8) :
    Nat.card (F.E g) = 16 ∧ Nat.card (center F.U) = 4 ∧
      Nat.card (dotImage F F.uhatAction (F.X g)) = 8 := by
  have he := source_intersection_card_le_at d earlier hq chosen structural alternatives F hne hI
    3 hc g hgP hgH
  have hz := source_center_card_ge_four_at d earlier hq chosen structural alternatives F hne hZ hI g hgP hgH
  have hi := source_actor_order_identity_at d earlier hq chosen structural alternatives F hne g hgP hgH
  rw [hc] at hi
  norm_num at he
  have hb := Nat.mul_le_mul he hX
  have hzc : Nat.card (center F.U) = 4 := by nlinarith
  have hec : Nat.card (F.E g) = 16 := by
    have hb := Nat.mul_le_mul_left (Nat.card (F.E g)) hX
    nlinarith
  exact ⟨hec, hzc, by rw [hec, hzc] at hi; omega⟩
theorem source_actor_elementary_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    IsElementaryAbelian 2 (dotImage F F.uhatAction (F.X g)) := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  obtain ⟨⟨hn, he⟩, _⟩ := source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH
  let := hn
  let := he
  exact Xdot_uhatAction_elementary F g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
theorem source_four_dimensional_orders_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hX : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 4) :
    F.E g = V ∧ Nat.card (center F.U) = 4 ∧
      Nat.card (dotImage F F.uhatAction (F.X g)) = 4 ∧ Nat.card (F.tilde F.ZU) = 2 := by
  have he := source_intersection_eq_seed_of_card_sixteen_at d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hxc := source_actor_order_eq_center_of_card_sixteen_at d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hz := source_center_card_ge_four_at d earlier hq chosen structural alternatives F hne hZ hI g hgP hgH
  have hzc : Nat.card (center F.U) = 4 := by omega
  obtain ⟨e⟩ := source_conjugate_center_image_equiv_at d earlier hq chosen structural alternatives F hne hI g hgP hgH
  have ho := source_conjugate_center_image_order_at d earlier hq chosen structural alternatives F hne hI g hgP hgH
  rw [Nat.card_congr e.toEquiv, hzc] at ho
  exact ⟨he, hzc, by omega, by omega⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/SolvableExclusion.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem solvableExclusion_binary_derived_fixed_at (v : BinaryLinear.OuterCyclic.Space 2)
    (hv : ∀ a : commutator (BinaryLinear.OuterCyclic.LinearGroup 2), a.val v = v) : v = 0 := by
  by_contra hn
  have hw : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hw' : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  obtain ⟨a, ha⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero hn hw
  obtain ⟨b, hb⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero hn hw'
  have he := (ha.symm.trans (hv a)).trans ((hv b).symm.trans hb)
  have hf := congrFun he 0
  norm_num at hf
private theorem solvableExclusion_normal_seed_fixed_at [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 (F.tilde V)]
    [IsElementaryAbelian 2 (F.tilde F.U)]
    (hLV : L ≤ normalizer (V : Set G)) (A : AmbientNaturalMarking L hLV 3)
    (M : Subgroup G) (hH : F.H ∈ F.Hz L M)
    [((F.Li L 1).subgroupOf F.H).Normal]
    (v : F.tilde (F.UH F.H))
    (hv : ∀ k : F.Li L 1,
      F.localTildeAction F.H le_rfl ⟨k, (F.Li_le L 1 k.property).2⟩ v = v) : v = 1 := by
  let : IsElementaryAbelian 2 (F.tilde (F.UH F.H)) :=
    inferInstanceAs (IsElementaryAbelian 2 (F.tilde F.U))
  obtain ⟨D, r, e, _, he, _⟩ :=
    F.homogeneous_natural_decomposition_of_ambient (by decide) (by decide) L hLV A hH
  have hz : e (Additive.ofMul v) = 0 := by
    funext i
    apply D.coordinates.injective
    change D.coordinates (e (Additive.ofMul v) i) = D.coordinates 0
    rw [map_zero]
    apply solvableExclusion_binary_derived_fixed_at
    intro a
    obtain ⟨q, hq⟩ := D.quotientEquiv.surjective a
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
    have hh := he k (Additive.ofMul v) i
    change e (Additive.ofMul (F.localTildeAction F.H le_rfl
      ⟨k, (F.Li_le L 1 k.property).2⟩ v)) i = _ at hh
    rw [hv k] at hh
    have hc := congrArg D.coordinates hh
    change D.coordinates (e (Additive.ofMul v) i) =
      D.coordinates (F.localSeedRepresentation L hLV k (e (Additive.ofMul v) i)) at hc
    rw [D.equivariant, hq] at hc
    exact hc.symm
  exact congrArg Additive.toMul (e.injective (hz.trans e.map_zero.symm))
omit [Finite G] in
private theorem solvableExclusion_fixed_tilded_center_at [IsMulCommutative V]
    (F : InvariantFlag T V 3) (hcard : Nat.card (F.tilde F.ZU) = 2) :
    ∃ v : F.tilde F.U, v ≠ 1 ∧ ∀ h : F.H, F.localTildeAction F.H le_rfl h v = v := by
  obtain ⟨z, hz, hu⟩ := (Nat.card_eq_two_iff' (1 : F.tilde F.ZU)).mp hcard
  have hZU : F.ZU ≤ F.U := map_subtype_le _
  have htilde : F.tilde F.ZU ≤ F.tilde F.U := map_mono (fun _ hx => hZU hx)
  let v : F.tilde F.U := ⟨z, htilde z.property⟩
  refine ⟨v, ?_, ?_⟩
  · intro he
    apply hz
    apply Subtype.ext
    exact congrArg (fun x : F.tilde F.U => (x : F.G₁tilde)) he
  · intro h
    let a := F.tildeAction F.H F.ZU le_rfl F.H_normalizes_ZU h
    have ha : a z ≠ 1 := fun he => hz (a.injective (he.trans a.map_one.symm))
    have he : a z = z := hu _ ha
    apply Subtype.ext
    exact congrArg (fun x : F.tilde F.ZU => (x : F.G₁tilde)) he
theorem source_normal_Li_one_exclusion_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hcard : Nat.card (F.tilde F.ZU) = 2) :
    ¬ ((F.Li L 1).subgroupOf F.H).Normal := by
  intro hn
  let := chosen.elementary
  let := hn
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, hphi, _⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.tilde_elementary_of_point htwo hphi
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨v, hv, hf⟩ := solvableExclusion_fixed_tilded_center_at F hcard
  exact hv (solvableExclusion_normal_seed_fixed_at F chosen.normalizes h.naturalMarking _
    (h.point_mem_Hz_at F alternatives) v (fun k => hf _))
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/SmallCenter.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_small_center_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hZ : Nat.card (F.tilde F.ZU) ≤ 2) : F.uhatAction.ker = pCore 2 F.H := by
  let := chosen.elementary
  have ht := source_action_kernel_at d earlier hq chosen structural alternatives F
  let q := F.tildeToUhat (by decide : 1 ≤ 3)
  have hk : Nat.card q.ker ≤ 2 := by
    rw [show q.ker = (F.tilde F.ZU).subgroupOf (F.tilde F.U) from F.tildeToUhat_ker (by decide)]
    have hle : F.tilde F.ZU ≤ F.tilde F.U := map_mono (comap_mono (map_subtype_le (center F.U)))
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact hZ
  have hf := q.isPGroup_fixingAut_of_kernel_card_le_two hk
  let f : F.uhatAction.ker →* q.fixingAut :=
    ((F.localTildeAction F.H le_rfl).comp F.uhatAction.ker.subtype).codRestrict _ (by
      intro a u
      change q (F.localTildeAction F.H le_rfl (a : F.H) u) = q u
      rw [show q (F.localTildeAction F.H le_rfl (a : F.H) u) =
        F.uhatAction (a : F.H) (q u) from F.tildeToUhat_equivariant (by decide) a u]
      have ha : F.uhatAction (a : F.H) = 1 := a.property
      rw [ha]
      rfl)
  have hfker : f.ker ≤ (pCore 2 F.H).subgroupOf F.uhatAction.ker := by
    intro a ha
    change (a : F.H) ∈ pCore 2 F.H
    rw [← ht]
    exact congrArg Subtype.val ha
  have hp : IsPGroup 2 f.ker :=
    (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf F.uhatAction.ker)).to_le hfker
  have htop := (hf.to_subgroup ⊤).comap_of_ker_isPGroup f hp
  rw [comap_top] at htop
  have hker : IsPGroup 2 F.uhatAction.ker := htop.of_surjective
    (⊤ : Subgroup F.uhatAction.ker).subtype (fun a => ⟨⟨a,mem_top a⟩,rfl⟩)
  exact le_antisymm (le_sSup ⟨inferInstance, hker⟩)
    (F.pCore_le_uhatAction_ker_of_tilde_kernel (by decide) ht)
private theorem smallCenter_source_normal_Li_one_of_dot_normal_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hkernel : F.uhatAction.ker = pCore 2 F.H)
    (hn : (dotImage F F.uhatAction (F.Li L 1)).Normal) :
    ((F.Li L 1).subgroupOf F.H).Normal := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes_at structural)
      ((F.invariant 1).trans (F.Gi 1).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.Gi 1) (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)))
  have hLH : F.Li L 1 ≤ F.H := fun x hx => (F.Li_le L 1 hx).2
  have hperf : IsPPerfect 2 (F.Li L 1) := by
    rw [hres]
    exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
  have hp : IsPPerfect 2 ((F.Li L 1).subgroupOf F.H) := hperf.of_surjective
    (subgroupOfEquivOfLe hLH).symm.toMonoidHom (subgroupOfEquivOfLe hLH).symm.surjective
  let q := QuotientGroup.mk' F.uhatAction.ker
  have hker : q.ker = pCore 2 F.H := (QuotientGroup.ker_mk' _).trans hkernel
  let : (((F.Li L 1).subgroupOf F.H).map q).Normal := hn
  apply normal_of_map_normal_of_pPerfect q _ hp (hker.symm ▸ pCore_isPGroup)
  intro x hx
  have hxQ : (x : G) ∈ F.H.pCoreIn 2 := mem_map_of_mem F.H.subtype (hker ▸ hx)
  have hxT : (x : G) ∈ (T : Subgroup G) := by
    obtain ⟨t, ht, he⟩ := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1)) hxQ
    exact he ▸ ht
  have hxn := hTn hxT
  rw [mem_normalizer_iff] at hxn ⊢
  intro y
  exact hxn (y : G)
theorem source_normal_dot_Li_one_exclusion_of_four_two_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (hr : primeRank 2 (Hdot F F.uhatAction) ≤ 2)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ¬ (dotImage F F.uhatAction (F.Li L 1)).Normal := by
  let := source_actor_elementary_at d earlier hq chosen structural alternatives F hne g hgP hgH
  have hb : Nat.card (dotImage F F.uhatAction (F.X g)) ≤ 4 :=
    (primeRank_le_iff_elementary_card_le (Hdot F F.uhatAction)).mp hr _ inferInstance
  have hz := (source_four_dimensional_orders_at d earlier hq chosen structural alternatives
    F hne hZ hI hc g hgP hgH hb).2.2.2
  have hk := source_small_center_kernel_at d earlier hq chosen structural alternatives F hz.le
  intro hn
  exact source_normal_Li_one_exclusion_at d earlier hq chosen structural alternatives F hne hz
    (smallCenter_source_normal_Li_one_of_dot_normal_at d earlier hq chosen structural F hk hn)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/G2Exclusion.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_point_cube_centralizes_conjugate_center_at
    (v : Additive F.Uhat) (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (g : G) (hgP : g ∈ F.P L)
    (hz : Nat.card (F.terminalDot (conjugate F.ZU g)) = 2)
    (a : F.TerminalHdot)
    (ha : a ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v)
    (haZ : a ∈ F.terminalDot (centralizer (F.ZU : Set G))) (ha3 : a^3=1) :
    a ∈ centralizer (F.terminalDot (conjugate F.ZU g) : Set F.TerminalHdot) := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  let D := C.map q
  let f : C →* D := q.subgroupMap C
  have hk : IsPGroup 2 f.ker := by
    have hle : f.ker ≤ (pCore 2 F.H).subgroupOf C := by
      intro x hx
      apply source_center_centralizing_kernel_le_core_at d earlier hq chosen structural alternatives F hne
      exact ⟨x.property,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩
    exact (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf C)).to_le hle
  let aa : D := ⟨a,haZ⟩
  have hao : orderOf aa ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext ha3)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime (Nat.card f.ker) (Nat.card (zpowers aa)) := by
    rw [hn,Nat.card_zpowers]
    exact ((by decide : Nat.Coprime 2 3).pow_left n).coprime_dvd_right hao
  obtain ⟨s,hs⟩ := f.exists_subgroup_section_of_coprime_kernel (q.subgroupMap_surjective C)
    (zpowers aa) hcop
  let b : C := s ⟨aa,mem_zpowers aa⟩
  have hb3 : b^3=1 := by
    rw [← map_pow]
    have hh : (⟨aa,mem_zpowers aa⟩ : zpowers aa)^3=1 := Subtype.ext (Subtype.ext ha3)
    rw [hh,map_one]
  have hba : q b.val = a := by
    have hh : f b = aa := DFunLike.congr_fun hs (⟨aa,mem_zpowers aa⟩ : zpowers aa)
    exact congrArg Subtype.val hh
  have hbplane : (b.val:G) ∈ centralizer (F.Vi 2 : Set G) :=
    source_point_preimage_centralizes_plane_of_cube_one_at d earlier hq chosen structural alternatives
      F hne v hline b.val (hba.symm ▸ ha) b.property (congrArg Subtype.val hb3)
  have hpoint : conjugate (F.Vi 1) g ≤ F.Vi 2 :=
    conjugate_le_of_normalizes (F.monotone (by decide : 1≤2)) g
      (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
  have hn : (b.val:G) ∈ normalizer (conjugate F.ZU g : Set G) := by
    have hHn : conjugate F.H g ≤ normalizer (conjugate F.ZU g : Set G) := by
      simpa only [conjugate,map_equiv_normalizer_eq] using
        map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) F.H_normalizes_ZU
    apply hHn
    change (b.val:G) ∈ (normalizer (F.Vi 1 : Set G)).map (MulAut.conj g⁻¹).toMonoidHom
    rw [map_equiv_normalizer_eq]
    exact Subgroup.centralizer_le_normalizer _ (centralizer_le hpoint hbplane)
  have hnH : b.val ∈ normalizer ((conjugate F.ZU g).subgroupOf F.H : Set F.H) := by
    rw [mem_normalizer_iff] at hn ⊢
    intro x
    exact hn (x:G)
  apply normalizer_le_centralizer_of_card_two _ hz
  rw [← hba]
  exact le_normalizer_map q (mem_map_of_mem q hnH)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_no_caseSix_at (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥) :
    ¬ CaseSix F.terminalRepresentation := by
  rintro ⟨hd,e,c,he⟩
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hc : Nat.card F.Uhat = 64 := by
    rw [← Nat.card_congr (Additive.toMul (α := F.Uhat))]
    simpa [hd] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat))
  have hr : primeRank 2 F.TerminalHdot ≤ 3 := by
    rw [primeRank_equiv 2 e,Atlas.G2.EvenTwoRank.two_rank (ZMod 2) (n := 1) (by simp)]
  have hX : Nat.card (F.terminalDot (F.X g)) ≤ 8 :=
    (primeRank_le_iff_elementary_card_le F.TerminalHdot).mp hr _ inferInstance
  have hcenter := (source_six_dimensional_orders_at d earlier hq chosen structural alternatives
    F hne hZ hI hc g hgP hgH hX).2.1
  have hzcard : Nat.card (F.terminalDot (conjugate F.ZU g)) = 2 := by
    let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
    have hzH : conjugate F.ZU g ≤ F.H :=
      (F.conjugate_ZU_le_X g).trans (F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP))
    let q := dotMap F F.uhatAction (conjugate F.ZU g) hzH
    have hk : q.ker=f.ker := dotMap_ker F F.uhatAction (conjugate F.ZU g) hzH
    let eqv := (QuotientGroup.quotientKerEquivOfSurjective q
      (dotMap_surjective F F.uhatAction (conjugate F.ZU g) hzH)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange f))
    have hh := source_conjugate_center_image_order_at d earlier hq chosen structural alternatives
      F hne hI g hgP hgH
    rw [hcenter] at hh
    change Nat.card (dotImage F F.uhatAction (conjugate F.ZU g))=2
    rw [Nat.card_congr eqv.toEquiv]
    change 2 * Nat.card f.range = 4 at hh
    omega
  let K := commutator F.TerminalHdot
  have hmap : K.map e.toMonoidHom=commutator (Atlas.G2.Model (ZMod 2)) := by
    change (commutator F.TerminalHdot).map e.toMonoidHom = _
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,commutator_def]
  let eK := (e.subgroupMap K).trans (MulEquiv.subgroupCongr hmap)
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hKa : ¬ IsMulCommutative K := by
    intro hcomm
    let := hcomm
    have hp : (Nat.card K).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr eK.toEquiv,Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hp
    norm_num at hp
  have hKc : centralizer (K : Set F.TerminalHdot)=⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    apply Atlas.G2.LieAutomorphismExtensions.binaryConjugation_injective
    rw [map_one]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    obtain ⟨k,hk,hky⟩ := (show y.val∈K.map e.toMonoidHom from hmap.symm ▸ y.property)
    have hcomm := congrArg e (hx k hk)
    have hky' : e k=y.val := hky
    change e x*y.val*(e x)⁻¹=y.val
    have hh : e x*y.val=y.val*e x := by
      simpa only [map_mul,hky'] using hcomm.symm
    rw [hh,mul_inv_cancel_right]
  have hKC := source_simple_normal_le_center_centralizer_at d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH K hKa hKc
  have hzX : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  have hzbot : F.terminalDot (conjugate F.ZU g)=⊥ := by
    apply bot_unique
    intro z hz
    apply mem_bot.mpr
    apply Atlas.G2.Natural.BinaryPointFlag.eq_one_of_point_cubic_fixer
      F.terminalRepresentation e c he v hyp.point_ne_zero z (hyp.fixes_point (hzX hz))
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) z (hzX hz))
    intro a ha haK ha3
    exact source_point_cube_centralizes_conjugate_center_at d earlier hq chosen structural alternatives
      F hne v hline.symm g hgP hzcard a ha (hKC haK) ha3 z hz
  have hh := Nat.card_congr (MulEquiv.subgroupCongr hzbot).toEquiv
  rw [hzcard,card_bot] at hh
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
open ChapterG.Section11.ExchangedRecognition
theorem source_four_or_whole_action_of_centerless_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (CaseTwo F.terminalRepresentation B ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_remaining_action_of_centerless_at d earlier hq chosen structural alternatives F hne hZ hI g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with (h2 | h6) | hwhole
  · exact Or.inl h2
  · exact (source_no_caseSix_at d earlier hq chosen structural alternatives F hne hZ hI h6).elim
  · exact Or.inr hwhole
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/FourDimensional.lean. -/
section
set_option backward.isDefEq.respectTransparency false
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem fourDimensional_plane_centralizer_normalizes_intersection_at (F : InvariantFlag T V 3)
    (g : G) (hg : g ∈ F.Gi 2) :
    centralizer (F.Vi 2 : Set G) ≤ normalizer (F.E g : Set G) := by
  have hCH : centralizer (F.Vi 2 : Set G) ≤ F.H :=
    (centralizer_le (F.monotone (by decide : 1≤2))).trans (Subgroup.centralizer_le_normalizer _)
  have hCW : centralizer (F.Vi 2 : Set G) ≤ normalizer (F.W : Set G) :=
    (le_inf (hCH.trans (le_normalizer_conjugateSpanBy V F.H))
      (centralizer (F.Vi 2 : Set G)).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hCg : conjugate (centralizer (F.Vi 2 : Set G)) g = centralizer (F.Vi 2 : Set G) := by
    apply Subgroup.eq_of_le_of_card_ge (conjugate_centralizer_le _ _ hg)
    rw [conjugate,card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hCX : centralizer (F.Vi 2 : Set G) ≤ normalizer (F.X g : Set G) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hCW
    rw [map_equiv_normalizer_eq] at hh
    exact hCg ▸ hh
  exact (le_inf hCW hCX).trans inf_normalizer_le_normalizer_inf
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_point_cube_preserves_intersection_at
    (v : Additive F.Uhat) (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (g : G) (hgP : g ∈ F.P L)
    (a : F.TerminalHdot)
    (ha : a ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v)
    (haZ : a ∈ F.terminalDot (centralizer (F.ZU : Set G))) (ha3 : a^3=1)
    (w : Additive F.Uhat) (hw : w ∈ hatSpace F (F.E g)) :
    F.terminalRepresentation a w ∈ hatSpace F (F.E g) := by
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  let D := C.map q
  let f : C →* D := q.subgroupMap C
  have hk : IsPGroup 2 f.ker := by
    have hle : f.ker ≤ (pCore 2 F.H).subgroupOf C := by
      intro x hx
      apply source_center_centralizing_kernel_le_core_at d earlier hq chosen structural alternatives F hne
      exact ⟨x.property,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)⟩
    exact (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf C)).to_le hle
  let aa : D := ⟨a,haZ⟩
  have hao : orderOf aa ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext ha3)
  obtain ⟨n,hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime (Nat.card f.ker) (Nat.card (zpowers aa)) := by
    rw [hn,Nat.card_zpowers]
    exact ((by decide : Nat.Coprime 2 3).pow_left n).coprime_dvd_right hao
  obtain ⟨s,hs⟩ := f.exists_subgroup_section_of_coprime_kernel (q.subgroupMap_surjective C)
    (zpowers aa) hcop
  let b : C := s ⟨aa,mem_zpowers aa⟩
  have hb3 : b^3=1 := by
    rw [← map_pow]
    have hh : (⟨aa,mem_zpowers aa⟩ : zpowers aa)^3=1 := Subtype.ext (Subtype.ext ha3)
    rw [hh,map_one]
  have hba : q b.val = a := by
    have hh : f b = aa := DFunLike.congr_fun hs (⟨aa,mem_zpowers aa⟩ : zpowers aa)
    exact congrArg Subtype.val hh
  have hbplane : (b.val:G) ∈ centralizer (F.Vi 2 : Set G) :=
    source_point_preimage_centralizes_plane_of_cube_one_at d earlier hq chosen structural alternatives
      F hne v hline b.val (hba.symm ▸ ha) b.property (congrArg Subtype.val hb3)
  have hbn := fourDimensional_plane_centralizer_normalizes_intersection_at F g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hbplane
  obtain ⟨x,hx,he⟩ := (show w.toMul ∈ hatImage F (F.E g) from hw)
  refine ⟨F.uAction b.val x,(mem_normalizer_iff.mp hbn (x:G)).mp hx,?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction b.val x) = _
  rw [← F.uhatAction_apply_mk,he]
  change F.terminalRepresentation (q b.val) w = F.terminalRepresentation a w
  rw [hba]
open Theory.SpecificGroups.SymmetricSix
theorem source_no_alternating_six_image_at
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (j : F.TerminalHdot →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (c : B.IsometryEquiv polarForm)
    (he : ∀ a w, c (F.terminalRepresentation a w) = polarAction (j a) (c w)) :
    ¬ alternatingGroup (Fin 6) ≤ j.range := by
  intro hA
  let K := (alternatingGroup (Fin 6)).comap j
  have hmap : K.map j = alternatingGroup (Fin 6) := by
    change ((alternatingGroup (Fin 6)).comap j).map j = _
    exact map_comap_eq_self hA
  let eK := (K.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hmap)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := eK.isSimpleGroup
  let : K.Normal := inferInstanceAs (((alternatingGroup (Fin 6)).comap j).Normal)
  have hKa : ¬ IsMulCommutative K := by
    intro hab
    let := hab
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective (f := eK.toMonoidHom) eK.surjective)
  have hKc : centralizer (K : Set F.TerminalHdot) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply hj
    rw [map_one]
    apply mem_bot.mp
    rw [← _root_.GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)]
    intro a ha
    obtain ⟨k,hk,rfl⟩ := (show a ∈ K.map j from hmap.symm ▸ ha)
    exact (map_mul j k x).symm.trans ((congrArg j (hx k hk)).trans (map_mul j x k))
  have hKC := source_simple_normal_le_center_centralizer_at d earlier hq chosen structural alternatives
    F hne hZ hI g hgP hgH K hKa hKc
  have hE := source_intersection_eq_seed_of_card_sixteen_at d earlier hq chosen structural alternatives
    F hne hI hc g hgP hgH
  have hdim : finrank (ZMod 2) (hatSpace F (F.E g)) = 2 := by
    rw [hE]
    exact seed_hat_dimension F (source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  let W := (hatSpace F (F.E g)).map c.toLinearEquiv.toLinearMap
  have hWdim : finrank (ZMod 2) W=2 := (c.toLinearEquiv.finrank_map_eq _).trans hdim
  have hiso : ∀ x∈W, ∀ y∈W, polarForm x y=0 := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    change polarForm (c x) (c y)=0
    rw [c.map_app]
    exact hyp.isotropic x hx y hy
  have hv : c v ≠ 0 := fun hz => hyp.point_ne_zero (c.injective (hz.trans c.map_zero.symm))
  obtain ⟨a,ha3,hav,w,hw,haw⟩ := PointCubicPlane.exists_matrix_cubic (c v) hv W hWdim hiso
    ⟨v,hyp.point_mem,rfl⟩
  obtain ⟨b,hb⟩ := hA a.property
  have hbK : b ∈ K := by change j b ∈ alternatingGroup (Fin 6); rw [hb]; exact a.property
  have hb3 : b^3=1 := by
    apply hj
    rw [map_pow,hb,map_one]
    exact congrArg Subtype.val ha3
  have hbv : b ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v := by
    apply c.injective
    change c (F.terminalRepresentation b v)=c v
    rw [he,hb]
    exact hav
  obtain ⟨x,hx,rfl⟩ := hw
  apply haw
  change polarAction a.val (c x) ∈ W
  rw [←hb,←he]
  exact ⟨F.terminalRepresentation b x,
    source_point_cube_preserves_intersection_at d earlier hq chosen structural alternatives F hne
      v hline g hgP b hbv (hKC hbK) hb3 x hx,rfl⟩
theorem source_four_symplectic_embedding_of_centerless_at
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16) :
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat),
    ∃ c : B.IsometryEquiv polarForm,
    ∃ j : F.TerminalHdot →* Equiv.Perm (Fin 6), Function.Injective j ∧
      (∀ a w, c (F.terminalRepresentation a w) = polarAction (j a) (c w)) ∧
      ¬ alternatingGroup (Fin 6) ≤ j.range := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hd : finrank (ZMod 2) (Additive F.Uhat)=4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide) (show 2^4=2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  obtain ⟨c,j,hj,he⟩ := exists_binarySymplecticFour_embedding F.terminalRepresentation
    hyp.faithful hd B hyp.alternating hyp.nondegenerate hyp.preserves
  have hform : Matrix.PSp4Three.form (n := 2) (F := ZMod 2)=polarForm := by
    unfold Matrix.PSp4Three.form polarForm
    congr 1
    ext i k
    exact ZMod.neg_eq_self_mod_two _
  let c' : B.IsometryEquiv polarForm := { c.toLinearEquiv with
    map_app' := fun x y => by rw [←hform]; exact c.map_app y x }
  let j' := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp j
  have hj' : Function.Injective j' :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hj
  have he' : ∀ a w, c' (F.terminalRepresentation a w) = polarAction (j' a) (c' w) := by
    intro a w
    have heq : polarRepresentation (j' a)=j a := by
      rw [← Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply]
      exact Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply (j a)
    change c (F.terminalRepresentation a w) = polarAction (j' a) (c w)
    rw [← polarRepresentation_apply,heq]
    exact he a w
  exact ⟨B,c',j',hj',he',source_no_alternating_six_image_at d earlier hq chosen structural alternatives
    F hne hZ hI hc g hgP hgH B v hyp hline.symm j' hj' c' he'⟩
theorem source_four_card_not_multiple_of_360_at
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hc : Nat.card F.Uhat = 16) : ¬ 360 ∣ Nat.card F.TerminalHdot := by
  intro h360
  obtain ⟨B,c,j,hj,_,hn⟩ := source_four_symplectic_embedding_of_centerless_at
    d earlier hq chosen structural alternatives F hne hZ hI hc
  have hjc : Nat.card j.range = Nat.card F.TerminalHdot :=
    (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hi := j.range.index_mul_card
  rw [s6_order] at hi
  have hd : 360 ≤ Nat.card j.range := by
    rw [hjc]
    exact Nat.le_of_dvd (Nat.card_pos) h360
  have hip : 0 < j.range.index := Nat.pos_of_ne_zero j.range.index_ne_zero_of_finite
  have hi2 : j.range.index ≤ 2 := by nlinarith
  apply hn
  by_cases h1 : j.range.index = 1
  · rw [Subgroup.index_eq_one.mp h1]
    exact le_top
  · let : j.range.Normal := normal_of_index_eq_two (by omega)
    let : Nontrivial j.range := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact Equiv.Perm.alternatingGroup_le_of_normal (by simp) inferInstance
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_four_or_whole_recognition_of_centerless_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((CaseTwo F.terminalRepresentation B ∧ ¬ 360 ∣ Nat.card F.TerminalHdot) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_four_or_whole_action_of_centerless_at d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,?_⟩
  rcases hcases with hfour | hwhole
  · have hc : Nat.card F.Uhat = 16 := by
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
      change Nat.card F.Uhat = _ at hh
      simpa only [Nat.card_zmod,hfour.1,show (2 : ℕ)^4=16 by decide] using hh
    exact .inl ⟨hfour,source_four_card_not_multiple_of_360_at d earlier hq chosen
      structural alternatives F hne hZ hI hc⟩
  · exact .inr hwhole
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end
