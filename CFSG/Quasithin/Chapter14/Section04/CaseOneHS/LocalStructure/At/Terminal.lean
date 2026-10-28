module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.FaithfulExclusion

/-!
# The literal marked terminal action at G,T

The original closure and its two parabolics produce the G.10 hypothesis
on H/C_H(U/Z(U)), retaining the marked line, actor and chosen Sylow.
The center and overlap calculations then prove the nontrivial dotted
conjugate center and the original half-degree bound.
Source: Aschbacher--Smith 12.8.8--13 and 14.3.23--24, pp.851--856,999--1000.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneLarge/ExtraspecialInputs.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_commutator_squares_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    ⁅F.U, F.U⁆ ≤ F.Vi 1 ∧ ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  exact F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape_at F alternatives)
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- The corresponding universal proof is in CaseOneLarge/Terminal.lean. -/
section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private structure terminal_TerminalData_at (F : InvariantFlag T V 3) (g : G) (hg : g ∈ F.Gi 2) : Prop where
  quotient_normal : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal
  quotient_elementary : letI := quotient_normal
    IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸
      (F.E g).subgroupOf (F.W ⊔ F.X g))
  disjoint : Disjoint (conjugate (F.Vi 1) g) F.ZU
  kernel : F.xHatKernel g hg = F.E g
  stabilizer : ∀ u : F.U, (u : G) ∉ F.W →
    (F.xHatStabilizer g hg (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
      (conjugate F.ZU g : Set G) * (F.E g : Set G)
  center_cut : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1
  conjugate_center_cut : conjugate F.ZU g ⊓ F.U =
    (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g
variable (F : InvariantFlag T V 3) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem terminal_form_zero_iff_at (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1)
    (B : F.UhatCommutatorForm hcomm) (a b : F.U) :
    B.form (hatElement F a) (hatElement F b)=0 ↔ Commute a b := by
  rw [show B.form (hatElement F a) (hatElement F b) =
    (B.valueEquiv ⟨⁅(a:G),(b:G)⁆,hcomm (commutator_mem_commutator a.property b.property)⟩).toAdd
      from B.evaluation a b]
  change B.valueEquiv _ = 1 ↔ _
  rw [map_eq_one_iff B.valueEquiv B.valueEquiv.injective,Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm.trans (by
    change (a:G)*(b:G)=(b:G)*(a:G) ↔ a*b=b*a
    constructor
    · intro h
      apply Subtype.ext
      exact h
    · intro h
      exact congrArg (fun t : F.U => (t:G)) h)
omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem terminal_terminal_fixedSpace_eq_at (g : G) :
    hatSpace F (F.E g) ⊓ fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      EhatFixed F g := by
  ext u
  simp only [EhatFixed,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,
    LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]
  rfl
omit [Finite G] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
private theorem terminal_kernel_criterion_at (g : G) (hg : g∈F.Gi 2) (a : terminal_TerminalData_at F g hg)
    (x : F.H) (hx : (x:G)∈F.X g) : F.uhatAction x=1 ↔ (x:G)∈F.E g := by
  rw [← a.kernel,F.mem_xHatKernel]
  exact ⟨fun h => ⟨hx,(F.mem_uhatAction_ker_iff x).mp h⟩,
    fun h => (F.mem_uhatAction_ker_iff x).mpr h.2⟩
private theorem terminal_terminal_form_invariant_at (d : ClosureGeometry F)
    (a : F.TerminalHdot) (u w : Additive F.Uhat) :
    F.uhatBilinearForm (by decide) d.two d.frattini_point
      (F.terminalRepresentation a u) (F.terminalRepresentation a w) =
    F.uhatBilinearForm (by decide) d.two d.frattini_point u w := by
  obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
  change F.uhatBilinearForm (by decide) d.two d.frattini_point
    (Additive.ofMul (F.uhatAction h u.toMul)) (Additive.ofMul (F.uhatAction h w.toMul)) = _
  rw [F.uhatBilinearForm_apply,F.uhatCommutator_invariant (by decide) d.two d.frattini_point]
  rfl
omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem terminal_terminal_orbit_span_at (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (v : Additive F.Uhat)
    (hline : Submodule.span (ZMod 2) {v}=hatSpace F (F.Vi 2)) :
    Submodule.span (ZMod 2) {w | ∃ a : F.TerminalHdot, F.terminalRepresentation a v=w}=⊤ := by
  let S := Submodule.span (ZMod 2) {w | ∃ a : F.TerminalHdot, F.terminalRepresentation a v=w}
  let P : Subgroup F.U := S.toAddSubgroup.toSubgroup'.comap (QuotientGroup.mk' (center F.U))
  have hU : F.U ≤ P.map F.U.subtype := by
    apply hspan.le.trans
    apply (closure_le _).mpr
    rintro _ ⟨h,hh,b,hb,rfl⟩
    let bU : F.U := ⟨b,(F.le_seed 2).trans (le_conjugateSpanBy V F.H) hb⟩
    have hbhat : hatElement F bU ∈ hatSpace F (F.Vi 2) := by
      exact ⟨bU,hb,rfl⟩
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline.symm ▸ hbhat)
    let hH : F.H := ⟨h,hh⟩
    refine ⟨F.uAction hH bU, ?_,rfl⟩
    change hatElement F (F.uAction hH bU) ∈ S
    have he : hatElement F (F.uAction hH bU) =
        F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker hH) (hatElement F bU) :=
      congrArg Additive.ofMul (F.uhatAction_apply_mk hH bU).symm
    rw [he,← hc,map_smul]
    exact S.smul_mem c (Submodule.subset_span ⟨_,rfl⟩)
  apply top_unique
  intro w _
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
  obtain ⟨a,ha,he⟩ := hU u.property
  have he' : a=u := Subtype.ext he
  change Additive.ofMul (QuotientGroup.mk' (center F.U) a)∈S at ha
  rw [he',hu] at ha
  exact ha
omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem terminal_terminal_sylow_fixes_at (v : Additive F.Uhat) (hv : v≠0)
    (hline : Submodule.span (ZMod 2) {v}=hatSpace F (F.Vi 2)) :
    ∀ t∈F.terminalDot (T:Subgroup G), F.terminalRepresentation t v=v := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := ht
  have hvP : v∈hatSpace F (F.Vi 2) := hline ▸ Submodule.mem_span_singleton_self v
  obtain ⟨u,hu,he⟩ := (show v.toMul∈hatImage F (F.Vi 2) from hvP)
  have hau : (F.uAction a u : G)∈F.Vi 2 :=
    (mem_normalizer_iff.mp (F.invariant 2 ha) (u:G)).mp hu
  have him : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v∈
      hatSpace F (F.Vi 2) := by
    refine ⟨F.uAction a u,hau,?_⟩
    change QuotientGroup.mk' (center F.U) (F.uAction a u) = F.uhatAction a v.toMul
    rw [← F.uhatAction_apply_mk,he]
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hline.symm ▸ him)
  have hne : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v ≠ 0 := by
    intro he
    have h := congrArg (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)⁻¹) he
    have hh : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)⁻¹
        (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v)=v := by
      rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
    rw [hh,map_zero] at h
    exact hv h
  have hcne : c≠0 := by intro h; rw [h,zero_smul] at hc; exact hne hc.symm
  have hc1 : c=1 := by
    have h : ∀c:ZMod 2,c=0 ∨ c=1 := by decide
    exact (h c).resolve_left hcne
  simpa only [hc1,one_smul] using hc.symm
private theorem terminal_elementary_primeRank_eq_finrank_at (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : primeRank 2 A=finrank (ZMod 2) (Additive A) := by
  have hc : Nat.card A=2^finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive A)
  have hu := IsElementaryAbelian.primeRank_le_of_card_le A hc.le
  let : IsElementaryAbelian 2 (⊤ : Subgroup A) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a.val }
  have hl := (primeRank_le_iff_elementary_card_le A).mp (le_refl (primeRank 2 A))
    (⊤ : Subgroup A) inferInstance
  rw [card_top,hc] at hl
  exact le_antisymm hu ((Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hl)
omit [IsElementaryAbelian 2 V] in
private theorem terminal_hat_primeRank_eq_finrank_at (A : Subgroup G) :
    primeRank 2 (hatImage F A)=finrank (ZMod 2) (hatSpace F A) := by
  let : IsElementaryAbelian 2 (hatImage F A) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 F.Uhat) a.val }
  rw [terminal_elementary_primeRank_eq_finrank_at]
  have h1 := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (hatImage F A))
  have h2 := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=hatSpace F A)
  have hc : Nat.card (Additive (hatImage F A))=Nat.card (hatSpace F A) :=
    (Nat.card_congr Additive.toMul).trans (card_hatSpace F A).symm
  rw [Nat.card_zmod] at h1 h2
  exact Nat.pow_right_injective (by decide : 2≤2) (h1.symm.trans (hc.trans h2))
private theorem terminal_terminal_action_hypothesis_at (d : ClosureGeometry F)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H)
    (hcomm : ⁅F.U,F.U⁆≤F.Vi 1) (g:G) (hg:g∈F.Gi 2)
    (a : terminal_TerminalData_at F g hg) :
    ∃ he : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := he
    ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation
        (F.uhatBilinearForm (by decide) d.two d.frattini_point) v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) := by
  let := a.quotient_normal
  let := a.quotient_elementary
  let he := Xdot_uhatAction_elementary F g hg
  let := he
  let : IsElementaryAbelian 2 (F.terminalDot (F.X g)) := he
  refine ⟨he,?_⟩
  let B := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hB := terminal_form_zero_iff_at F hcomm B
  obtain ⟨v,hv,hline⟩ := exists_plane_hat_generator F (by decide) g hg d.seed_center
  refine ⟨v, ?_, hline⟩
  have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [d.frattini_point]
    exact map_subgroupOf_eq_of_le (show F.Vi 1≤F.U from
      (F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  have hrank := transvection_rank_identity F (by decide) g hg d.seed_center a.disjoint
    a.center_cut a.conjugate_center_cut (terminal_kernel_criterion_at F g hg a) B.form hB B.nondegenerate
  dsimp only at hrank
  rw [terminal_hat_primeRank_eq_finrank_at F,terminal_elementary_primeRank_eq_finrank_at F.Uhat,
    terminal_elementary_primeRank_eq_finrank_at (XdotCenterQuotient F F.uhatAction g)] at hrank
  have hperp : hatSpace F F.W=(B.form (v:Additive F.Uhat)).ker := by
    rw [What_eq_orthogonal F B.form hB,← hline,
      LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    rfl
  apply F.terminal_g10_hypothesis g hg B.form B.nondegenerate B.alternating
    (terminal_terminal_form_invariant_at F d) v hv hline.symm v.property
    (terminal_terminal_orbit_span_at F hspan v hline) (terminal_terminal_sylow_fixes_at F v hv hline)
    (Ehat_totally_isotropic F (by decide) g d.two hPhi a.disjoint B.form hB)
  · intro x hx e heE
    exact Ehat_displacement_mem_plane F g hg hcomm ⟨x,hx⟩ ⟨e,heE⟩
  · rw [terminal_terminal_fixedSpace_eq_at F]
    exact EhatFixed_eq_plane F g hg hcomm a.disjoint a.center_cut a.conjugate_center_cut
      B.form hB B.nondegenerate B.alternating.isRefl
  · exact F.commutator_W_X_le_E g
  · exact hperp
  · exact hrank
  · intro e heE heH
    exact (terminal_kernel_criterion_at F g hg a ⟨e,heH⟩ heE.2).mpr heE
  · exact a.stabilizer
omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
theorem source_closure_geometry_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (hne : ¬ IsMulCommutative F.U) :
    let := chosen.elementary
    ClosureGeometry F := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  exact ⟨htwo, hphi, hc, source_action_kernel_at d earlier hq chosen
    structural alternatives F⟩
private theorem terminal_source_terminal_earlier_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (c : ClosureGeometry F)
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U,u^2 ∈ F.Vi 1)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    terminal_TerminalData_at F g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) := by
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨e,_,hgen,_,_,_,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  have hqn := F.binary_source_E_normal_in_core L chosen.normalizes g hgP hgen.symm hcomm
  let := hqn
  have hqe := F.binary_source_quotient_elementary L chosen.normalizes g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal,
      letI := hn
      IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
        (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hqn,hqe⟩
  rw [hsplit] at hpair
  obtain ⟨hn,he⟩ := hpair
  let := hn
  obtain ⟨_,hk,hstab⟩ := F.binary_source_parabolic_action_clauses (by decide) L
    chosen.normalizes (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural)
    hcomm hsquare hspan hne c.seed_center g hgP hgH
  let B : F.UhatCommutatorForm hcomm :=
    F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  have hc := F.binary_source_center_calculations (by decide) L chosen.normalizes
    ((pResidual_eq_top_iff 2 L).mp h.residual) (h.sylow_normalizes_at structural)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT_at structural) c.seed_center
    hcomm hsquare hspan hne g hgP hgH c.tilde_kernel B
  refine ⟨hn,he,?_,hk.1,hstab,hc.1,?_⟩
  · exact disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L
      chosen.normalizes c.seed_center g hgP hgH).1
  · have hh := hc.2.2.2.2.2.2.2.2.1
    simpa only [inf_comm] using hh
omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
theorem source_terminal_marked_hypothesis_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v := by
  let := chosen.elementary
  let c := source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let heU := F.uhat_elementary_of_point (by decide) c.two c.frattini_point
  let := heU
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares_at d earlier hq chosen structural alternatives F
  let a := terminal_source_terminal_earlier_at F d earlier hq chosen structural c hcomm hsquare hne g hgP hgH
  obtain ⟨heX, v, hyp, hline⟩ := terminal_terminal_action_hypothesis_at F c
    (source_seed_geometry_at d earlier hq chosen F).2.1 hcomm g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) a
  exact ⟨heU, heX, _, v, hyp, hline,
    terminal_terminal_sylow_fixes_at F v hyp.point_ne_zero hline⟩
omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
theorem source_terminal_hypothesis_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) := by
  obtain ⟨heU, heX, B, v, hyp, _⟩ :=
    source_terminal_marked_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  exact ⟨heU, heX, B, v, hyp⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/EarlierGeometry.lean. -/
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
private theorem earlierGeometry_hatSpace_mono_at (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    {A B : Subgroup G} (h : A ≤ B) : hatSpace F A ≤ hatSpace F B :=
  fun _ hx => (show hatImage F A ≤ hatImage F B from map_mono (comap_mono h)) hx
theorem source_four_marked_geometry_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
      hatSpace F (F.E g) = hatSpace F V ∧
      finrank (ZMod 2) (hatSpace F (F.E g)) = 2 ∧
      Group.rank ((F.terminalDot (F.X g)) ⧸
        (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) = 1 := by
  obtain ⟨_, hx, B, v, hyp⟩ := CaseOneLarge.source_terminal_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := hx
  let := chosen.elementary
  have hVE : hatSpace F V ≤ hatSpace F (F.E g) :=
    earlierGeometry_hatSpace_mono_at F (F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L chosen.normalizes hgP))
  have hv := seed_hat_dimension F (source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  have he := Submodule.finrank_mono hVE
  have hi := B.twice_finrank_le_of_isotropic hyp.nondegenerate _ hyp.isotropic
  rw [hd] at hi
  have heq : finrank (ZMod 2) (hatSpace F (F.E g)) = 2 := by omega
  have hb := hyp.dimension
  rw [hd, heq] at hb
  exact ⟨hx, (Submodule.eq_of_le_of_finrank_eq hVE (hv.trans heq.symm)).symm, heq, by omega⟩
theorem source_seed_hat_not_invariant_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) :
    ¬ ∀ a : F.TerminalHdot, ∀ w ∈ hatSpace F V,
      F.terminalRepresentation a w ∈ hatSpace F V := by
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_, hx, B, v, hyp, hline, _⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F d earlier hq
    chosen structural alternatives hne g hgP hgH
  let := chosen.elementary
  let := hx
  obtain ⟨htwo, hphi, hvc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  have hdim := (quotient_dimension F htwo hphi hvc).1
  have hv := seed_hat_dimension F hvc
  intro hstable
  let S : Subrepresentation F.terminalRepresentation := ⟨hatSpace F V, fun a _ hw => hstable a _ hw⟩
  have hproper : S.toSubmodule ≠ ⊤ := by
    intro he
    have hh : finrank (ZMod 2) (hatSpace F V) = finrank (ZMod 2) (Additive F.Uhat) := by
      rw [show hatSpace F V = ⊤ from he, finrank_top]
    omega
  apply hyp.point_not_mem S hproper
  exact earlierGeometry_hatSpace_mono_at F (F.le_seed 2) (hline ▸ Submodule.mem_span_singleton_self v)
theorem source_dotted_intersection_ne_top_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) :
    F.terminalDot (F.H ⊓ normalizer (L : Set G)) ≠ ⊤ := by
  let := chosen.elementary
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he, card_bot] at hc
    norm_num at hc
  have hm := intersection_normalizer_at d earlier hq chosen structural
    (F.Vi 1) F.H hpoint (F.le_seed 1) le_rfl
  intro htop
  apply source_seed_hat_not_invariant_at d earlier hq chosen structural alternatives F hne
  intro a w hw
  obtain ⟨b, hb, rfl⟩ := (show a ∈ F.terminalDot (F.H ⊓ normalizer (L : Set G)) by rw [htop]; trivial)
  have hn : (b:G) ∈ normalizer (V : Set G) := (hm ▸ hb).2
  obtain ⟨c, hc, he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction b c, (mem_normalizer_iff.mp hn (c:G)).mp hc, ?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction b c) = F.terminalHatAction b w.toMul
  change QuotientGroup.mk' (center F.U) (F.uAction b c) = F.uhatAction b w.toMul
  rw [← F.uhatAction_apply_mk, he]
theorem source_earlier_actor_normal_in_sylow_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
      (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
    F.terminalDot (F.X g) ≤ (P : Subgroup F.TerminalHdot) ∧
      ((F.terminalDot (F.X g)).subgroupOf (P : Subgroup F.TerminalHdot)).Normal := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := CaseOneLarge.source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨e, _, hgen, _, hIG, hIN, _, _, hfactor, hPH, hcore, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hcore' := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  exact Xdot_normal_in_Tdot F (by decide) z hzp hz
    (F.binary_point_commutator (by decide) hcomm hindex) L g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hcore'
    F.terminalHatAction F.terminalHatAction_apply_mk
omit [Finite G] in
private theorem earlierGeometry_marked_form_zero_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat]
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (B : F.UhatCommutatorForm hcomm) (a b : F.U) :
    B.form (hatElement F a) (hatElement F b) = 0 ↔ Commute a b := by
  rw [show B.form (hatElement F a) (hatElement F b) =
    (B.valueEquiv ⟨⁅(a:G),(b:G)⁆,hcomm (commutator_mem_commutator a.property b.property)⟩).toAdd
      from B.evaluation a b]
  change B.valueEquiv _ = 1 ↔ _
  rw [map_eq_one_iff B.valueEquiv B.valueEquiv.injective,Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm.trans (by
    change (a:G)*(b:G)=(b:G)*(a:G) ↔ a*b=b*a
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg (fun t : F.U => (t:G)) h)
private theorem earlierGeometry_source_parabolic_displacement_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x,u⁆ * e = w := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := CaseOneLarge.source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨ι, ⟨N⟩⟩ := F.binary_source_parabolic_natural_module (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  obtain ⟨_, _, hgen, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hnE := F.binary_source_E_normalized L chosen.normalizes g hgP hgen.symm hcomm
  let : ((F.E g).subgroupOf F.W).Normal := normal_subgroupOf_of_le_normalizer
    ((show F.W ≤ F.I₂ L from inf_le_left.trans (le_conjugateSpanBy _ _)).trans hnE)
  intro u hu huw w hw
  let uU : F.U := ⟨u, hu⟩
  have hcm : ∀ x ∈ F.X g, ⁅x,u⁆ ∈ F.W := fun x hx =>
    N.commutator_mem_W uU huw x ((le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx)
  obtain ⟨x, hx⟩ := F.parabolicCommutator_natural_surjective L g N uU huw hcm
    N.commutator_core_le (QuotientGroup.mk' ((F.E g).subgroupOf F.W) ⟨w, hw⟩)
  have he : ⁅(x:G),u⁆⁻¹ * w ∈ F.E g := by
    change (⟨⁅(x:G),u⁆, hcm x x.property⟩ : F.W)⁻¹ * ⟨w,hw⟩ ∈ (F.E g).subgroupOf F.W
    rw [← QuotientGroup.ker_mk' ((F.E g).subgroupOf F.W)]
    exact (MonoidHom.eq_iff (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).mp hx.symm
  exact ⟨x, x.property, _, he, mul_inv_cancel_left _ _⟩
private theorem earlierGeometry_source_fixed_point_alternative_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} ∨
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let c := CaseOneLarge.source_closure_geometry_at F d earlier hq chosen structural alternatives hne
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  obtain ⟨hcomm, hsquare⟩ := CaseOneLarge.source_commutator_squares_at d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  have hg := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  obtain ⟨e, _, _, _, hIG, _, _, _, _, _, _, hindex, heval⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  let C := F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  have hC := earlierGeometry_marked_form_zero_at F hcomm C
  have hdis := disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
    c.seed_center g hgP hgH).1
  have hcuts := source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH
  have hc : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1 := by
    rw [hcuts.1]; exact hcuts.2.1
  have hcg : conjugate F.ZU g ⊓ F.U = (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g := by
    rw [hcuts.1]; exact hcuts.2.2
  have hfour : hatSpace F (F.E g) ⊓ XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2) :=
    EhatFixed_eq_plane F g hg hcomm hdis hc hcg C.form hC C.nondegenerate C.alternating.isRefl
  have hfix : Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      XfixedSpace F F.terminalHatAction g := by
    ext w
    simp only [XfixedSpace, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  by_cases heq : Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v}
  · exact Or.inl heq
  right
  have hstrict : hatSpace F (F.Vi 2) < XfixedSpace F F.terminalHatAction g := by
    apply lt_of_le_of_ne (hfour ▸ inf_le_right)
    intro he
    exact heq (hfix.trans (he.symm.trans hline.symm))
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [c.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy _ _))
  have hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hIG)) := by
    intro α
    obtain ⟨i, hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L))
      (e.symm (F.binaryPlaneLabel (by decide) α))
    refine ⟨i, ?_⟩
    ext w
    change (i:G)*(w:G)*(i:G)⁻¹ = (α w:G)
    rw [← heval i w]
    change ((F.binaryPlaneLabel (by decide)).symm (e (QuotientGroup.mk' _ i)) w : G) = _
    rw [hi, e.apply_symm_apply, MulEquiv.symm_apply_apply]
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hi : ∀ (b : F.H) (u w : F.Uhat),
      C.form (Additive.ofMul (F.terminalHatAction b u)) (Additive.ofMul (F.terminalHatAction b w)) =
        C.form (Additive.ofMul u) (Additive.ofMul w) := by
    change ∀ b u w, F.uhatBilinearForm (by decide) c.two c.frattini_point
      (Additive.ofMul (F.uhatAction b u)) (Additive.ofMul (F.uhatAction b w)) = _
    intro b u w
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) c.two c.frattini_point]
    rfl
  obtain ⟨x, hx, _, hr, hm⟩ := exists_lowRank_of_fixedSpace_lt F (by decide) hne
    c.two hPhi c.seed_center L g hg hdis z hzp hz hIG hfull F.terminalHatAction
    F.terminalHatAction_apply_mk
    (F.binary_source_action_kernel_intersections (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hcomm hsquare hspan hne
      c.seed_center g hgP hgH).1 hindex
    (earlierGeometry_source_parabolic_displacement_at d earlier hq chosen structural alternatives F hne g hgP hgH)
    hc C.form C.nondegenerate C.alternating hC hi hfour hstrict
  exact ⟨x, hx, hr, hm (hline ▸ Submodule.mem_span_singleton_self v)⟩
theorem source_earlier_classification_input_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (Representation.BinaryOffender.fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
          Submodule.span (ZMod 2) {v} ∨
        ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) := by
  obtain ⟨heU, heX, B, v, hyp, hline, hfix⟩ :=
    CaseOneLarge.source_terminal_marked_hypothesis_at F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  have hn := source_earlier_actor_normal_in_sylow_at d earlier hq chosen structural alternatives F hne g hgP hgH
  refine ⟨heU, heX, B, v, hyp, hline, CaseOneLarge.source_terminal_cover F d chosen,
    ⟨_, ?_, hn⟩, earlierGeometry_source_fixed_point_alternative_at d earlier hq chosen structural alternatives F hne g hgP hgH v hline⟩
  exact hfix
theorem source_dimension_le_twice_actor_of_dot_center_ne_bot_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hne : ¬ IsMulCommutative F.U) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hZ : F.terminalDot (conjugate F.ZU g) ≠ ⊥) :
    finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
  obtain ⟨_, hx, B, v, hyp⟩ := CaseOneLarge.source_terminal_hypothesis_at F d earlier hq chosen
    structural alternatives hne g hgP hgH
  apply hyp.dimension_le_twice_actor_of_smaller_ne_bot
  intro hb
  have hh := congrArg (fun A : Subgroup (F.terminalDot (F.X g)) =>
    A.map (F.terminalDot (F.X g)).subtype) hb
  have hle : F.terminalDot (conjugate F.ZU g) ≤ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g))
  exact hZ (by simpa only [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] using hh)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/EarlierNontrivial.lean. -/
section
open Subgroup Theory.GroupTheory Representation
open scoped MonoidAlgebra
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem earlierNontrivial_center_split_of_trivial_image_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hzero : F.terminalDot (conjugate F.ZU g) = ⊥) :
    (F.ZU = Chapter12.Section08.centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
      Disjoint (Chapter12.Section08.centerIn (F.I₂ L)) (F.Vi 1) ∧
      ∃ e : Chapter12.Section08.centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
        ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
    ⁅L, Chapter12.Section08.centerIn (F.I₂ L)⁆ = ⊥ := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  apply h.localKernel_center_product_at structural alternatives F hne g hgP hgH
  have hker := (source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  intro z hz
  have hzH := F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
    (F.conjugate_ZU_le_X g hz)
  have hzq : QuotientGroup.mk' F.terminalHatAction.ker ⟨z, hzH⟩ = 1 := by
    apply mem_bot.mp
    rw [← hzero]
    exact ⟨⟨z, hzH⟩, hz, rfl⟩
  have hk : (⟨z, hzH⟩ : F.H) ∈ F.uhatAction.ker :=
    (QuotientGroup.eq_one_iff _).mp hzq
  have hzE : z ∈ F.E g := by
    rw [← hker, F.mem_xHatKernel]
    exact ⟨F.conjugate_ZU_le_X g hz, (F.mem_uhatAction_ker_iff _).mp hk⟩
  exact hzE.1.1
private theorem earlierNontrivial_closure_location_of_trivial_image_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hzero : F.terminalDot (conjugate F.ZU g) = ⊥) :
    Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥ ∧
      normalizer (Chapter12.Section08.centerIn (F.I₂ L) : Set G) ≤ normalizer (L : Set G) ∧
      conjugateSpanBy (F.Li L 1) F.H ≤
        F.H ⊓ centralizer (F.ZU : Set G) ⊓ normalizer (L : Set G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let D := Chapter12.Section08.centerIn (F.I₂ L)
  obtain ⟨⟨hsplit, _, _⟩, hLD⟩ := earlierNontrivial_center_split_of_trivial_image_at d earlier hq chosen
    structural alternatives F hne g hgP hgH hzero
  have hD : D ≠ ⊥ := by
    intro he
    exact hZ (by simpa only [show Chapter12.Section08.centerIn (F.I₂ L) = ⊥ from he,
      bot_sup_eq] using hsplit)
  have hDT : D ≤ (T : Subgroup G) :=
    (hsplit ▸ (le_sup_left : D ≤ D ⊔ F.Vi 1)).trans
      ((map_subtype_le (center F.U)).trans
        (source_closure_le_sylow_at d earlier hq chosen structural alternatives F))
  have hND : normalizer (D : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hLN
      exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hLN⟩)
    · exact T.isPGroup'.to_le hDT
    · exact hD
    · exact sup_le ((commutator_eq_bot_iff_le_centralizer.mp hLD).trans
        (Subgroup.centralizer_le_normalizer _)) ((F.binary_sylow_le_P L).trans
          ((le_normalizer_conjugateSpanBy F.U (F.P L)).trans
            (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L)))))
  have hLC : F.Li L 1 ≤ centralizer (F.ZU : Set G) := by
    apply le_centralizer_iff.mp
    rw [hsplit]
    apply sup_le
    · exact le_centralizer_iff.mp (((F.Li_le L 1).trans inf_le_left).trans
        (commutator_eq_bot_iff_le_centralizer.mp hLD))
    · exact le_centralizer_iff.mp (((F.Li_le L 1).trans inf_le_right).trans
        (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have hJC : conjugateSpanBy (F.Li L 1) F.H ≤ centralizer (F.ZU : Set G) :=
    conjugateSpanBy_le hLC (F.H_normalizes_ZU.trans (normalizer_le_normalizer_centralizer _))
  have hDC : D ≤ F.ZU := hsplit ▸ le_sup_left
  refine ⟨hD, hND, le_inf (le_inf (conjugateSpanBy_le_self
    ((F.Li_le L 1).trans inf_le_right)) hJC) ?_⟩
  exact hJC.trans ((centralizer_le hDC).trans
    ((Subgroup.centralizer_le_normalizer _).trans hND))
omit [Finite G] in
private theorem earlierNontrivial_seed_moved_at [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 (F.tilde V)]
    (hLV : L ≤ normalizer (V : Set G)) (D : F.NaturalSeedMarking L hLV) :
    ∃ k v, F.localSeedRepresentation L hLV k v ≠ v := by
  by_contra! hfix
  let v := D.coordinates.symm (![1, 0] : Fin 2 → ZMod 2)
  have hw : (![1, 0] : Fin 2 → ZMod 2) ≠ 0 := by decide
  have hw' : (![0, 1] : Fin 2 → ZMod 2) ≠ 0 := by decide
  obtain ⟨a, ha⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero hw hw'
  obtain ⟨q, hq⟩ := D.quotientEquiv.surjective a
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.Li L 1)) q
  have he := D.equivariant k v
  rw [hfix, hq] at he
  simp only [v, LinearEquiv.apply_symm_apply] at he
  have hh := congrFun (he.trans ha) 0
  norm_num at hh
private theorem earlierNontrivial_closure_fixed_center_le_point_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hloc : conjugateSpanBy (F.Li L 1) F.H ≤
      F.H ⊓ centralizer (F.ZU : Set G) ⊓ normalizer (L : Set G)) :
    F.ZU ≤ F.Vi 1 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨htwo, hphi, _⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.tilde_elementary_of_point htwo hphi
  let := F.localKernel_tilde_seed_elementary
  let : IsElementaryAbelian 2 (F.tilde (F.UH F.H)) :=
    inferInstanceAs (IsElementaryAbelian 2 (F.tilde F.U))
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let J := conjugateSpanBy (F.Li L 1) F.H
  have hJH : J ≤ F.H := hloc.trans (inf_le_left.trans inf_le_left)
  let N := J.subgroupOf F.H
  let : N.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he, card_bot] at hc
    norm_num at hc
  have hm := intersection_normalizer_at d earlier hq chosen structural
    (F.Vi 1) F.H hpoint (F.le_seed 1) le_rfl
  have hJV : J ≤ normalizer (V : Set G) := by
    intro j hj
    exact ((hm ▸ (show j ∈ F.H ⊓ normalizer (L : Set G) from
      ⟨hJH hj,(hloc hj).2⟩))).2
  let ρ := F.localSpanRepresentation F.H le_rfl
  let σ := F.localSeedRepresentation L chosen.normalizes
  let ι := F.localSeedInclusion F.H
  let τ := ρ.comp N.subtype
  have hKJ : F.Li L 1 ≤ J := le_conjugateSpanBy _ _
  let kN : F.Li L 1 →* N := {
    toFun k := ⟨⟨k, hJH (hKJ k.property)⟩, hKJ k.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hι (k : F.Li L 1) (v : Additive (F.tilde V)) :
      ι (σ k v) = τ (kN k) (ι v) :=
    F.localSeedInclusion_equivariant L F.H chosen.normalizes le_rfl
      ((F.Li_le L 1).trans inf_le_right) k v
  let S : Subrepresentation τ := {
    toSubmodule := LinearMap.range ι
    apply_mem_toSubmodule a _ hv := by
      obtain ⟨v,rfl⟩ := hv
      let w := F.tildeAction J V hJH hJV ⟨a.val.val, a.property⟩ v.toMul
      refine ⟨Additive.ofMul w, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      rfl }
  obtain ⟨k, v, hmv⟩ := earlierNontrivial_seed_moved_at F chosen.normalizes D
  have hmove : ∃ n : N, ∃ v : S, S.toRepresentation n v ≠ v := by
    refine ⟨kN k, ⟨ι v, ⟨v,rfl⟩⟩, ?_⟩
    intro he
    have hh : τ (kN k) (ι v) = ι v := congrArg Subtype.val he
    rw [← hι] at hh
    exact hmv (F.localSeedInclusion_injective F.H hh)
  have hsimple : IsIrreducible σ :=
    (irreducible_iff_isSimpleModule_asModule σ).mpr (D.seed_simple (by decide))
  have hs : IsIrreducible S.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom S).mpr
    rw [isAtom_iff_le_of_ge]
    refine ⟨?_, ?_⟩
    · intro he
      have hzero (w : S) : w.val = 0 := by
        have he' : S.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule he
        exact (show w.val ∈ (⊥ : Submodule (ZMod 2) (Additive (F.tilde (F.UH F.H)))) from
          he' ▸ w.property)
      obtain ⟨a,w,hm⟩ := hmove
      exact hm (Subtype.ext ((hzero _).trans (hzero _).symm))
    · intro R hR hRS
      let A : Subrepresentation σ := {
        toSubmodule := R.toSubmodule.comap ι
        apply_mem_toSubmodule k _ hv := by
          change ι (σ k _) ∈ R
          rw [hι]
          exact R.apply_mem_toSubmodule _ hv }
      have hA : A ≠ ⊥ := by
        intro he
        apply hR
        apply bot_unique
        intro w hw
        obtain ⟨v,rfl⟩ := hRS hw
        have hv : v ∈ A := hw
        rw [he] at hv
        change v = 0 at hv
        rw [hv, map_zero]
        exact (⊥ : Subrepresentation τ).toSubmodule.zero_mem
      have ha : A = ⊤ := (hsimple.eq_bot_or_eq_top A).resolve_left hA
      rintro w ⟨v,rfl⟩
      exact (show v ∈ A from ha ▸ Submodule.mem_top)
  have hgen : ∀ R : Subrepresentation ρ, S.toSubmodule ≤ R.toSubmodule → R = ⊤ := by
    intro R hR
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← F.localSeed_orbit_span F.H le_rfl]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,v,rfl⟩
    exact R.apply_mem_toSubmodule a (hR ⟨v,rfl⟩)
  have hf := fixedSpace_eq_bot_of_normal_simple_seed ρ N S hs hmove hgen
  intro z hz
  let u : F.U := ⟨z, (map_subtype_le (center F.U)) hz⟩
  let v := Additive.ofMul (F.tildeMap F.U F.U_le_H u)
  have hv : v ∈ BinaryOffender.fixedSpace τ ⊤ := by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    change F.tildeProjection a.val.val * F.tildeProjection ⟨z,F.U_le_H u.property⟩ *
      (F.tildeProjection a.val.val)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg F.tildeProjection
    apply Subtype.ext
    change (a.val.val:G) * z * (a.val.val:G)⁻¹ = z
    have hc := (hloc a.val.property).1.2 z hz
    change z * (a.val.val:G) = (a.val.val:G) * z at hc
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [hf] at hv
  have he : F.tildeMap F.U F.U_le_H u = 1 := congrArg Additive.toMul hv
  have hk : u ∈ (F.tildeMap F.U F.U_le_H).ker := he
  rwa [F.tildeMap_U_ker] at hk
theorem source_earlier_conjugate_center_ne_bot_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) ≠ ⊥ := by
  let := chosen.elementary
  intro hzero
  have hloc := (earlierNontrivial_closure_location_of_trivial_image_at d earlier hq chosen structural alternatives F hne hZ
    g hgP hgH hzero).2.2
  exact hZ (le_antisymm
    (earlierNontrivial_closure_fixed_center_le_point_at d earlier hq chosen structural alternatives F hne hloc)
    (F.point_le_ZU (by decide)))
theorem source_earlier_dimension_le_twice_actor_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Module.finrank (ZMod 2) (Additive F.Uhat) ≤
      2 * Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) :=
  source_dimension_le_twice_actor_of_dot_center_ne_bot_at d earlier hq chosen structural alternatives
    F g hne hgP hgH
    (source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end
