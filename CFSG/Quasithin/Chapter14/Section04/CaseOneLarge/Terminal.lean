module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExtraspecialInputs
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterPoint
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Cover
public import CFSG.Quasithin.ChapterG.Section10.Reducible.Solvable

/-!
# The original rank-three terminal action in the extraspecial case

The original natural module supplies U = ⟨V₂ᴴ⟩. Thus the binary line V₂/Z(U)
has a spanning orbit even though V₂ is not the whole three-dimensional seed.
The source parabolic and center calculations construct the actual G.10
hypothesis on H/ker(uhatAction) acting on U/Z(U), together with its SQTK cover.

When Z(U) = V₁, the kernel is O₂(H) and the conjugate center has trivial dotted
image. This gives the literal 14.4.1 rank equation. G.10.4 also excludes a
reducible terminal action when |U| > 64, since its degree-four conclusion
would force |U| = 32. The marked nonsolvable catalogue is still required.

The general terminal calculations are adapted from
Section03.NonabelianSource.Recognition.TerminalAction, with the rank-three
span identity supplied by the original source rather than the rank-two flag's
last-subspace equation.

Source: Aschbacher--Smith, 12.8.8--12, 14.3.11 and 14.4.1--2,
printed pp.851--855,993,1006.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private structure TerminalData (F : InvariantFlag T V 3) (g : G) (hg : g ∈ F.Gi 2) : Prop where
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
private theorem form_zero_iff (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1)
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
private theorem terminal_fixedSpace_eq (g : G) :
    hatSpace F (F.E g) ⊓ fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      EhatFixed F g := by
  ext u
  simp only [EhatFixed,Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,
    LinearMap.sub_apply,LinearMap.id_apply,sub_eq_zero]
  rfl

omit [Finite G] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
private theorem kernel_criterion (g : G) (hg : g∈F.Gi 2) (a : TerminalData F g hg)
    (x : F.H) (hx : (x:G)∈F.X g) : F.uhatAction x=1 ↔ (x:G)∈F.E g := by
  rw [← a.kernel,F.mem_xHatKernel]
  exact ⟨fun h => ⟨hx,(F.mem_uhatAction_ker_iff x).mp h⟩,
    fun h => (F.mem_uhatAction_ker_iff x).mpr h.2⟩

private theorem terminal_form_invariant (d : ClosureGeometry F)
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
/-- The original plane conjugate span makes the terminal orbit of the marked line generate. -/
private theorem terminal_orbit_span (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (v : Additive F.Uhat)
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
private theorem terminal_sylow_fixes (v : Additive F.Uhat) (hv : v≠0)
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

private theorem elementary_primeRank_eq_finrank (A : Type*) [Group A] [Finite A]
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
private theorem hat_primeRank_eq_finrank (A : Subgroup G) :
    primeRank 2 (hatImage F A)=finrank (ZMod 2) (hatSpace F A) := by
  let : IsElementaryAbelian 2 (hatImage F A) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 F.Uhat) a.val }
  rw [elementary_primeRank_eq_finrank]
  have h1 := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=Additive (hatImage F A))
  have h2 := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=hatSpace F A)
  have hc : Nat.card (Additive (hatImage F A))=Nat.card (hatSpace F A) :=
    (Nat.card_congr Additive.toMul).trans (card_hatSpace F A).symm
  rw [Nat.card_zmod] at h1 h2
  exact Nat.pow_right_injective (by decide : 2≤2) (h1.symm.trans (hc.trans h2))

/-- The literal terminal action satisfies G.10 from the earlier source
clauses. The vector, fixed spaces, transvections, orbit span and rank are derived. -/
private theorem terminal_action_hypothesis (d : ClosureGeometry F)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H)
    (hcomm : ⁅F.U,F.U⁆≤F.Vi 1) (g:G) (hg:g∈F.Gi 2)
    (a : TerminalData F g hg) :
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
  have hB := form_zero_iff F hcomm B
  obtain ⟨v,hv,hline⟩ := exists_plane_hat_generator F (by decide) g hg d.seed_center
  refine ⟨v, ?_, hline⟩
  have hPhi : (frattini F.U).map F.U.subtype=F.Vi 1 := by
    rw [d.frattini_point]
    exact map_subgroupOf_eq_of_le (show F.Vi 1≤F.U from
      (F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  have hrank := transvection_rank_identity F (by decide) g hg d.seed_center a.disjoint
    a.center_cut a.conjugate_center_cut (kernel_criterion F g hg a) B.form hB B.nondegenerate
  dsimp only at hrank
  rw [hat_primeRank_eq_finrank F,elementary_primeRank_eq_finrank F.Uhat,
    elementary_primeRank_eq_finrank (XdotCenterQuotient F F.uhatAction g)] at hrank
  have hperp : hatSpace F F.W=(B.form (v:Additive F.Uhat)).ker := by
    rw [What_eq_orthogonal F B.form hB,← hline,
      LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    rfl
  apply F.terminal_g10_hypothesis g hg B.form B.nondegenerate B.alternating
    (terminal_form_invariant F d) v hv hline.symm v.property
    (terminal_orbit_span F hspan v hline) (terminal_sylow_fixes F v hv hline)
    (Ehat_totally_isotropic F (by decide) g d.two hPhi a.disjoint B.form hB)
  · intro x hx e heE
    exact Ehat_displacement_mem_plane F g hg hcomm ⟨x,hx⟩ ⟨e,heE⟩
  · rw [terminal_fixedSpace_eq F]
    exact EhatFixed_eq_plane F g hg hcomm a.disjoint a.center_cut a.conjugate_center_cut
      B.form hB B.nondegenerate B.alternating.isRefl
  · exact F.commutator_W_X_le_E g
  · exact hperp
  · exact hrank
  · intro e heE heH
    exact (kernel_criterion F g hg a ⟨e,heH⟩ heE.2).mpr heE
  · exact a.stabilizer



omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
/-- All closure data on the original rank-three flag, including its action kernel. -/
theorem source_closure_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hne : ¬ IsMulCommutative F.U) :
    let := chosen.elementary
    ClosureGeometry F := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hc⟩ := source_closure d earlier hq chosen structural alternatives F hne
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  exact ⟨htwo, hphi, hc, source_action_kernel d earlier hq chosen
    ⟨structural, unique, alternatives⟩ F⟩

private theorem source_terminal_earlier (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : ClosureGeometry F)
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U,u^2 ∈ F.Vi 1)
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    TerminalData F g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) := by
  let h := higherRankHypothesis d earlier hq chosen
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨e,_,hgen,_,_,_,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
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
    chosen.normalizes (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
    hcomm hsquare hspan hne c.seed_center g hgP hgH
  let B : F.UhatCommutatorForm hcomm :=
    F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  have hc := F.binary_source_center_calculations (by decide) L chosen.normalizes
    ((pResidual_eq_top_iff 2 L).mp h.residual) (h.sylow_normalizes structural)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT structural) c.seed_center
    hcomm hsquare hspan hne g hgP hgH c.tilde_kernel B
  refine ⟨hn,he,?_,hk.1,hstab,hc.1,?_⟩
  · exact disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L
      chosen.normalizes c.seed_center g hgP hgH).1
  · have hh := hc.2.2.2.2.2.2.2.2.1
    simpa only [inf_comm] using hh

omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
/-- G.10.1 with the original quotient point retained. The specified quotient
Sylow fixes that same vector, as required by G.11.1(4). -/
theorem source_terminal_marked_hypothesis (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  let heU := F.uhat_elementary_of_point (by decide) c.two c.frattini_point
  let := heU
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  let a := source_terminal_earlier F d earlier hq chosen structural c hcomm hsquare hne g hgP hgH
  obtain ⟨heX, v, hyp, hline⟩ := terminal_action_hypothesis F c
    (source_seed_geometry d earlier hq chosen F).2.1 hcomm g
    (F.P_le_G₂ (by decide) L chosen.normalizes hgP) a
  exact ⟨heU, heX, _, v, hyp, hline,
    terminal_sylow_fixes F v hyp.point_ne_zero hline⟩


omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
/-- The original rank-three source satisfies every clause of G.10.1. -/
theorem source_terminal_hypothesis (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) := by
  obtain ⟨heU, heX, B, v, hyp, _⟩ :=
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  exact ⟨heU, heX, B, v, hyp⟩


omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
/-- In the extraspecial case the terminal action kernel is the literal two-core. -/
theorem source_terminal_kernel (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) :
    F.terminalHatAction.ker = pCore 2 F.H := by
  let := chosen.elementary
  exact terminal_kernel_of_center_point F
    (source_closure_geometry F d earlier hq chosen structural alternatives hne) hZ

omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
/-- The conjugate center has trivial image under that same terminal quotient. -/
theorem source_terminal_conjugate_center (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.terminalDot (conjugate F.ZU g) = ⊥ := by
  let := chosen.elementary
  have hplane := F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH
  have hZU : conjugate F.ZU g ≤ F.U := by
    rw [hZ]
    exact le_sup_right.trans (hplane.ge.trans ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)))
  have htwo := (source_closure d earlier hq chosen structural alternatives F hne).1
  have hUcore : F.U ≤ F.H.pCoreIn 2 := le_pCoreIn_of_normalizes htwo F.U_le_H
    (le_normalizer_conjugateSpanBy V F.H)
  change ((conjugate F.ZU g).subgroupOf F.H).map
    (QuotientGroup.mk' F.terminalHatAction.ker) = ⊥
  apply le_bot_iff.mp
  rw [map_le_iff_le_comap, MonoidHom.comap_bot, QuotientGroup.ker_mk',
    source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ]
  intro x hx
  have hm := hUcore (hZU hx)
  obtain ⟨y, hy, he⟩ := hm
  exact (show y = x from Subtype.ext he) ▸ hy

omit [IsElementaryAbelian 2 V] in
/-- Original 14.4.1 on the literal central quotient and conjugate actor.
The smaller actor in G.10 is trivial because the center is the marked point. -/
theorem source_terminal_rank_balance (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    finrank (ZMod 2) (hatSpace F (F.E g)) + Group.rank (F.terminalDot (F.X g)) =
      finrank (ZMod 2) (Additive F.Uhat) - 1 := by
  obtain ⟨_, heX, B, v, hyp⟩ :=
    source_terminal_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  have hd := hyp.dimension
  have hbot : ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) = ⊥ := by
    rw [source_terminal_conjugate_center F d earlier hq chosen structural alternatives hne hZ g hgP hgH]
    simp only [bot_subgroupOf]
  rw [hbot, Group.rank_congr (QuotientGroup.quotientBot)] at hd
  exact hd

omit [IsElementaryAbelian 2 V] in
/-- The original large closure has an irreducible terminal action. A reducible
G.10 action would have dimension four, forcing the extraspecial group to have
order 32, contrary to the literal large-branch hypothesis. -/
theorem source_large_terminal_irreducible (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U) : IsIrreducible F.terminalRepresentation := by
  obtain ⟨g, _, hgP, hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_, heX, B, v, hyp⟩ :=
    source_terminal_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  by_contra hred
  have hd := (hyp.reducible_degree_and_solvable hred).1
  have hcenter := (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1.center_order_p
  have hquot := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
  rw [Nat.card_zmod, hd] at hquot
  have hcard : Nat.card F.U = 32 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U), hcenter]
    change Nat.card (Additive F.Uhat) * 2 = 32
    norm_num only [hquot]
  omega

omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat] in
/-- The literal dotted actor has its original point-normalizer as an SQTK
cover. This supplies the cover used by the G.9 source classification. -/
theorem source_terminal_cover (d : Counterexample T L) (chosen : ChosenModule T L V) :
    Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot) := by
  let := chosen.elementary
  exact ⟨terminal_sqtkCover d.qtke F (by decide)⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
