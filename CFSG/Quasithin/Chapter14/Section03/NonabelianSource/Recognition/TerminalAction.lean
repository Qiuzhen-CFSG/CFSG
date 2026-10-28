module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalAction.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Preparation
public import CFSG.Quasithin.ChapterG.Section10.TerminalSource
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections

/-!
# The terminal action on the original rank-two central quotient

The earlier closure, parabolic and center calculations construct G.10's
hypothesis on the literal action of H/ker(uhatAction) on U/Z(U). The two
source action APIs agree definitionally, so the fixed-space, displacement
and rank theorems of 12.8.11 apply to the actual terminal subgroups.

The marked plane has a nonzero image vector. Its H-orbit spans because
U is the original conjugate span, and the Sylow subgroup fixes it because
the invariant image line is binary. The canonical commutator form supplies
the invariant symplectic form, isotropic intersection and orthogonal
hyperplane. The seven earlier-source clauses are kept in TerminalEarlierData;
the actual rank-two source consumer discharges every field.

Source: Aschbacher--Smith, 12.8.8--11 and original 14.3.11, leading to G.10.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
variable (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]

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
private theorem kernel_criterion (g : G) (hg : g∈F.Gi 2) (a : TerminalEarlierData F g hg)
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
/-- The original rank-two conjugate span makes the terminal orbit of the marked line generate. -/
theorem terminal_orbit_span (v : Additive F.Uhat)
    (hline : Submodule.span (ZMod 2) {v}=hatSpace F (F.Vi 2)) :
    Submodule.span (ZMod 2) {w | ∃ a : F.TerminalHdot, F.terminalRepresentation a v=w}=⊤ := by
  let S := Submodule.span (ZMod 2) {w | ∃ a : F.TerminalHdot, F.terminalRepresentation a v=w}
  let P : Subgroup F.U := S.toAddSubgroup.toSubgroup'.comap (QuotientGroup.mk' (center F.U))
  have hU : F.U ≤ P.map F.U.subtype := by
    change conjugateSpanBy V F.H ≤ _
    apply (closure_le _).mpr
    rintro _ ⟨h,hh,b,hb,rfl⟩
    let bU : F.U := ⟨b,le_conjugateSpanBy V F.H hb⟩
    have hbhat : hatElement F bU ∈ hatSpace F (F.Vi 2) := by
      exact ⟨bU,F.last.symm ▸ hb,rfl⟩
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

/-- The literal terminal action satisfies G.10 from the earlier rank-two source
clauses. The vector, fixed spaces, transvections, orbit span and rank are derived. -/
theorem terminal_action_hypothesis (d : ClosureGeometry F)
    (hcomm : ⁅F.U,F.U⁆≤F.Vi 1) (g:G) (hg:g∈F.Gi 2)
    (a : TerminalEarlierData F g hg) :
    ∃ he : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := he
    ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation
        (F.uhatBilinearForm (by decide) d.two d.frattini_point) v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) := by
  let := a.quotient_normal
  let := a.quotient_elementary
  let he := Xdot_uhatAction_elementary F g hg
  let := he
  let : IsElementaryAbelian 2 (F.terminalDot (F.X g)) := he
  refine ⟨he,?_⟩
  let B := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hB := form_zero_iff F hcomm B
  obtain ⟨v,hv,hline⟩ := exists_plane_hat_generator F (by decide) g hg d.seed_center
  refine ⟨v,?_⟩
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
    (terminal_orbit_span F v hline) (terminal_sylow_fixes F v hv hline)
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

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
