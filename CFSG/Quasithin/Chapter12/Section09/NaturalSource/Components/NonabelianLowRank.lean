module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianHypotheses
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalPreimage
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction

/-!
# The original natural branch supplies G.11.1(3)

The natural parabolic quotient realizes every displacement in W/E by an
actual member of X. The canonical commutator form and the earlier center
identities then supply the fixed-line or low-rank alternative on the literal
terminalRepresentation. The form, vector, actors, relative Sylow and SQTK
cover are retained together for subsequent recognition.

This adapts the same Section 12.8 calculation used in Chapter14's
CaseOneLarge.FixedPoint to the original higher-rank flag. It constructs
recognition inputs, not an exhaustive catalogue.
Source: Aschbacher--Smith 12.8.11(6),12.8.12(3),12.9.4,
printed pp.854--855,859.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem marked_form_zero (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1)
    (B : F.UhatCommutatorForm hcomm) (a b : F.U) :
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

/-- The source representative equation [Wᵍ/E,u] = W/E, for every u outside W. -/
theorem nonabelian_parabolic_displacement
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x,u⁆ * e = w := by
  let := h.chosen.elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
      h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
      h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hspan := F.U_eq_plane_span L hn h.chosen.normalizes
    (F.localKernel_irreducible L hn h.chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  obtain ⟨ι, ⟨M⟩⟩ := F.binary_source_parabolic_natural_module hn L h.chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)
    hcomm hsquare hspan hne g hgP hgH
  obtain ⟨_, _, hgen, _⟩ := F.binary_generation hn L h.chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural)
    hcomm hsquare hspan hne g hgP hgH
  have hnE := F.binary_source_E_normalized L h.chosen.normalizes g hgP hgen.symm hcomm
  let : ((F.E g).subgroupOf F.W).Normal := normal_subgroupOf_of_le_normalizer
    ((show F.W ≤ F.I₂ L from inf_le_left.trans (le_conjugateSpanBy _ _)).trans hnE)
  intro u hu huw w hw
  let uU : F.U := ⟨u, hu⟩
  have hcm : ∀ x ∈ F.X g, ⁅x,u⁆ ∈ F.W := fun x hx =>
    M.commutator_mem_W uU huw x ((le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx)
  obtain ⟨x, hx⟩ := F.parabolicCommutator_natural_surjective L g M uU huw hcm
    M.commutator_core_le (QuotientGroup.mk' ((F.E g).subgroupOf F.W) ⟨w, hw⟩)
  have he : ⁅(x:G),u⁆⁻¹ * w ∈ F.E g := by
    change (⟨⁅(x:G),u⁆, hcm x x.property⟩ : F.W)⁻¹ * ⟨w,hw⟩ ∈ (F.E g).subgroupOf F.W
    rw [← QuotientGroup.ker_mk' ((F.E g).subgroupOf F.W)]
    exact (MonoidHom.eq_iff (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).mp hx.symm
  exact ⟨x, x.property, _, he, mul_inv_cancel_left _ _⟩

/-- G.11.1(3), with every preceding geometric and parabolic premise discharged
from the original source. Both alternatives concern the same literal action. -/
theorem nonabelian_fixed_point_alternative
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2) ∨
      ∃ x ∈ F.terminalDot (F.X g), x ≠ 1 ∧
        finrank (ZMod 2) (Symplectic.movedSpace F F.terminalHatAction x) ≤ 2 ∧
        hatSpace F (F.Vi 2) ≤ Symplectic.movedSpace F F.terminalHatAction x := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  have hn : 2 ≤ n := by have := h.rank; omega
  let := F.localKernel_tilde_seed_elementary
  have hJ := h.point_mem_Hz F earlier.alternatives
  have htwo : IsPGroup 2 F.U := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
  have hcenter := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
  have hcore := F.localKernel_eq_pCore h.source.simpleQTKE L _ F.H hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique earlier.structural earlier.uniqueness).2
    (h.seed_centralizer_le earlier.structural earlier.uniqueness) h.centralizer_L hJ
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
      h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
      h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hspan := F.U_eq_plane_span L hn h.chosen.normalizes
    (F.localKernel_irreducible L hn h.chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  have hg : g ∈ F.Gi 2 := F.P_le_G₂ hn L h.chosen.normalizes hgP
  obtain ⟨e, _, hgen, _, hIG, _, _, _, _, _, _, hindex, heval⟩ :=
    F.binary_generation hn L h.chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT earlier.structural) hcomm hsquare hspan hne g hgP hgH
  let B := F.localKernel_markedForm (by omega) htwo hphi hcomm
  have hB := marked_form_zero F hcomm B
  have hc := F.binary_source_center_calculations hn L h.chosen.normalizes
    ((pResidual_eq_top_iff 2 L).mp h.residual) (h.sylow_normalizes earlier.structural)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT earlier.structural) hcenter
    hcomm hsquare hspan hne g hgP hgH hcore B
  have hdis := disjoint_iff.mpr (F.parabolic_displaced_centers hn L
    h.chosen.normalizes hcenter g hgP hgH).1
  have hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g := by
    simpa only [inf_comm] using hc.2.2.2.2.2.2.2.2.1
  have hfour : hatSpace F (F.E g) ⊓ XfixedSpace F F.terminalHatAction g =
      hatSpace F (F.Vi 2) :=
    EhatFixed_eq_plane F g hg hcomm hdis hc.1 hZg B.form hB B.nondegenerate B.alternating.isRefl
  by_cases heq : XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2)
  · exact Or.inl heq
  right
  have hstrict : hatSpace F (F.Vi 2) < XfixedSpace F F.terminalHatAction g :=
    lt_of_le_of_ne (hfour ▸ inf_le_right) (Ne.symm heq)
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [hphi]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  have hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hIG)) := by
    intro a
    obtain ⟨i, hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L))
      (e.symm (F.binaryPlaneLabel hn a))
    refine ⟨i, ?_⟩
    ext v
    change (i:G)*(v:G)*(i:G)⁻¹ = (a v:G)
    rw [← heval i v]
    change ((F.binaryPlaneLabel hn).symm (e (QuotientGroup.mk' _ i)) v : G) = _
    rw [hi, e.apply_symm_apply, MulEquiv.symm_apply_apply]
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by omega)
  have hi : ∀ (a : F.H) (u v : F.Uhat),
      B.form (Additive.ofMul (F.terminalHatAction a u)) (Additive.ofMul (F.terminalHatAction a v)) =
        B.form (Additive.ofMul u) (Additive.ofMul v) := by
    intro a u v
    change F.uhatBilinearForm (by omega) htwo hphi
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a v)) = _
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by omega) htwo hphi]
    rfl
  exact exists_lowRank_of_fixedSpace_lt F hn hne htwo hPhi hcenter L g hg
    hdis z hzp hz hIG hfull F.terminalHatAction F.terminalHatAction_apply_mk
    (F.binary_source_action_kernel_intersections hn L h.chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT earlier.structural) hcomm hsquare hspan hne
      hcenter g hgP hgH).1 hindex
    (nonabelian_parabolic_displacement h earlier F hne g hgP hgH)
    hc.1 B.form B.nondegenerate B.alternating hB hi hfour hstrict

omit [Finite G] in
private theorem terminal_fixed_space_eq (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      XfixedSpace F F.terminalHatAction g := by
  ext w
  simp only [XfixedSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

/-- The same alternative in G.11's representation conventions, on the
original point rather than a newly chosen vector. -/
theorem nonabelian_terminal_fixed_point_alternative
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} ∨
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v
        (F.terminalDot (F.X g)) := by
  rcases nonabelian_fixed_point_alternative h earlier F hne g hgP hgH with
    hf | ⟨a, ha, _, hr, hm⟩
  · exact Or.inl ((terminal_fixed_space_eq F g).trans (hf.trans hline))
  · exact Or.inr ⟨a,ha,hr,hm (hline.symm ▸ Submodule.mem_span_singleton_self v)⟩

/-- All original G.11 recognition inputs on one flag, form, point and pair
of actors. The source's fixed-line alternative remains explicit. The SQTK
cover is the original point normalizer with its literal action projection. -/
theorem nonabelian_g11_inputs
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        Nonempty (ChapterG.Section09.SQTKCover K F.TerminalHdot) ∧
        ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
        (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
            Submodule.span (ZMod 2) {v} ∨
          ChapterG.Section11.LowRankWitness F.terminalRepresentation v
            (F.terminalDot (F.X g))) := by
  obtain ⟨hX,B,v,hg10,hline,hS⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  exact ⟨hX,B,v,hg10,hline,⟨nonabelian_sqtkCover h F⟩,hS,
    nonabelian_terminal_fixed_point_alternative h earlier F hne g hgP hgH v hline⟩
/-- A larger original center supplies a low-rank witness even in the fixed-line
case. A nonidentity returning-center image centralizes the marked hyperplane
modulo its point, so the symplectic displacement calculation applies. -/
theorem nonabelian_lowRank_of_larger_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hZ : F.Vi 1 < F.ZU) (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v
      (F.terminalDot (F.X g)) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn2 : 2 ≤ n := by omega
  have hJ := h.point_mem_Hz F earlier.alternatives
  have htwo : IsPGroup 2 F.U := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H hn2
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ hn2
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
  obtain ⟨hc,_⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ hn2
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hcenter := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
  let B := F.localKernel_markedForm (by omega) htwo hphi hc
  obtain ⟨x,hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (nonabelian_conjugate_center_ne_bot h hn earlier F hne g hgP hgH hZ)
  have hxe : (x : F.TerminalHdot) ≠ 1 := fun he => hx (Subtype.ext he)
  have hxX : (x : F.TerminalHdot) ∈ F.terminalDot (F.X g) :=
    map_mono (comap_mono (F.conjugate_ZU_le_X g)) x.property
  have hx0 : (x : F.TerminalHdot) ∈ Xdot₀ F F.terminalHatAction g := by
    apply (mem_Xdot₀_iff F F.terminalHatAction F.terminalHatAction_apply_mk
      g (F.P_le_G₂ hn2 L h.chosen.normalizes hgP) x).mpr
    refine ⟨hxX,?_⟩
    intro w hw
    apply (Submodule.Quotient.eq _).mpr
    obtain ⟨a,ha,he⟩ := x.property
    have hm := F.conjugate_center_displacement_hyperplane hn2 L h.chosen.normalizes
      hcenter B g hgP hgH ⟨a,ha⟩
    have hh := hm (Submodule.mem_map_of_mem hw)
    change F.uhatDisplacement (F.conjugateCenterActor hn2 L h.chosen.normalizes
      g hgP ⟨a,ha⟩) w ∈ F.hatSubspace (F.Vi 2) at hh
    rw [←he]
    exact hh
  have hi : ∀ (a : F.H) (u w : F.Uhat),
      B.form (Additive.ofMul (F.terminalHatAction a u))
        (Additive.ofMul (F.terminalHatAction a w)) =
          B.form (Additive.ofMul u) (Additive.ofMul w) := by
    intro a u w
    change F.uhatBilinearForm (by omega) htwo hphi
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a w)) = _
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by omega) htwo hphi]
    rfl
  obtain ⟨hr,hm⟩ := lowRank_bound_of_mem_Xdot₀ F hn2 hcenter F.terminalHatAction
    g B.form B.nondegenerate B.alternating (marked_form_zero F hc B) hi hx0 hxe
  exact ⟨x,hxX,hr,hm (hline.symm ▸ Submodule.mem_span_singleton_self v)⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
