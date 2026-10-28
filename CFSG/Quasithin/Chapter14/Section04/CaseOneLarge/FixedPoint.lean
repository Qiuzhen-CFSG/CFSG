module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Terminal
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalPreimage
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction

/-!
# The marked fixed-point alternative for the original large-case action

The natural parabolic quotient realizes every displacement in W/E by an
actual member of Wᵍ. The earlier center calculations and canonical commutator
form therefore supply 12.8.11(6). Either the conjugate actor fixes only the
marked quotient point, or it contains a nonidentity element moving at most
two dimensions whose image contains that point. This is G.11.1(3) on the
original action, before any classification of its nonsolvable constituents.

Source: Aschbacher--Smith, 12.8.11(6), G.11.1(3) and 14.4.2,
printed pp.854--855,364,1006.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


omit [Finite G] in
private theorem marked_form_zero (F : InvariantFlag T V 3)
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
theorem source_parabolic_displacement (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x,u⁆ * e = w := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨ι, ⟨M⟩⟩ := F.binary_source_parabolic_natural_module (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
    hcomm hsquare hspan hne g hgP hgH
  obtain ⟨_, _, hgen, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT structural)
    hcomm hsquare hspan hne g hgP hgH
  have hnE := F.binary_source_E_normalized L chosen.normalizes g hgP hgen.symm hcomm
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
theorem source_fixed_point_alternative (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2) ∨
      ∃ x ∈ F.terminalDot (F.X g), x ≠ 1 ∧
        finrank (ZMod 2) (Symplectic.movedSpace F F.terminalHatAction x) ≤ 2 ∧
        hatSpace F (F.Vi 2) ≤ Symplectic.movedSpace F F.terminalHatAction x := by
  let := chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := higherRankHypothesis d earlier hq chosen
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  have hg : g ∈ F.Gi 2 := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  obtain ⟨e, _, hgen, _, hIG, _, _, _, _, _, _, hindex, heval⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  let B := F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  have hB := marked_form_zero F hcomm B
  have hc := F.binary_source_center_calculations (by decide) L chosen.normalizes
    ((pResidual_eq_top_iff 2 L).mp h.residual) (h.sylow_normalizes structural)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT structural) c.seed_center
    hcomm hsquare hspan hne g hgP hgH c.tilde_kernel B
  have hdis := disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L
    chosen.normalizes c.seed_center g hgP hgH).1
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
    rw [c.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  have hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hIG)) := by
    intro a
    obtain ⟨i, hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L))
      (e.symm (F.binaryPlaneLabel (by decide) a))
    refine ⟨i, ?_⟩
    ext v
    change (i:G)*(v:G)*(i:G)⁻¹ = (a v:G)
    rw [← heval i v]
    change ((F.binaryPlaneLabel (by decide)).symm (e (QuotientGroup.mk' _ i)) v : G) = _
    rw [hi, e.apply_symm_apply, MulEquiv.symm_apply_apply]
  obtain ⟨z, hz, hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hi : ∀ (a : F.H) (u v : F.Uhat),
      B.form (Additive.ofMul (F.terminalHatAction a u)) (Additive.ofMul (F.terminalHatAction a v)) =
        B.form (Additive.ofMul u) (Additive.ofMul v) := by
    intro a u v
    change F.uhatBilinearForm (by decide) c.two c.frattini_point
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a v)) = _
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) c.two c.frattini_point]
    rfl
  exact exists_lowRank_of_fixedSpace_lt F (by decide) hne c.two hPhi c.seed_center L g hg
    hdis z hzp hz hIG hfull F.terminalHatAction F.terminalHatAction_apply_mk
    (F.binary_source_action_kernel_intersections (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT structural) hcomm hsquare hspan hne
      c.seed_center g hgP hgH).1 hindex
    (source_parabolic_displacement d earlier hq chosen structural alternatives F hne g hgP hgH)
    hc.1 B.form B.nondegenerate B.alternating hB hi hfour hstrict

omit [Finite G] in
private theorem terminal_fixed_space_eq (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (g : G) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      XfixedSpace F F.terminalHatAction g := by
  ext w
  simp only [XfixedSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

/-- The fixed-point alternative on the exact vector retained by
source_terminal_marked_hypothesis, in G.11's representation conventions. -/
theorem source_terminal_fixed_point_alternative (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2)) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} ∨
      ∃ a : F.terminalDot (F.X g), a ≠ 1 ∧
        finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - LinearMap.id)) ≤ 2 ∧
        v ∈ LinearMap.range (F.terminalRepresentation a - LinearMap.id) := by
  rcases source_fixed_point_alternative d earlier hq chosen structural alternatives F hne
      g hgP hgH with hf | ⟨a, ha, hane, hr, hm⟩
  · exact Or.inl ((terminal_fixed_space_eq F g).trans (hf.trans hline.symm))
  · exact Or.inr ⟨⟨a, ha⟩, fun he => hane (congrArg Subtype.val he), hr,
      hm (hline ▸ Submodule.mem_span_singleton_self v)⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
