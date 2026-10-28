module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernel
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalAction
public import CFSG.Quasithin.ChapterG.Section10.InvariantGeometry

/-!
# The selected-vector fixed-point alternative

The original rank-two flag supplies the full parabolic plane action and
surjective displacement on W/E. The canonical commutator form and earlier
center calculations then give 12.8.11(6) on the literal terminal quotient.
G.10's fixed space inside E-hat identifies the original plane image with
the span of the exact selected vector v. Consequently the low-rank witness
contains this same v, in both the faithful and nonfaithful branches.

Source: Aschbacher--Smith, 12.8.9(3), 12.8.11(4,6), 12.8.12(3), and
G.11.1(3), printed pp.853--855 and 364. No catalogue counterexample
hypothesis or model-recognition conclusion is assumed.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)

omit [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)] in
private theorem marked_form_zero
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (C : F.UhatCommutatorForm hcomm) (a b : F.U) :
    C.form (hatElement F a) (hatElement F b) = 0 ↔ Commute a b := by
  rw [show C.form (hatElement F a) (hatElement F b) =
    (C.valueEquiv ⟨⁅(a:G),(b:G)⁆,hcomm (commutator_mem_commutator a.property b.property)⟩).toAdd
      from C.evaluation a b]
  change C.valueEquiv _ = 1 ↔ _
  rw [map_eq_one_iff C.valueEquiv C.valueEquiv.injective,Subtype.ext_iff]
  exact commutatorElement_eq_one_iff_mul_comm.trans (by
    change (a:G)*(b:G)=(b:G)*(a:G) ↔ a*b=b*a
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      exact congrArg (fun t : F.U => (t:G)) h)

omit [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)]
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))] in
private theorem terminal_fixed_space_eq :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      XfixedSpace F F.terminalHatAction g := by
  ext w
  simp only [XfixedSpace, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

include s

private theorem source_commutator_squares :
    ⁅F.U,F.U⁆ ≤ F.Vi 1 ∧ ∀ u ∈ F.U, u^2 ∈ F.Vi 1 := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  exact F.localKernel_commutator_squares h.simpleQTKE (sourceResidual M Mc) M
    (by decide) h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual
    (by omega) (h.flag_escape F)

private theorem source_parabolic_displacement :
    ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x,u⁆ * e = w := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  obtain ⟨hcomm,hsquare⟩ := s.source_commutator_squares
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨m,⟨N⟩⟩ := F.binary_source_parabolic_natural_module (by decide)
    (sourceResidual M Mc) h.L_normalizes_seed (h.binarySeedAction_surjective F)
    h.centralizer hcomm hsquare hspan s.nonabelian g s.parabolic_mem s.normalizer_not_mem
  obtain ⟨_,_,hgen,_⟩ := F.binary_generation (by decide)
    (sourceResidual M Mc) h.L_normalizes_seed (h.binarySeedAction_surjective F)
    h.centralizer hcomm hsquare hspan s.nonabelian g s.parabolic_mem s.normalizer_not_mem
  have hnE := F.binary_source_E_normalized (sourceResidual M Mc) h.L_normalizes_seed
    g s.parabolic_mem hgen.symm hcomm
  let : ((F.E g).subgroupOf F.W).Normal := normal_subgroupOf_of_le_normalizer
    ((show F.W ≤ F.I₂ (sourceResidual M Mc) from
      inf_le_left.trans (le_conjugateSpanBy _ _)).trans hnE)
  intro u hu huw w hw
  let uU : F.U := ⟨u,hu⟩
  have hcm : ∀ x ∈ F.X g, ⁅x,u⁆ ∈ F.W := fun x hx =>
    N.commutator_mem_W uU huw x ((le_sup_right : F.X g ≤ F.W ⊔ F.X g) hx)
  obtain ⟨x,hx⟩ := F.parabolicCommutator_natural_surjective (sourceResidual M Mc) g N uU
    huw hcm N.commutator_core_le (QuotientGroup.mk' ((F.E g).subgroupOf F.W) ⟨w,hw⟩)
  have he : ⁅(x:G),u⁆⁻¹ * w ∈ F.E g := by
    change (⟨⁅(x:G),u⁆,hcm x x.property⟩ : F.W)⁻¹ * ⟨w,hw⟩ ∈ (F.E g).subgroupOf F.W
    rw [← QuotientGroup.ker_mk' ((F.E g).subgroupOf F.W)]
    exact (MonoidHom.eq_iff (QuotientGroup.mk' ((F.E g).subgroupOf F.W))).mp hx.symm
  exact ⟨x,x.property,_,he,mul_inv_cancel_left _ _⟩

/-- The selected point spans the original image of V₂, not an unmarked line. -/
theorem point_span_eq_hatPlane :
    Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  obtain ⟨hcomm,hsquare⟩ := s.source_commutator_squares
  let a := Recognition.rankTwo_terminal_earlier h F d hcomm hsquare s.nonabelian
    g s.parabolic_mem s.normalizer_not_mem
  let C := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hfour := EhatFixed_eq_plane F g
    (F.P_le_G₂ (by decide) (sourceResidual M Mc) h.L_normalizes_seed s.parabolic_mem)
    hcomm a.disjoint a.center_cut a.conjugate_center_cut C.form
    (marked_form_zero hcomm C) C.nondegenerate C.alternating.isRefl
  calc
    Submodule.span (ZMod 2) {v} = hatSpace F (F.E g) ⊓
        fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) :=
      s.hypothesis.fixedSpace_in_W.symm
    _ = hatSpace F (F.Vi 2) := by
      rw [terminal_fixed_space_eq]
      exact hfour

/-- Original 12.8.11(6), on the literal terminal quotient and marked plane. -/
theorem hatPlane_fixedPointAlternative :
    XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2) ∨
      ∃ x ∈ F.terminalDot (F.X g), x ≠ 1 ∧
        Module.finrank (ZMod 2) (Symplectic.movedSpace F F.terminalHatAction x) ≤ 2 ∧
        hatSpace F (F.Vi 2) ≤ Symplectic.movedSpace F F.terminalHatAction x := by
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  obtain ⟨hcomm,hsquare⟩ := s.source_commutator_squares
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  have hg := F.P_le_G₂ (by decide) (sourceResidual M Mc) h.L_normalizes_seed s.parabolic_mem
  let a := Recognition.rankTwo_terminal_earlier h F d hcomm hsquare s.nonabelian
    g s.parabolic_mem s.normalizer_not_mem
  obtain ⟨e,_,_,_,hIG,_,_,_,_,_,_,hindex,heval⟩ := F.binary_generation (by decide)
    (sourceResidual M Mc) h.L_normalizes_seed (h.binarySeedAction_surjective F)
    h.centralizer hcomm hsquare hspan s.nonabelian g s.parabolic_mem s.normalizer_not_mem
  let C := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hC := marked_form_zero hcomm C
  have hfour : hatSpace F (F.E g) ⊓ XfixedSpace F F.terminalHatAction g =
      hatSpace F (F.Vi 2) := EhatFixed_eq_plane F g hg hcomm a.disjoint
    a.center_cut a.conjugate_center_cut C.form hC C.nondegenerate C.alternating.isRefl
  by_cases heq : XfixedSpace F F.terminalHatAction g = hatSpace F (F.Vi 2)
  · exact Or.inl heq
  right
  have hstrict : hatSpace F (F.Vi 2) < XfixedSpace F F.terminalHatAction g :=
    lt_of_le_of_ne (hfour ▸ inf_le_right) (Ne.symm heq)
  have hPhi : (frattini F.U).map F.U.subtype = F.Vi 1 := by
    rw [d.frattini_point]
    exact map_subgroupOf_eq_of_le ((F.le_seed 1).trans
      (le_conjugateSpanBy (rankTwoSeed T M) F.H))
  have hfull : Function.Surjective ((F.Vi 2).normalizerMonoidHom.comp (inclusion hIG)) := by
    intro b
    obtain ⟨i,hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ (sourceResidual M Mc)))
      (e.symm (F.binaryPlaneLabel (by decide) b))
    refine ⟨i,?_⟩
    ext w
    change (i:G)*(w:G)*(i:G)⁻¹ = (b w:G)
    rw [← heval i w]
    change ((F.binaryPlaneLabel (by decide)).symm (e (QuotientGroup.mk' _ i)) w : G) = _
    rw [hi,e.apply_symm_apply,MulEquiv.symm_apply_apply]
  obtain ⟨z,hz,hzp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hi : ∀ (a : F.H) (u w : F.Uhat),
      C.form (Additive.ofMul (F.terminalHatAction a u))
        (Additive.ofMul (F.terminalHatAction a w)) =
      C.form (Additive.ofMul u) (Additive.ofMul w) := by
    intro a u w
    change F.uhatBilinearForm (by decide) d.two d.frattini_point
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a w)) = _
    rw [F.uhatBilinearForm_apply,F.uhatCommutator_invariant (by decide) d.two d.frattini_point]
    rfl
  exact exists_lowRank_of_fixedSpace_lt F (by decide) s.nonabelian d.two hPhi d.seed_center
    (sourceResidual M Mc) g hg a.disjoint z hzp hz hIG hfull F.terminalHatAction
    F.terminalHatAction_apply_mk
    (F.binary_source_action_kernel_intersections (by decide) (sourceResidual M Mc)
      h.L_normalizes_seed (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare
      hspan s.nonabelian d.seed_center g s.parabolic_mem s.normalizer_not_mem).1
    hindex s.source_parabolic_displacement a.center_cut C.form C.nondegenerate C.alternating
    hC hi hfour hstrict

/-- G.11.1(3) for the same v in both the faithful and nonfaithful branches. -/
theorem fixedPointAlternative : FixedPointAlternative (F := F) (g := g) (v := v) := by
  rcases s.hatPlane_fixedPointAlternative with hf | ⟨a,ha,hane,hr,hm⟩
  · exact Or.inl (terminal_fixed_space_eq.trans (hf.trans s.point_span_eq_hatPlane.symm))
  · exact Or.inr ⟨⟨a,ha⟩,fun he => hane (congrArg Subtype.val he),hr,
      hm (s.point_span_eq_hatPlane ▸ Submodule.mem_span_singleton_self v)⟩

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
