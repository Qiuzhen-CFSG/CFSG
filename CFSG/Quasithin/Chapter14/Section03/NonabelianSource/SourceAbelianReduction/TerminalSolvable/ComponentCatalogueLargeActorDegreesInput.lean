module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegrees
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.TerminalPointSylow
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.LowRank
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalPreimage
public import CFSG.Quasithin.Chapter12.Section08.Setup.FlagGeometry.Construction
public import CFSG.Quasithin.ChapterG.Section11.LowRank

/-!
# The original larger actor satisfies the full G.11 input alternative

The rank-two parabolic natural module realizes every displacement in W/E
by an element of the original conjugate actor. The earlier kernel and center
calculations therefore give 12.8.11(6). The point in the supplied G.10
hypothesis is identified with the actual image of the marked plane through
their common fixed space in E-hat; no change of point or actor is made.

Together with the actual point-fixing Sylow and SQTK cover, this constructs
G.11.1, including both alternatives of (3). The low-rank witness is obtained
only when the common fixed space is strictly larger than the marked line.
The fixed-line branch and the exhaustive classification remain separate
obligations in the source degree proof.

Source: Aschbacher--Smith, 12.8.9--12, printed pp.853--855; G.11.1,
printed p.364; the setup for 14.3.13--14, printed pp.993--994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition

private theorem marked_form_zero
    {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 F.Uhat]
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

namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

private theorem parabolic_displacement :
    ∀ u ∈ F.U, u ∉ F.W → ∀ w ∈ F.W,
      ∃ x ∈ F.X g, ∃ e ∈ F.E g, ⁅x,u⁆ * e = w := by
  let L := sourceResidual M Mc
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨ι, ⟨N⟩⟩ := F.binary_source_parabolic_natural_module (by decide) L h.L_normalizes_seed
    (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan s.nonabelian
    g s.parabolic_mem s.normalizer_not_mem
  obtain ⟨_, _, hgen, _⟩ := F.binary_generation (by decide) L h.L_normalizes_seed
    (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan s.nonabelian
    g s.parabolic_mem s.normalizer_not_mem
  have hnE := F.binary_source_E_normalized L h.L_normalizes_seed g s.parabolic_mem hgen.symm hcomm
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

/-- The actual point and both alternatives of G.11.1(3), derived from the
original source. A fixed line is not replaced by an unproved low-rank witness. -/
theorem fixed_point_alternative :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v} ∨
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let L := sourceResidual M Mc
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let c := rankTwo_closure_geometry h F s.nonabelian
  let : IsElementaryAbelian 2 (F.Vi 2) := IsElementaryAbelian.of_injective
    (inclusion (F.le_seed 2)) (inclusion_injective _)
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  have hg : g ∈ F.Gi 2 := F.P_le_G₂ (by decide) L h.L_normalizes_seed s.parabolic_mem
  obtain ⟨e, _, _, _, hIG, _, _, _, _, _, _, hindex, heval⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan s.nonabelian g s.parabolic_mem s.normalizer_not_mem
  let C := F.localKernel_markedForm (by decide) c.two c.frattini_point hcomm
  have hC := marked_form_zero F hcomm C
  have a := rankTwo_terminal_earlier h F c hcomm hsquare s.nonabelian
    g s.parabolic_mem s.normalizer_not_mem
  have hfour : hatSpace F (F.E g) ⊓ XfixedSpace F F.terminalHatAction g =
      hatSpace F (F.Vi 2) :=
    EhatFixed_eq_plane F g hg hcomm a.disjoint a.center_cut a.conjugate_center_cut
      C.form hC C.nondegenerate C.alternating.isRefl
  have hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      XfixedSpace F F.terminalHatAction g := by
    ext w
    simp only [XfixedSpace, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} := by
    rw [← hfour, ← hfix]
    exact s.hypothesis.fixedSpace_in_W
  by_cases heq : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v}
  · exact Or.inl heq
  right
  have hstrict : hatSpace F (F.Vi 2) < XfixedSpace F F.terminalHatAction g := by
    apply lt_of_le_of_ne (hfour ▸ inf_le_right)
    intro he
    exact heq (hfix.trans (he.symm.trans hline))
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
    intro b u w
    change F.uhatBilinearForm (by decide) c.two c.frattini_point
      (Additive.ofMul (F.uhatAction b u)) (Additive.ofMul (F.uhatAction b w)) = _
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) c.two c.frattini_point]
    rfl
  obtain ⟨x, hx, _, hr, hm⟩ := exists_lowRank_of_fixedSpace_lt F (by decide) s.nonabelian
    c.two hPhi c.seed_center L g hg a.disjoint z hzp hz hIG hfull F.terminalHatAction
    F.terminalHatAction_apply_mk
    (F.binary_source_action_kernel_intersections (by decide) L h.L_normalizes_seed
      (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan s.nonabelian
      c.seed_center g s.parabolic_mem s.normalizer_not_mem).1 hindex
    s.parabolic_displacement a.center_cut C.form C.nondegenerate C.alternating hC hi hfour hstrict
  exact ⟨x, hx, hr, hm (hline.symm ▸ Submodule.mem_span_singleton_self v)⟩

/-- G.11.1(4) uses normality inside the actual image of the original Sylow. -/
theorem normal_sylow :
    ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  exact ⟨_, source_terminal_actor_normal_in_point_sylow s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
    F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis⟩

/-- The exhaustive classifier's genuine input on the original dotted group.
This supplies its SQTK cover and both extra G.11 hypotheses, not its output list. -/
theorem classification_input :
    Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
          Submodule.span (ZMod 2) {v} ∨
        ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :=
  ⟨⟨terminal_sqtkCover s.simple F (by decide)⟩, s.normal_sylow, s.fixed_point_alternative⟩

/-- The strict fixed-space branch supplies the exact witness required by the
independent low-rank classifier. The fixed-line branch is deliberately retained. -/
theorem low_rank_of_fixed_space_ne
    (hne : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) ≠
      Submodule.span (ZMod 2) {v}) :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) :=
  s.fixed_point_alternative.resolve_left hne

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
