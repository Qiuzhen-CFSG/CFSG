module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesFive
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.CenterAbovePoint.Geometry

/-!
# Low rank from the original displaced center

The rank-two source geometry gives [W,Z(U)ᵍ] ≤ V₁ᵍ ≤ V₂. Consequently
the original dotted displaced center centralizes the section W-hat/V₂-hat.
When Z(U)>V₁, its dotted image is nontrivial by the actual center-kernel
calculation. The symplectic section-centralizer lemma then provides an
element of the original actor with displacement rank at most two containing
the original marked point.

Thus the only source branch still lacking the G.11.1(3ii) witness has
Z(U)=V₁ and fixed space exactly the marked line. This uses the ambient
source geometry, not an implication from G.11.1(3i) to (3ii).
The row (5) reduction below uses the proved center-point exclusion.
The independent low-rank classifier and the remaining source recognition
and row (5) exclusion are not asserted here.

Source: Aschbacher--Smith, 12.8.10--12, printed pp.853--855;
G.11.1(3), printed p.364; 14.3.13--15, printed pp.993--995
(combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The original displaced center lies in the section centralizer from 12.8.11. -/
theorem displaced_center_le_section_centralizer :
    F.terminalDot (conjugate F.ZU g) ≤ Xdot₀ F F.terminalHatAction g := by
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hg := F.P_le_G₂ (by decide) (sourceResidual M Mc) h.L_normalizes_seed s.parabolic_mem
  have hm := Recognition.rankTwo_center_commutator_le_conjugate_point h F d s.nonabelian
    g s.parabolic_mem s.normalizer_not_mem
  rw [commutator_comm] at hm
  have hp : conjugate (F.Vi 1) g ≤ F.Vi 2 := by
    rw [F.plane_eq_point_join_conjugate (by decide) (sourceResidual M Mc)
      h.L_normalizes_seed g s.parabolic_mem s.normalizer_not_mem]
    exact le_sup_right
  intro x hx
  apply (mem_Xdot₀_iff F F.terminalHatAction F.terminalHatAction_apply_mk g hg x).mpr
  refine ⟨(map_mono (comap_mono (F.conjugate_ZU_le_X g))) hx,?_⟩
  obtain ⟨a,ha,rfl⟩ := hx
  intro w hw
  obtain ⟨u,hu,he⟩ := hw
  have hw : w = Additive.ofMul (QuotientGroup.mk' (center F.U) u) :=
    congrArg Additive.ofMul he.symm
  rw [hw]
  apply (Submodule.Quotient.eq _).mpr
  let u' := F.U.normalizerMonoidHom
    ⟨a,le_normalizer_conjugateSpanBy _ _ a.property⟩ u
  have hc : ((u' * u⁻¹ : F.U) : G) ∈ F.Vi 2 :=
    hp (hm (commutator_mem_commutator ha hu))
  refine ⟨u' * u⁻¹,hc,?_⟩
  rw [dotLinearAction_mk_apply,F.terminalHatAction_apply_mk]
  simp only [sub_eq_add_neg]
  change QuotientGroup.mk' (center F.U) (u' * u⁻¹) =
    QuotientGroup.mk' (center F.U) u' * (QuotientGroup.mk' (center F.U) u)⁻¹
  rw [map_mul,map_inv]

/-- A center larger than the point supplies an actual low-rank witness even
in the fixed-line branch. This uses the original displaced-center geometry. -/
theorem low_rank_of_center_ne_point (hZ : F.ZU ≠ F.Vi 1) :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  let L := sourceResidual M Mc
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hg := F.conjugate_center_le_H g (F.P_le_seed_normalizer L h.L_normalizes_seed s.parabolic_mem)
  have hne := F.terminalDot_center_ne_bot g hg
    (Recognition.rankTwo_terminal_center_kernel h F d s.nonabelian
      g s.parabolic_mem s.normalizer_not_mem)
    (lt_of_le_of_ne (F.point_le_ZU (by decide)) (Ne.symm hZ))
  have hsec : Xdot₀ F F.terminalHatAction g ≠ ⊥ := by
    intro he
    exact hne (le_bot_iff.mp (he ▸ s.displaced_center_le_section_centralizer))
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,_⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  let C := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
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
    change F.uhatBilinearForm (by decide) d.two d.frattini_point
      (Additive.ofMul (F.uhatAction a u)) (Additive.ofMul (F.uhatAction a w)) = _
    rw [F.uhatBilinearForm_apply,F.uhatCommutator_invariant (by decide) d.two d.frattini_point]
    rfl
  obtain ⟨x,hx,_,hr,hm⟩ := exists_lowRank_of_Xdot₀_ne_bot F (by decide) d.seed_center
    F.terminalHatAction g C.form C.nondegenerate C.alternating hzero hi hsec
  exact ⟨x,hx,hr,hm (s.marked_line.symm ▸ Submodule.mem_span_singleton_self v)⟩

/-- The only source branch not providing the low-rank classifier's witness
has the original center equal to the point and fixed space exactly the line. -/
theorem low_rank_or_extraspecial_fixed_line :
    ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∨
      (F.ZU = F.Vi 1 ∧ fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Submodule.span (ZMod 2) {v}) := by
  by_cases hZ : F.ZU = F.Vi 1
  · rcases s.fixed_point_alternative with hfix | hw
    · exact Or.inr ⟨hZ,hfix⟩
    · exact Or.inl hw
  · exact Or.inl (s.low_rank_of_center_ne_point hZ)


/-- Any remaining row (5) source has a larger center and hence the literal
low-rank witness. This does not yet exclude that remaining row. -/
theorem caseFive_center_and_low_rank
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    F.ZU ≠ F.Vi 1 ∧
      ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
  have hZ : F.ZU ≠ F.Vi 1 := fun he => s.not_caseFive_of_center_point he h5
  exact ⟨hZ,s.low_rank_of_center_ne_point hZ⟩

/-- The existing source degree sieve now confines its exceptional row to
the larger-center branch, with the actual low-rank input constructed. -/
theorem degree_cases_or_caseFive_center_above_point
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B
      (F.terminalDot (F.X g))) :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (ChapterG.Section11.CaseFive F.terminalRepresentation B ∧ F.ZU ≠ F.Vi 1 ∧
        ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) := by
  rcases s.degree_cases_or_caseFive hc with hd | h5
  · exact Or.inl hd
  · exact Or.inr ⟨h5,s.caseFive_center_and_low_rank h5⟩

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
