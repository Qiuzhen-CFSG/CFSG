module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelFullLinear
public import Theory.Representation.FullLinearOuterAction.Four

/-!
# Representation and rank reductions for the degree-four full-linear branch

An outer conjugation action commutes with the constituent stabilizer. If the
constituent lay in the marked axis, its full-center action would contradict
the outer full-center obstruction. Once it escapes the axis, G.10.10 applied
to the orthogonal complement makes its two-member orbit span the ambient
space. The original small-actor equality then gives an actor of order eight.

The full-center obstruction is discharged by point-radical rigidity. The
final conditional consumer retains just the lower bound sixteen for a normal
elementary Sylow actor inducing an outer degree-four linear automorphism.
That group calculation remains explicit, so this is not yet the exclusion.
Source: Aschbacher--Smith G.10.15(3), printed p.363, with the original
small-actor bound from 14.3.12, printed p.993.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- The outer full-center obstruction excludes containment in the marked axis,
using the original constituent action and the commuting original actor. -/
theorem fullLinear_not_le_axis_of_center_obstruction
    (hcenter : FullCenterOuterObstruction I)
    (hs : Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom) :
    ¬ I ≤ (B v).ker := by
  intro haxis
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  obtain ⟨x,hx,_,_,_,hgeo⟩ := s.hypothesis.exchanged_constituent_geometry s.nonsolvable
    s.component s.moved (pointSylow (F := F)) s.actor_sylow.2
    (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
    s.selected s.point_not_mem
  have haxis' : I ⊓ (B v).ker = I := inf_eq_left.mpr haxis
  dsimp only at hgeo
  rw [haxis'] at hgeo
  obtain ⟨i,hi0,_,_,hfull⟩ := hgeo
  have hxi : (x : F.TerminalHdot)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : F.TerminalHdot) x.property)
  have ho := s.selected.conjugation_not_inner F.terminalRepresentation
    s.fixedSpace_eq_bot x (by rwa [hxi])
  let e := s.fullLinearEquiv hs
  let a := MulAut.congr e (MulAut.conjNormal (x : F.TerminalHdot))
  have hoa : a ∉ MulAut.innerSubgroup _ := by
    intro ha
    rw [← MulAut.map_innerSubgroup_congr e] at ha
    obtain ⟨b,hb,he⟩ := ha
    exact ho ((MulAut.congr e).injective he ▸ hb)
  apply hcenter a hoa i (fun he => hi0 (congrArg Subtype.val he))
  intro f hf
  obtain ⟨y,hy⟩ := hfull.full f hf
  let y' : subspaceStabilizer F.terminalRepresentation I := ⟨(y.val : F.TerminalHdot),y.property⟩
  have haction : (stabilizerRepresentation F.terminalRepresentation I).asGroupHom y' =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).symm
        (BinaryLinear.transvection i f hf) := by
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    exact hy u
  have hcomm : Commute (y' : F.TerminalHdot) (x : F.TerminalHdot) :=
    congrArg Subtype.val (mul_comm y.val x)
  have hfix := normal_full_action_fixed_of_commute F.terminalRepresentation
    (componentOrbit L ⊤) I s.selected.invariant e (s.fullLinearEquiv_apply hs)
    (binary_full_center_eq_bot (by have := s.dimension_gt_two; omega)) x y' hcomm
  rw [haction] at hfix
  exact hfix

/-- The original degree-four full-linear constituent escapes the marked axis.
Point-radical rigidity discharges the outer full-center obstruction. -/
theorem fullLinear_four_not_le_axis (hd : finrank (ZMod 2) I = 4)
    (hs : Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom) :
    ¬ I ≤ (B v).ker :=
  s.fullLinear_not_le_axis_of_center_obstruction (fullCenterOuterObstruction_four hd) hs

/-- Escaping the marked axis suffices for orbit spanning. This proof uses
G.10.10 directly and does not invoke the non-GL assertion. -/
theorem orbitSpan_eq_top_of_not_le_axis (haxis : ¬ I ≤ (B v).ker) :
    Homogeneous.orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I = ⊤ := by
  let O := Homogeneous.orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I
  have hHI := Homogeneous.orbitSpan_component_invariant F.terminalRepresentation
    s.selected.normalizes s.selected.isIrrPlus
  have hXI := Homogeneous.orbitSpan_invariant F.terminalRepresentation (F.terminalDot (F.X g)) I
  have horth : B.orthogonal O = ⊥ := by
    by_contra hne
    have hvO := s.hypothesis.point_mem_normal_component_subspace s.nonsolvable
      s.component s.moved (pointSylow (F := F)) s.actor_sylow.2
      (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
      (B.orthogonal O) (orthogonal_invariant F.terminalRepresentation B s.hypothesis.preserves hHI)
      (orthogonal_invariant F.terminalRepresentation B s.hypothesis.preserves hXI) hne
    apply haxis
    intro u hu
    exact s.hypothesis.alternating.isRefl u v
      (hvO u (Homogeneous.le_orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I hu))
  have hh := B.orthogonal_orthogonal s.hypothesis.nondegenerate s.hypothesis.alternating.isRefl O
  rw [horth,LinearMap.BilinForm.orthogonal_bot] at hh
  exact hh.symm

/-- The original degree-four branch has actor order eight once the constituent
escapes the marked axis. The source small-actor equality is used essentially. -/
theorem fullLinear_four_actor_card_of_not_le_axis
    (hd : finrank (ZMod 2) I = 4) (haxis : ¬ I ≤ (B v).ker) :
    Nat.card (F.terminalDot (F.X g)) = 8 := by
  have hspan := s.orbitSpan_eq_top_of_not_le_axis haxis
  obtain ⟨x,_,hpair,hdis,_,_⟩ := s.hypothesis.exchanged_constituent_geometry s.nonsolvable
    s.component s.moved (pointSylow (F := F)) s.actor_sylow.2
    (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
    s.selected s.point_not_mem
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq I (I.map (F.terminalRepresentation x))
  rw [hdis.eq_bot,finrank_bot,add_zero,finrank_map_action,hd,← hpair,hspan,finrank_top] at hdim
  have hr := (s.hypothesis.numerical_equality_of_actor_dimension_le s.small_actor).2.1
  have he : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 := by omega
  change Nat.card (Additive (F.terminalDot (F.X g))) = 8
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,he]
  norm_num

/-- Under the actual full-image hypothesis, the original degree-four actor
has order eight. No spanning, axis or faithfulness premise is added. -/
theorem fullLinear_four_actor_card (hd : finrank (ZMod 2) I = 4)
    (hs : Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom) :
    Nat.card (F.terminalDot (F.X g)) = 8 :=
  s.fullLinear_four_actor_card_of_not_le_axis hd (s.fullLinear_four_not_le_axis hd hs)

/-- Conditional final consumer of the remaining degree-four Sylow calculation.
Its lower-bound premise must be discharged before claiming G.10.15(3). -/
theorem not_fullLinear_four_of_outer_rank
    (hd : finrank (ZMod 2) I = 4)
    (hlarge : ∀ (_e : (componentOrbit L ⊤) ≃* LinearMap.GeneralLinearGroup (ZMod 2) I)
      (x : F.terminalDot (F.X g)),
      letI := componentOrbit_top_normal L
      (MulAut.conjNormal (x : F.TerminalHdot) : MulAut (componentOrbit L ⊤)) ∉
        MulAut.innerSubgroup (componentOrbit L ⊤) → 16 ≤ Nat.card (F.terminalDot (F.X g))) :
    ¬ Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom := by
  intro hs
  have hc := s.fullLinear_four_actor_card hd hs
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  obtain ⟨x,hx,_,_,_,_⟩ := s.hypothesis.exchanged_constituent_geometry s.nonsolvable
    s.component s.moved (pointSylow (F := F)) s.actor_sylow.2
    (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
    s.selected s.point_not_mem
  have hxi : (x : F.TerminalHdot)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : F.TerminalHdot) x.property)
  have ho := s.selected.conjugation_not_inner F.terminalRepresentation
    s.fixedSpace_eq_bot x (by rwa [hxi])
  have hl := hlarge (s.fullLinearEquiv hs) x ho
  omega

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
