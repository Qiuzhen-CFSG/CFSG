module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelSource
public import Theory.Representation.NormalComponentConstituents.FullLinear
public import Theory.GroupTheory.ElementaryOuterSylow
public import Theory.LinearAlgebra.BinaryInvariantAlternating

/-!
# The faithful full-linear reduction of the exchanged central-kernel branch

Surjectivity makes the selected constituent image centerless. Ambient
irreducibility then kills the center of the normal component orbit, so the
literal central constituent kernel vanishes. The original geometry selects
a moved involution, and homogeneous selection makes its conjugation outer.
The source Sylow restricts to the component orbit and supplies elementary
Sylow displacements. All maps concern the same original selected constituent.

The two remaining inputs are explicit: the linear-group obstruction away
from degree four, and the degree-four exclusion using the original action
and small-actor bound. An outer transposition on A8 shows why elementary
Sylow displacements alone cannot exclude degree four. The conditional final
reduction below does not assert the completed source theorem.

Source: Aschbacher--Smith G.10.9 and G.10.15(3), printed pp.360,363.
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

/-- The literal constituent map is faithful under the full-image hypothesis.
This uses the original faithful irreducible ambient action, with no multiplier
or assumed constituent-faithfulness premise. -/
theorem fullLinear_faithful
    (hs : Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom) :
    Function.Injective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  have hne : I ≠ ⊥ := by
    intro he
    have hd := s.dimension_gt_two
    rw [he,finrank_bot] at hd
    omega
  exact faithful_constituent_of_centerless_surjective F.terminalRepresentation
    s.hypothesis.faithful (s.hypothesis.irreducible_of_not_solvable s.nonsolvable)
    (componentOrbit L ⊤) I s.selected.invariant hne hs
    (binary_full_center_eq_bot (by have := s.dimension_gt_two; omega)) s.central_kernel

/-- The full-image isomorphism is the original constituent action itself. -/
@[expose] def fullLinearEquiv
    (hs : Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom) :
    (componentOrbit L ⊤) ≃* LinearMap.GeneralLinearGroup (ZMod 2) I :=
  MulEquiv.ofBijective _ ⟨s.fullLinear_faithful hs, hs⟩

theorem fullLinearEquiv_apply
    (hs : Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom)
    (a : componentOrbit L ⊤) :
    s.fullLinearEquiv hs a = (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom a := rfl

/-- The selected constituent supplies an actual outer involution, together
with the original Sylow intersection and elementary displacement subgroup. -/
theorem exists_outer_sylow_action : Nonempty (ElementaryOuterSylowAction (componentOrbit L ⊤)) := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  obtain ⟨x,hx,_⟩ := s.hypothesis.exchanged_constituent_geometry s.nonsolvable
    s.component s.moved (pointSylow (F := F)) s.actor_sylow.2
    (Recognition.terminal_component_normalizer_index_le_two s.simple F (by decide) L s.component)
    s.selected s.point_not_mem
  have hxi : (x : F.TerminalHdot)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (x : F.TerminalHdot) x.property)
  have ho := s.selected.conjugation_not_inner F.terminalRepresentation
    s.fixedSpace_eq_bot x (by rwa [hxi])
  exact ⟨ElementaryOuterSylowAction.of_normal_elementary (componentOrbit L ⊤)
    (pointSylow (F := F)) (F.terminalDot (F.X g)) s.actor_sylow.1 s.actor_sylow.2 x ho⟩

/-- Full binary linear image forces the original restricted alternating
form to vanish, without any spanning or properness premise. -/
theorem fullLinear_isotropic
    (hs : Function.Surjective (invariantSubspace F.terminalRepresentation
      (componentOrbit L ⊤) I s.selected.invariant).toRepresentation.asGroupHom) :
    ∀ u ∈ I, ∀ w ∈ I, B u w = 0 := by
  have hz : B.restrict I = 0 := (B.restrict I).eq_zero_of_full_binary_linear_invariance
    (fun u => s.hypothesis.alternating u) (fun e u w => by
      obtain ⟨a,ha⟩ := hs ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).symm e)
      have he := congrArg (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I) ha
      change LinearMap.GeneralLinearGroup.toLinearEquiv
        ((invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
          s.selected.invariant).toRepresentation.asGroupHom a) = e at he
      rw [← he]
      exact s.hypothesis.preserves a u w)
    (by have := s.dimension_gt_two; omega)
  intro u hu w hw
  exact LinearMap.congr_fun (LinearMap.congr_fun hz (⟨u,hu⟩ : I)) (⟨w,hw⟩ : I)

/-- Final reduction to two separate obligations: the native linear Sylow
bound, and the original-source degree-four exclusion. Both remain explicit. -/
theorem not_fullLinear_of_outer_bound_and_four
    (hbound : ∀ (_a : ElementaryOuterSylowAction (componentOrbit L ⊤))
      (_e : (componentOrbit L ⊤) ≃* LinearMap.GeneralLinearGroup (ZMod 2) I),
      finrank (ZMod 2) I = 4)
    (hfour : finrank (ZMod 2) I = 4 → ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom) :
    ¬ Function.Surjective (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom := by
  intro hs
  obtain ⟨a⟩ := s.exists_outer_sylow_action
  exact hfour (hbound a (s.fullLinearEquiv hs)) hs

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
