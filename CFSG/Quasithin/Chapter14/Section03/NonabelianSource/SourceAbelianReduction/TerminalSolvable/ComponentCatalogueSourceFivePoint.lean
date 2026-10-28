module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSeedModule
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5WholeAction

/-!
# The full five-point group in the original larger-actor branch

The original degree alternatives, component catalogue and A₆/G₂ exclusions
supply a normalized A₅ lift in degree four. Applying the whole-action
construction identifies the actual full dotted group and carries its
five-point action together with that same lift and the original seed.
No degree, component-recognition or action-model premise is added.

This removes those local inputs from the larger-actor field-four recognition
step. The terminal-solvability owner still owes the ambient field-four
recognition and Borel contradiction; the independently owned L₂(8) source
exclusion remains necessary for final assembly.
Source: Aschbacher–Smith 14.3.6 and 14.3.14–15, printed pp.991,993–994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
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

/-- The actual full dotted group in the original larger-actor branch is A₅ or S₅. -/
theorem terminal_alternating_five_or_symmetric_five :
    Nonempty (F.TerminalHdot ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨K,hK,⟨e5⟩,hspan⟩ := s.exists_normalized_a5_lift
  exact source_single_a5_whole_group_of_four s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
    F s.nonabelian s.not_model g s.parabolic_mem s.normalizer_not_mem s.hypothesis
    hK e5 hspan s.degree_eq_four

/-- The original larger-actor source supplies the whole five-point action
and its singular seed, retaining the selected component and its marking. -/
theorem exists_marked_five_point_lift :
    ∃ K : Subgroup G, ComponentLift F g K ∧
      K = conjugateSpanBy K (T : Subgroup G) ∧
      ∃ (e5 : F.terminalDot K ≃* alternatingGroup (Fin 5))
        (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
        (p : F.TerminalHdot →* Equiv.Perm (Fin 5)) (w : Additive F.Uhat),
        Function.Injective p ∧
        (∀ l : F.terminalDot K, p l = (e5 l).val) ∧
        (∀ a x, c (F.terminalRepresentation a x) =
          BinaryPermutation.coreRepresentation (Fin 5) (p a) (c x)) ∧
        w ≠ 0 ∧ hatSpace F (rankTwoSeed T M) = Submodule.span (ZMod 2) {w} ∧
        BinaryPermutation.FiveGeometry.form (c w) = 0 ∧
        ∀ a : F.H, (a : G) ∈ M →
          BinaryPermutation.coreRepresentation (Fin 5)
            (p (QuotientGroup.mk' F.terminalHatAction.ker a)) (c w) = c w := by
  obtain ⟨K,hK,⟨e5⟩,hspan⟩ := s.exists_normalized_a5_lift
  exact ⟨K,hK,hspan,e5,source_single_a5_whole_action_seed_of_four s.simple T s.empty
    s.maximal s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
    F s.nonabelian s.not_model g s.parabolic_mem s.normalizer_not_mem s.hypothesis
    hK e5 hspan s.degree_eq_four⟩

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
