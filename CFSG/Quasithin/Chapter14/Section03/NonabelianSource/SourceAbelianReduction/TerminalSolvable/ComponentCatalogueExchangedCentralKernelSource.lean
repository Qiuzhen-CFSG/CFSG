module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedRank
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedContracts
public import Theory.Frattini.PGroup

/-!
# The literal central-kernel source and its Sylow restrictions

This interface retains all original terminal hypotheses and every clause of
one selected constituent witness. Its central-kernel field concerns the
literal action on that same constituent; it does not assert faithfulness.
The source Sylow normality proves the elementary commutator and trivial
Frattini restriction in G.10.9. Triviality of the ambient two-core descends
to the normal component orbit.

These are inputs to the two independent remaining model arguments: exclusion
of full GL, and exclusion of a nondegenerate exchanged constituent. Neither
model conclusion is included in the source structure.

Source: Aschbacher--Smith G.10.9 and G.10.15, printed pp.360--363;
14.3.12--15, printed pp.993--994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative

/-- The original exchanged central-kernel branch, with the same selected
constituent throughout. Every field is an original hypothesis or one of the
proved geometric selection conclusions. -/
structure ExchangedCentralSource {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M Mc : Subgroup G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (L : Subgroup F.TerminalHdot) (I : Submodule (ZMod 2) (Additive F.Uhat)) : Prop where
  simple : IsSimpleQTKE KnownSimple.IsKnownSimple G
  empty : MainForward.faithfulLocalComponents T = ∅
  maximal : IsOrderingMaximal T M
  unique_overgroup : maximalTwoLocalOvergroups
    (centralizer (centralInvolutions T : Set G)) = {Mc}
  many_overgroups : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  seed_card : Nat.card (localModule T M) = 4
  centralizer_quotient : Nonempty
    ((M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
  not_model : ¬ ClassificationModels.IsTheoremEModel G
  nonabelian : ¬ IsMulCommutative F.U
  parabolic_mem : g ∈ F.P (sourceResidual M Mc)
  normalizer_not_mem : g ∉ F.H
  nonsolvable : ¬ Group.IsSolvable F.TerminalHdot
  hypothesis : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))
  small_actor : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
    Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  component : IsComponent F.TerminalHdot L
  moved : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥
  orthogonal : ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L
  fixedSpace_eq_bot : fixedSpace F.terminalRepresentation (componentOrbit L ⊤) = ⊥
  commutator_eq_top : subspaceCommutator F.terminalRepresentation ⊤ (componentOrbit L ⊤) = ⊤
  selected : Homogeneous.IsIrrPlusWith F.terminalRepresentation
    (componentOrbit L ⊤) (F.terminalDot (F.X g)) I
  irreducible : IsIrreducible
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I selected.invariant).toRepresentation
  conjugate_span :
    let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
    (⨆ a : F.TerminalHdot, conjugateSubrepresentation F.terminalRepresentation
      (componentOrbit L ⊤)
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I selected.invariant) a) = ⊤
  conjugate_disjoint : ∀ a : F.TerminalHdot,
    I.map (F.terminalRepresentation a) = I ∨ Disjoint (I.map (F.terminalRepresentation a)) I
  form_cases : (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∨ (B.restrict I).Nondegenerate
  dimension_gt_two : 2 < Module.finrank (ZMod 2) I
  independent : sSupIndep (subspaceOrbit F.terminalRepresentation (F.terminalDot (F.X g)) I)
  point_not_mem : v ∉ I
  central_kernel :
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      selected.invariant).toRepresentation.asGroupHom.ker ≤
        Subgroup.center (componentOrbit L ⊤)

namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

/-- The Sylow subgroup obtained from the original T, with its literal quotient map. -/
abbrev pointSylow : Sylow 2 F.TerminalHdot :=
  (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)

include s

/-- Normality of the normal component orbit transfers the original G.10.3
conclusion to its intrinsic two-core. -/
theorem orbit_twoCore_eq_bot : pCore 2 (componentOrbit L ⊤) = ⊥ := by
  let hn := componentOrbit_top_normal L
  rw [pCore_subnormal_eq_comap 2 hn.isSubnormal, s.hypothesis.twoCore_eq_bot]
  apply bot_unique
  intro x hx
  exact mem_bot.mpr (Subtype.ext (show (x : F.TerminalHdot) = 1 from hx))

/-- The original actor is contained in, and normalized by, the actual source Sylow. -/
theorem actor_sylow :
    F.terminalDot (F.X g) ≤ (pointSylow (F := F) : Subgroup F.TerminalHdot) ∧
    (pointSylow (F := F) : Subgroup F.TerminalHdot) ≤
      normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) := by
  obtain ⟨_,hXP,hN⟩ := Recognition.source_terminal_actor_normal_in_point_sylow
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis
  exact ⟨hXP,(normal_subgroupOf_iff_le_normalizer hXP).mp hN⟩

/-- G.10.9(2) on the literal original actor and the original Sylow intersection.
Its Frattini subgroup is intrinsic to the commutator subgroup. -/
theorem sylow_commutator :
    let C := ⁅F.terminalDot (F.X g),
      (pointSylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆
    C ≤ F.terminalDot (F.X g) ⊓ componentOrbit L ⊤ ∧
    IsElementaryAbelian 2 C ∧ frattini C = ⊥ := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let C := ⁅F.terminalDot (F.X g),
    (pointSylow (F := F) : Subgroup F.TerminalHdot) ⊓ H⁆
  have hCX : C ≤ F.terminalDot (F.X g) :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans s.actor_sylow.2)
  have hCH : C ≤ H :=
    (commutator_mono le_rfl inf_le_right).trans (commutator_le_right _ _)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hCX) (inclusion_injective hCX)
  let : Fact (IsPGroup 2 C) := ⟨IsElementaryAbelian.isPGroup 2 C⟩
  exact ⟨le_inf hCX hCH,inferInstance,frattini_eq_bot_of_isElementaryAbelian (p := 2)⟩


end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
