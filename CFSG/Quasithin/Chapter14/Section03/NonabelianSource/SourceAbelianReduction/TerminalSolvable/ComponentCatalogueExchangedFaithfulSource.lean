module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedContracts
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedRank
public import Theory.Frattini.PGroup

/-!
# Original faithful exchanged source and its Sylow commutator

This interface retains every original terminal hypothesis and every clause of
one fixed `ComponentOrbitSelection` witness. Properness and the faithful,
non-self-dual constituent data are the explicit inputs of the conditional
G.11.6 branch, to be supplied by the separate central-kernel argument. No
recognition conclusion is included.

The same source gives the exchanged orbit span and exact stabilizer degree.
Normality of X in the original dotted Sylow group proves the literal G.10.9(2)
commutator containment and its trivial Frattini subgroup. The remaining
SL3(4) exclusion must supply the conflicting model calculation.

Source: Aschbacher--Smith G.10.9(2), G.10.15(II), G.11.6, printed pp.360--366;
12.8.13 and 14.3.13--15, printed pp.855--856,993--994.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative

/-- All original source data, on the same selected constituent, together with
exactly the two explicit premises of the faithful exchanged task. -/
structure ExchangedFaithfulSource {G : Type*} [Group G] [Finite G]
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
    letI : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
    (⨆ a : F.TerminalHdot, conjugateSubrepresentation F.terminalRepresentation
      (componentOrbit L ⊤)
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I selected.invariant) a) = ⊤
  conjugate_disjoint : ∀ a : F.TerminalHdot,
    I.map (F.terminalRepresentation a) = I ∨ Disjoint (I.map (F.terminalRepresentation a)) I
  form_cases : (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∨ (B.restrict I).Nondegenerate
  dimension_gt_two : 2 < Module.finrank (ZMod 2) I
  independent : sSupIndep (subspaceOrbit F.terminalRepresentation (F.terminalDot (F.X g)) I)
  point_not_mem : v ∉ I
  proper : ¬ Function.Surjective
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      selected.invariant).toRepresentation.asGroupHom
  faithful_data : ExchangedFaithfulConstituentData F.terminalRepresentation B L
    (F.terminalDot (F.X g)) I selected

namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

/-- The selected component-orbit action, before any quotient. -/
abbrev orbitAction :=
  (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
    s.selected.invariant).toRepresentation

/-- The original dotted Sylow subgroup, rather than an arbitrary chosen Sylow. -/
abbrev sylow : Sylow 2 F.TerminalHdot :=
  (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)

include s

/-- The exchanged pair spans the whole original module; the exact stabilizer
acts faithfully both on the constituent and on its normal component orbit. -/
theorem completion :
    ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
    Homogeneous.orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I = ⊤ ∧
    let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))
    (∀ y : Y, (∀ u : I, F.terminalRepresentation ((y : F.terminalDot (F.X g)) : F.TerminalHdot) u = u) → y = 1) ∧
    (∀ y : Y, ((y : F.terminalDot (F.X g)) : F.TerminalHdot) ∈
      centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) → y = 1) :=
  Recognition.source_terminal_exchanged_constituent_completion s.simple T s.empty
    s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem s.proper

/-- The sharp degree on the literal subgroup N_X(I), with its inherited
binary vector-space structure. -/
theorem stabilizer_degree :
    let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf (F.terminalDot (F.X g))
    letI : IsElementaryAbelian 2 Y :=
      IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 :=
  source_exchanged_stabilizer_degree_eq s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected s.point_not_mem s.proper s.small_actor

/-- Source normality gives the actual G.10.9(2) commutator inside X∩H. -/
theorem sylow_commutator_le :
    ⁅F.terminalDot (F.X g),
      (sylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆ ≤
      F.terminalDot (F.X g) ⊓ componentOrbit L ⊤ := by
  obtain ⟨_,hXP,hN⟩ := Recognition.source_terminal_actor_normal_in_point_sylow
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis
  have hnorm := (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hnorm))
    ((commutator_mono le_rfl inf_le_right).trans (commutator_le_right _ _))

/-- The original source commutator is elementary, hence has trivial Frattini
subgroup. A model obstruction must contradict this actual subgroup. -/
theorem sylow_commutator_frattini :
    frattini (⁅F.terminalDot (F.X g),
      (sylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆ :
        Subgroup F.TerminalHdot) = ⊥ := by
  have hle := s.sylow_commutator_le.trans inf_le_left
  let : IsElementaryAbelian 2 (⁅F.terminalDot (F.X g),
      (sylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆ :
        Subgroup F.TerminalHdot) :=
    IsElementaryAbelian.of_injective (inclusion hle) (inclusion_injective hle)
  let : Fact (IsPGroup 2 (⁅F.terminalDot (F.X g),
      (sylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆ :
        Subgroup F.TerminalHdot)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
