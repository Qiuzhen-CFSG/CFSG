module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedTransport
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SourceNonsolvable.Homogeneous

/-!
# Original marked-constituent data and its image transport

The original G.10 geometry supplies homogeneity, faithful action of the
normal component orbit and self-duality of its selected constituent. The
results below descend that self-duality to the actual constituent action
quotient and identify its actor kernel with the original orbit centralizer.
Concrete image rows then transport through the literal local component
lift and intrinsic two-core quotient from ComponentCatalogue.

MarkedSource retains the original hypotheses and every geometric clause
of the chosen ComponentOrbitSelection witness, including the same I. Its
ImageCases predicate is an output obligation: faithful-actor recognition
and the nonfaithful homogeneous-multiplicity branch remain unproved.
No model classification or desired conclusion is included in the input.

Source: Aschbacher--Smith, G.10.15(I), G.11.6--9, printed pp.361,366--369;
12.8.13 and 14.3.12--15, printed pp.855--856,993--994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-orbit self-duality used by the original marked classifier,
now on the literal constituent action quotient. -/
theorem source_marked_constituent_image_selfDual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) I)
    (hv : v ∈ I) :
    let H := componentOrbit L ⊤
    let : H.Normal := componentOrbit_top_normal L
    let hXI := hyp.stabilizes_constituent_of_point_mem
      (hyp.irreducible_of_not_solvable hn) H hI hv
    let σ := MarkedAction.action F.terminalRepresentation H
      (F.terminalDot (F.X g)) I hI.choose hXI
    let Hbar := MarkedAction.image F.terminalRepresentation H (F.terminalDot (F.X g)) I hI.choose hXI H
    Nonempty (Representation.Equiv ((kerRepresentation σ).comp Hbar.subtype)
      (Representation.dual ((kerRepresentation σ).comp Hbar.subtype))) := by
  intro H hnormal hXI σ Hbar
  exact MarkedAction.selfDual_image F.terminalRepresentation H
    (F.terminalDot (F.X g)) I hI.choose hXI
    (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hL hm hI hv).2.2.1

/-- Original C_X(I)=C_X(H), with the chosen constituent and original dotted
actor, including the case where X has a nontrivial constituent kernel. -/
theorem source_marked_constituent_fixes_iff_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) I)
    (hv : v ∈ I)
    (x : F.terminalDot (F.X g)) :
    (∀ w : I, F.terminalRepresentation x w = w) ↔
      (x : F.TerminalHdot) ∈ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  have hXI := hyp.stabilizes_constituent_of_point_mem
    (hyp.irreducible_of_not_solvable hn) H hI hv
  have hf := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hL hm hI hv).2.1
  exact MarkedAction.fixes_iff_centralizes F.terminalRepresentation H
    (F.terminalDot (F.X g)) I hI.choose hXI hf
    (hI.irreducible_of_normal_restriction F.terminalRepresentation
      (hyp.irreducible_of_not_solvable hn) H) ⟨v,hv⟩
    (fun he => hyp.point_ne_zero (congrArg Subtype.val he)) x (hyp.fixes_point x.property)

/-- The actual terminal-component application of constituent image transport.
The remaining premise is explicitly the still-unproved recognition output. -/
theorem source_marked_component_cases_of_constituent_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) I)
    (hv : v ∈ I) :
    let H := componentOrbit L ⊤
    let : H.Normal := componentOrbit_top_normal L
    let hXI := hyp.stabilizes_constituent_of_point_mem
      (hyp.irreducible_of_not_solvable hn) H hI hv
    ComponentOrbitImageCases (MarkedAction.image F.terminalRepresentation H (F.terminalDot (F.X g)) I hI.choose hXI L)
      (MarkedAction.image F.terminalRepresentation H (F.terminalDot (F.X g)) I hI.choose hXI H) →
      ComponentImageCases L := by
  intro H hnormal hXI hc
  have hf := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hL hm hI hv).2.1
  exact MarkedAction.componentImageCases F.terminalRepresentation H
    (F.terminalDot (F.X g)) I hI.choose hXI hf L (le_componentOrbit L ⊤) hc


/-- The source faithful/nonfaithful split can be made on the literal
centralizer intersection, with no replacement of the original actor. -/
theorem source_marked_actor_faithful_iff
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) I)
    (hv : v ∈ I) :
    Function.Injective (fun x : F.terminalDot (F.X g) =>
      (F.terminalRepresentation (x : F.TerminalHdot)).comp I.subtype) ↔
      F.terminalDot (F.X g) ⊓
        centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) = ⊥ := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  have hXI := hyp.stabilizes_constituent_of_point_mem
    (hyp.irreducible_of_not_solvable hn) H hI hv
  have hf := (Recognition.source_terminal_constituent_homogeneous_of_point_mem
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hL hm hI hv).2.1
  exact MarkedAction.actor_faithful_iff F.terminalRepresentation H
    (F.terminalDot (F.X g)) I hI.choose hXI hf
    (hI.irreducible_of_normal_restriction F.terminalRepresentation
      (hyp.irreducible_of_not_solvable hn) H) ⟨v,hv⟩
    (fun he => hyp.point_ne_zero (congrArg Subtype.val he))
    (fun x => hyp.fixes_point x.property)


/-- The original marked branch, retaining the exact selected constituent.
Every field is a source hypothesis or a conclusion of the already proved
constituent selection. No group-model or image-recognition field is present. -/
structure MarkedSource {G : Type*} [Group G] [Finite G]
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
  point_mem : v ∈ I

namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)

/-- The literal source actor's faithfulness on the selected subspace. -/
def ActorFaithful : Prop :=
  Function.Injective (fun x : F.terminalDot (F.X g) =>
    (F.terminalRepresentation (x : F.TerminalHdot)).comp I.subtype)

include s

/-- X preserves this same constituent through the marked point. -/
theorem actor_stabilizes : F.terminalDot (F.X g) ≤
    subspaceStabilizer F.terminalRepresentation I := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  exact s.hypothesis.stabilizes_constituent_of_point_mem
    (s.hypothesis.irreducible_of_not_solvable s.nonsolvable)
    (componentOrbit L ⊤) s.selected.isIrrPlus s.point_mem

/-- The model-recognition target on the actual constituent quotient.
This definition supplies no witness of the classification. -/
def ImageCases : Prop :=
  ComponentOrbitImageCases
    (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L)
    (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes (componentOrbit L ⊤))

/-- Apply the proved original-source transport to the complete selected data.
Image recognition remains an explicit premise for the two branch owners. -/
theorem componentImageCases (hc : s.ImageCases) : ComponentImageCases L :=
  source_marked_component_cases_of_constituent_image s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem hc

/-- The exact original centralizer intersection is the actor kernel test. -/
theorem actorFaithful_iff : ActorFaithful (F := F) (g := g) (I := I) ↔
    F.terminalDot (F.X g) ⊓ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) = ⊥ :=
  source_marked_actor_faithful_iff s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.nonsolvable s.hypothesis s.component s.moved
    s.selected.isIrrPlus s.point_mem

/-- Feed the recognized constituent images into the parent's literal local
lift and intrinsic two-core quotient. The only extra premise is recognition. -/
theorem local_lift_of_image_cases (hc : s.ImageCases) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  source_component_catalogue_of_small_actor_image s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis s.small_actor s.component s.moved
    (s.componentImageCases hc)

end MarkedSource

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
