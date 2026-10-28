module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedTransport
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedTransport

/-!
# The literal exchanged constituent action

The actor is N_X(I), embedded in the dotted group as X intersected with the
subspace stabilizer. Its action quotient is exactly Aut_HY(I). The original
orbit-span theorem makes this actor faithful, so the quotient preserves its
rank. The faithful component-orbit action identifies H with its literal image;
non-self-duality, properness and irreducibility transfer with the same action.

These supply the numerical and representation inputs of G.9.3 in G.11.6.
The moved component and its possible dual-quasiequivalent partner still need
to be established on this quotient before applying the classification.
Source: Aschbacher--Smith G.11.6, printed p.366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
namespace ExchangedAction
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H X : Subgroup D)
  (I : Submodule (ZMod 2) W) (hH : H ≤ subspaceStabilizer ρ I)

abbrev stabilizer := (subspaceStabilizer ρ I).subgroupOf X
abbrev actor := subspaceStabilizer ρ I ⊓ X

/-- The literal subgroup of X and its embedded subgroup of D. -/
def stabilizerEquiv : stabilizer ρ X I ≃* actor ρ X I where
  toFun y := ⟨y.val, y.property, y.val.property⟩
  invFun y := ⟨⟨y.val,y.property.2⟩,y.property.1⟩
  map_mul' _ _ := rfl

abbrev action := MarkedAction.action ρ H (actor ρ X I) I hH inf_le_left
abbrev quotient := MarkedAction.quotient ρ H (actor ρ X I) I hH inf_le_left
abbrev projection := MarkedAction.projection ρ H (actor ρ X I) I hH inf_le_left
abbrev image (J : Subgroup D) := MarkedAction.image ρ H (actor ρ X I) I hH inf_le_left J
abbrev imageAction := kerRepresentation (action ρ H X I hH)

/-- Faithfulness of H on I gives the actual orbit-image isomorphism. -/
def orbitEquiv (hf : Function.Injective (invariantSubspace ρ H I hH).toRepresentation) :
    H ≃* image ρ H X I hH H :=
  MarkedAction.subgroupEquiv ρ H (actor ρ X I) I hH inf_le_left hf H le_rfl

/-- A faithful stabilizer is isomorphic to its actual quotient image. -/
def actorEquiv (hf : Function.Injective
    (invariantSubspace ρ (actor ρ X I) I inf_le_left).toRepresentation) :
    actor ρ X I ≃* image ρ H X I hH (actor ρ X I) := by
  let A := actor ρ X I
  let P := H ⊔ A
  let eA := subgroupOfEquivOfLe (show A ≤ P from le_sup_right)
  refine eA.symm.trans (ChapterG.Section09.actionImageEquiv
    (action ρ H X I hH) (imageAction ρ H X I hH)
    (projection ρ H X I hH) rfl (A.subgroupOf P) ?_)
  intro a b hab
  apply eA.injective
  apply hf
  exact hab

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
/-- Non-self-duality transfers for the fixed H-action, without an outer twist. -/
theorem image_not_selfDual
    (hn : ¬ Nonempty (Representation.Equiv
      (invariantSubspace ρ H I hH).toRepresentation
      (invariantSubspace ρ H I hH).toRepresentation.dual)) :
    ¬ Nonempty (Representation.Equiv
      ((imageAction ρ H X I hH).comp (image ρ H X I hH H).subtype)
      (Representation.dual ((imageAction ρ H X I hH).comp (image ρ H X I hH H).subtype))) := by
  rintro ⟨e⟩
  apply hn
  refine ⟨Representation.Equiv.mk e.toLinearEquiv ?_⟩
  intro a
  let b : (H ⊔ actor ρ X I : Subgroup D) := ⟨a,(show H ≤ H ⊔ actor ρ X I from le_sup_left) a.property⟩
  exact e.isIntertwining' ⟨projection ρ H X I hH b,mem_map.mpr ⟨b,a.property,rfl⟩⟩

omit [Finite D] [FiniteDimensional (ZMod 2) W] in
/-- The proper linear image is unchanged by the literal action quotient. -/
theorem image_not_surjective
    (hn : ¬ Function.Surjective (invariantSubspace ρ H I hH).toRepresentation.asGroupHom) :
    ¬ Function.Surjective
      (Representation.asGroupHom ((imageAction ρ H X I hH).comp (image ρ H X I hH H).subtype)) := by
  intro hs
  apply hn
  intro z
  obtain ⟨a,ha⟩ := hs z
  obtain ⟨b,hb,hba⟩ := mem_map.mp a.property
  have he : (⟨projection ρ H X I hH b,mem_map.mpr ⟨b,hb,rfl⟩⟩ :
      image ρ H X I hH H) = a := Subtype.ext hba
  rw [← he] at ha
  exact ⟨⟨b,hb⟩,ha⟩

/-- Recognition of the actual image of H recognizes the original component
and gives its ambient normality, using the parent's A7 transport. -/
theorem componentImageCases_of_image_alternating_seven
    {L : Subgroup D} (hL : IsComponent D L) (hH_eq : H = componentOrbit L ⊤)
    (hf : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    (e : image ρ H X I hH H ≃* alternatingGroup (Fin 7)) : ComponentImageCases L := by
  have er := (orbitEquiv ρ H X I hH hf).trans e
  subst H
  exact component_image_cases_of_orbit_alternating_seven hL er

end ExchangedAction

open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

abbrev actor := ExchangedAction.actor F.terminalRepresentation (F.terminalDot (F.X g)) I
abbrev action := ExchangedAction.action F.terminalRepresentation (componentOrbit L ⊤)
  (F.terminalDot (F.X g)) I s.selected.invariant
abbrev actionQuotient := ExchangedAction.quotient F.terminalRepresentation (componentOrbit L ⊤)
  (F.terminalDot (F.X g)) I s.selected.invariant
abbrev projection := ExchangedAction.projection F.terminalRepresentation (componentOrbit L ⊤)
  (F.terminalDot (F.X g)) I s.selected.invariant
abbrev image (J : Subgroup F.TerminalHdot) :=
  ExchangedAction.image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant J
abbrev imageAction := kerRepresentation s.action

include s

/-- The explicit faithful constituent input, as injectivity of its linear action. -/
theorem orbit_faithful : Function.Injective s.orbitAction := by
  intro a b hab
  exact s.faithful_data.1 (Units.ext hab)

/-- The exchanged actor on I is faithful because its X-orbit spans the original
faithful module. This is not the marked-point X-action. -/
theorem actor_faithful : Function.Injective
    (invariantSubspace F.terminalRepresentation
      (actor (F := F) (g := g) (I := I)) I inf_le_left).toRepresentation :=
  s.hypothesis.spanning_constituent_stabilizer_faithful s.completion.2.1

/-- The actor's cardinality on the embedded literal stabilizer, at degree dim I−2. -/
theorem actor_card : Nat.card (actor (F := F) (g := g) (I := I)) =
    2 ^ (finrank (ZMod 2) I - 2) := by
  let X := F.terminalDot (F.X g)
  let Y := (subspaceStabilizer F.terminalRepresentation I).subgroupOf X
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  have hd : finrank (ZMod 2) I = finrank (ZMod 2) (Additive Y) + 2 :=
    s.stabilizer_degree
  have hc : Nat.card Y = 2 ^ finrank (ZMod 2) (Additive Y) := by
    change Nat.card (Additive Y) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have he := Nat.card_congr
    (ExchangedAction.stabilizerEquiv F.terminalRepresentation X I).toEquiv
  rw [← he,hc]
  congr 1
  omega

omit [Finite G] [IsElementaryAbelian 2 (rankTwoSeed T M)] s in
/-- The embedded stabilizer inherits elementary abelianness from the original X. -/
theorem actor_elementary : IsElementaryAbelian 2 (actor (F := F) (g := g) (I := I)) :=
  IsElementaryAbelian.of_injective (inclusion (show
    actor (F := F) (g := g) (I := I) ≤ F.terminalDot (F.X g) from inf_le_right))
    (inclusion_injective _)

/-- The actor is unchanged by passing to Aut_HY(I), because its action is faithful. -/
def actorEquiv : actor (F := F) (g := g) (I := I) ≃*
    s.image (actor (F := F) (g := g) (I := I)) :=
  ExchangedAction.actorEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_faithful

/-- The literal faithful action image satisfies all numerical hypotheses G.9.1,
with m=dim(I)−2, without a classification assumption. -/
theorem image_setup : ChapterG.Section09.Setup s.imageAction
    (s.image (actor (F := F) (g := g) (I := I))) (finrank (ZMod 2) I - 2) := by
  let A := actor (F := F) (g := g) (I := I)
  let P := componentOrbit L ⊤ ⊔ A
  let : IsElementaryAbelian 2 A := actor_elementary (F := F) (g := g) (I := I)
  let : IsElementaryAbelian 2 (A.subgroupOf P) :=
    IsElementaryAbelian.subgroupOf (show A ≤ P from le_sup_right)
  refine { faithful := kerRepresentation_faithful s.action
           elementary := IsElementaryAbelian.map s.projection
           card_actor := (Nat.card_congr s.actorEquiv.toEquiv).symm.trans s.actor_card
           degree_le := ?_ }
  have hd := s.dimension_gt_two
  omega

/-- The remaining geometric input for the literal application of G.9.3.
This is a target proposition, not an assumed classifier or a proved inhabitant. -/
def ComponentInput : Prop :=
  ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple s.imageAction
    (s.image (actor (F := F) (g := g) (I := I)))
    (s.image L) (s.image (componentOrbit L ⊤)) (finrank (ZMod 2) I - 2)

/-- The actual preimage of HY in the original SQTK cover still covers the
constituent action quotient. No SQTK property of arbitrary quotients is assumed. -/
def imageCover : ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple s.actionQuotient :=
  ((Recognition.terminal_sqtkCover s.simple F (by decide)).subgroup
    (componentOrbit L ⊤ ⊔ actor (F := F) (g := g) (I := I))).map s.projection
      (QuotientGroup.mk'_surjective _)

/-- The orbit image is normal in the actual constituent quotient. -/
theorem image_normal : (s.image (componentOrbit L ⊤)).Normal := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  exact Subgroup.Normal.map inferInstance s.projection (QuotientGroup.mk'_surjective _)

/-- The faithful orbit survives unchanged in Aut_HY(I). -/
def orbitEquiv : componentOrbit L ⊤ ≃* s.image (componentOrbit L ⊤) :=
  ExchangedAction.orbitEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.orbit_faithful

/-- The original irreducible H-action remains irreducible on its literal image. -/
theorem image_irreducible : IsIrreducible
    (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) := by
  apply (irreducible_comp_surjective_iff s.orbitEquiv.toMonoidHom
    s.orbitEquiv.surjective _).mp
  exact s.irreducible

/-- Retain non-self-duality on the fixed image of H. -/
theorem image_not_selfDual : ¬ Nonempty (Representation.Equiv
    (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
    (Representation.dual (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype))) :=
  ExchangedAction.image_not_selfDual F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.faithful_data.2.1

/-- Retain the actual properness premise on the literal image action. -/
theorem image_not_surjective : ¬ Function.Surjective
    (Representation.asGroupHom (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)) :=
  ExchangedAction.image_not_surjective F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.proper

/-- A7 recognition on Aut_HY(I) feeds the actual terminal catalogue consumer. -/
theorem componentImageCases_of_image_alternating_seven
    (e : s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 7)) : ComponentImageCases L :=
  ExchangedAction.componentImageCases_of_image_alternating_seven
    F.terminalRepresentation (componentOrbit L ⊤) (F.terminalDot (F.X g)) I
    s.selected.invariant s.component rfl s.orbit_faithful e

/-- The recognized literal image also supplies the parent's local component lift. -/
theorem local_lift_of_image_alternating_seven
    (e : s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 7)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  source_component_catalogue_of_small_actor_image s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis s.small_actor s.component s.moved
    (s.componentImageCases_of_image_alternating_seven e)

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
