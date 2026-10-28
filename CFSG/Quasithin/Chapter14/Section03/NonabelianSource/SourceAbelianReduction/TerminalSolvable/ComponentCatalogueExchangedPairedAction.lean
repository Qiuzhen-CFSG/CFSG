module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentKernelImage
public import CFSG.Quasithin.ChapterG.Section09.Basic

/-!
# The original paired constituent quotient satisfies G.9.3

Take the literal action of H joined with N_X(I) on the original I, then
quotient by exactly its action kernel. The source completion makes the actor
faithful and preserves its rank dim(I)-2. Irreducibility and self-duality
descend through the explicit restricted H projection, as does the proved
elementary-Sylow condition.

The original noncentral kernel kills one of the two component factors; the
nontrivial H-image is consequently a single component. A centralizing actor
involution would be trivial on the faithful irreducible binary action, so
positive actor rank supplies the required movement. This constructs the actual
G.9 component hypothesis on the same H-image, with no classification callback.
Paired A5 recognition and its original component lift remain later steps.

Source: Aschbacher--Smith G.10.15 and G.11.6, printed pp.362--366;
14.3.12--15, printed pp.993--994.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedPairedSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedPairedSource T M Mc F g B v L I)

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


/-- The literal quotient map restricted to the original H. -/
def orbitProjection : componentOrbit L ⊤ →* s.image (componentOrbit L ⊤) :=
  (s.projection.subgroupMap ((componentOrbit L ⊤).subgroupOf
    (componentOrbit L ⊤ ⊔ actor (F:=F) (g:=g) (I:=I)))).comp
    (subgroupOfEquivOfLe (show componentOrbit L ⊤ ≤
      componentOrbit L ⊤ ⊔ actor (F:=F) (g:=g) (I:=I) from le_sup_left)).symm.toMonoidHom

theorem orbitProjection_surjective : Function.Surjective s.orbitProjection :=
  (s.projection.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe (show componentOrbit L ⊤ ≤
      componentOrbit L ⊤ ⊔ actor (F:=F) (g:=g) (I:=I) from le_sup_left)).symm.surjective

/-- The original irreducible action descends along the actual H projection. -/
theorem image_irreducible : IsIrreducible
    (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype) := by
  apply (irreducible_comp_surjective_iff s.orbitProjection
    s.orbitProjection_surjective _).mp
  exact s.irreducible

/-- The same H-image is nontrivial by the original fixed-space conclusion. -/
theorem image_ne_bot : s.image (componentOrbit L ⊤) ≠ ⊥ := by
  intro hz
  have hfix : I ≤ fixedSpace F.terminalRepresentation (componentOrbit L ⊤) := by
    intro u hu a
    have he : s.orbitProjection a = 1 := Subtype.ext (mem_bot.mp (hz ▸ (s.orbitProjection a).property))
    have hr : (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation a = 1 := by
      calc
        _ = s.imageAction (s.orbitProjection a).val := rfl
        _ = s.imageAction (1:s.image (componentOrbit L ⊤)).val := congrArg (fun b => s.imageAction b.val) he
        _ = 1 := map_one s.imageAction
    exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩:Additive F.Uhat)) hr
  exact s.selected.isIrrPlus.ne_bot F.terminalRepresentation
    (bot_unique (s.fixedSpace_eq_bot ▸ hfix))

/-- Noncentrality of the original constituent kernel makes its nontrivial
H-image a single genuine component of the actual HY quotient. -/
theorem image_component : IsComponent s.actionQuotient (s.image (componentOrbit L ⊤)) := by
  apply Theory.GroupTheory.ExchangedOrbit.image_orbit_component s.component s.normalizer_index_eq_two
    (componentOrbit L ⊤ ⊔ actor (F:=F) (g:=g) (I:=I)) le_sup_left
    s.projection (QuotientGroup.mk'_surjective _) _ s.image_ne_bot
  intro hc
  apply s.noncentral_kernel
  intro a ha
  apply hc
  apply MonoidHom.mem_ker.mpr
  apply (QuotientGroup.eq_one_iff _).mpr
  exact congrArg Units.val (MonoidHom.mem_ker.mp ha)

/-- Self-duality descends without changing the H-marking. -/
theorem image_selfDual : Nonempty (Representation.Equiv
    (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype)
    (Representation.dual (s.imageAction.comp (s.image (componentOrbit L ⊤)).subtype))) :=
  MarkedAction.selfDual_image F.terminalRepresentation (componentOrbit L ⊤)
    (actor (F:=F) (g:=g) (I:=I)) I s.selected.invariant inf_le_left s.constituent_selfDual

/-- The literal action-quotient H-image retains elementary Sylow subgroups. -/
theorem quotient_image_sylow_elementary (P : Sylow 2 (s.image (componentOrbit L ⊤))) :
    IsElementaryAbelian 2 P :=
  Theory.GroupTheory.ExchangedOrbit.elementary_sylow_image s.orbitProjection
    s.orbitProjection_surjective s.orbit_sylow_elementary P

/-- Genuine G.9.3 on the same original H-image, at the exact stabilizer rank.
Both component slots are this H-image; no catalogue conclusion is an input. -/
theorem image_component_hypothesis :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple s.imageAction
      (s.image (actor (F:=F) (g:=g) (I:=I)))
      (s.image (componentOrbit L ⊤)) (s.image (componentOrbit L ⊤))
      (finrank (ZMod 2) I - 2) := by
  refine { s.image_setup with
    quotient := ⟨s.imageCover⟩
    component := s.image_component
    noncentral := ?_
    normal_H := s.image_normal
    irreducible := s.image_irreducible
    components := Or.inl rfl }
  intro hz
  let A := s.image (actor (F:=F) (g:=g) (I:=I))
  let H := s.image (componentOrbit L ⊤)
  let : IsElementaryAbelian 2 A := s.image_setup.elementary
  let : IsIrreducible (s.imageAction.comp H.subtype) := s.image_irreducible
  have htriv : ∀ a:A, a=1 := by
    intro a
    apply Subtype.ext
    apply Representation.BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
      s.imageAction H s.image_setup.faithful
    · exact elemPow_eq_one_of_isElementaryAbelian (p:=2) _ a.property
    · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz) a.property
  have ha : Nat.card A = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,htriv⟩
  have hpow := s.image_setup.card_actor
  change Nat.card A = _ at hpow
  rw [ha] at hpow
  have hpos := one_lt_pow' (by decide : 1<2)
    (show finrank (ZMod 2) I - 2 ≠ 0 by have := s.dimension_gt_two; omega)
  omega

end ExchangedPairedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
