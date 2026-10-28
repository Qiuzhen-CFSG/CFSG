module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.Sections

/-!
# The natural SL₂(4) quotient with its full original action

Field coordinates identify the actual natural quotient with the consumer's
SL₂(4) model. The full normalizer section constructs the representation on
U, the surjective natural projection, its fixed kernel, and compatible LT
actions on both spaces. The component map is the literal original map from
L, and hence retains L/O∞(L) and U/C_U(L).

Source: Aschbacher--Smith 13.1.10(1), pp.871--872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
open Representation.SL2FourNatural
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal component map, with codomain restricted to its actual image. -/
@[expose] def reducedComponentMap (L : Subgroup G) : L →* NormalizerReducedAction.componentImage L :=
  (NormalizerReducedAction.componentMap L).codRestrict _ (fun l =>
    NormalizerReducedAction.componentMap_range L ▸ ⟨l,rfl⟩)

omit [Finite G] in
theorem reducedComponentMap_surjective (L : Subgroup G) :
    Function.Surjective (reducedComponentMap L) := by
  intro a
  have ha : (a : NormalizerReducedAction.Star L) ∈
      (NormalizerReducedAction.componentMap L).range :=
    (NormalizerReducedAction.componentMap_range L).symm ▸ a.property
  obtain ⟨l,hl⟩ := ha
  exact ⟨l,Subtype.ext hl⟩

/-- Change field coordinates to the exact natural model used by the consumer. -/
def fourNaturalEquiv (F' : BinaryField) (hF : F'.degree = 2) :
    ActionEquiv (linearNatural F' 2) AlternatingFive.Natural := by
  let := Fintype.ofFinite F'.Carrier
  let ef : F'.Carrier ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F'.card_eq, hF, card_field]; decide)
  let el : F'.Carrier ≃ₗ[ZMod 2] F :=
    { ef.toAddEquiv with map_smul' := ZMod.map_smul ef }
  refine ⟨Atlas.fieldEquivSL 2 ef, LinearEquiv.piCongrRight (fun _ : Fin 2 => el), ?_⟩
  intro g v
  funext i
  change ef (∑ j, g.val i j * v j) = ∑ j, ef (g.val i j) * ef (v j)
  simp only [map_sum, map_mul]

private theorem normal_representation_compatible {D E W : Type*}
    [Group D] [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {K : Subgroup D} [K.Normal]
    (e : K ≃* E) (x : D) (g : E) (w : W) :
    ρ x (ρ (e.symm g : D) w) =
      ρ (e.symm ((MulAut.congr e (MulAut.conjNormal x)) g) : D) (ρ x w) := by
  change ρ x (ρ (e.symm g : D) w) =
    ρ (e.symm (e (MulAut.conjNormal x (e.symm g))) : D) (ρ x w)
  rw [e.symm_apply_apply, ← Module.End.mul_apply, ← map_mul,
    ← Module.End.mul_apply, ← map_mul]
  apply congrArg (fun k => ρ k w)
  change x * (e.symm g : D) = (x * (e.symm g : D) * x⁻¹) * x
  simp only [inv_mul_cancel_right]

/-- Construct all full-normalizer and central-quotient maps in the natural
SL₂(4) row from the actual moved-section action. -/
def fullSectionFourMarking
    {T : Sylow 2 G} {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (c : CommonMarking T L)
    (a : ActionEquiv
      ((fullMovedSection L).action.comp (NormalizerReducedAction.componentImage L).subtype)
      AlternatingFive.Natural) :
    AlternatingFive.Marking T L (fullMovedSection L).space.toSubmodule := by
  let C := NormalizerReducedAction.componentImage L
  let : C.Normal := reducedComponent_normal L
  let s := fullMovedSection L
  let f := (NormalizerReducedAction.quotient L).comp (inclusion c.ambient_invariant)
  let σ : Representation (ZMod 2) SL s.space.toSubmodule := s.space.toRepresentation.comp (C.subtype.comp a.groupEquiv.symm.toMonoidHom)
  let μ : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) s.space.toSubmodule := s.space.toRepresentation.comp f
  let π : σ.IntertwiningMap AlternatingFive.Natural :=
    (a.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ).intertwiningMap_of_isIntertwiningMap
      _ _ (by
        intro g v
        have hh := a.intertwines (a.groupEquiv.symm g) (s.central.toSubmodule.mkQ v)
        change a.linearEquiv ((MovedSection.action (reducedRepresentation L) s)
          (a.groupEquiv.symm g : NormalizerReducedAction.Star L) (s.central.toSubmodule.mkQ v)) = _ at hh
        rw [a.groupEquiv.apply_symm_apply] at hh
        exact hh)
  let α : (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut SL :=
    (MulAut.congr a.groupEquiv).toMonoidHom.comp ((MulAut.conjNormal).comp f)
  let ν : Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) V :=
    a.linearEquiv.conjRingEquiv.toMonoidHom.comp
      ((MovedSection.action (reducedRepresentation L) s).comp f)
  let ec : normalizerMoved L ≃* Multiplicative s.space.toSubmodule :=
    (movedCoordinates L).trans
      (LinearEquiv.ofEq _ _ s.space_eq.symm).toAddEquiv.toMultiplicative
  refine {
    invariant := c.invariant
    coordinates := ec
    component := a.groupEquiv.toMonoidHom.comp (reducedComponentMap L)
    onto := a.groupEquiv.surjective.comp (reducedComponentMap_surjective L)
    representation := σ
    actor := μ
    equivariant := ?_
    component_action := ?_
    projection := π
    projection_onto := a.linearEquiv.surjective.comp (Submodule.mkQ_surjective _)
    kernel_fixed := ?_
    conjugation := α
    naturalActor := ν
    compatible := ?_
    quotient_action := ?_ }
  · intro m u
    apply Subtype.ext
    exact movedCoordinates_equivariant L (inclusion c.ambient_invariant m) u
  · intro l w
    change s.space.toRepresentation (f (inclusion le_sup_left l)) w =
      s.space.toRepresentation (a.groupEquiv.symm (a.groupEquiv (reducedComponentMap L l))) w
    rw [a.groupEquiv.symm_apply_apply]
    apply congrArg (fun x => s.space.toRepresentation x w)
    change NormalizerReducedAction.quotient L
      (inclusion c.ambient_invariant (inclusion le_sup_left l)) =
      NormalizerReducedAction.componentMap L l
    rw [NormalizerReducedAction.componentMap_eq]
    rfl
  · intro v hv g
    have hz : s.central.toSubmodule.mkQ v = 0 := a.linearEquiv.injective
      (by exact hv.trans a.linearEquiv.map_zero.symm)
    have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
    rw [s.central_eq] at hm
    exact hm (a.groupEquiv.symm g)
  · intro m g w
    exact normal_representation_compatible s.space.toRepresentation a.groupEquiv (f m) g w
  · intro m v
    change a.linearEquiv (s.central.toSubmodule.mkQ (s.space.toRepresentation (f m) v)) =
      a.linearEquiv ((MovedSection.action (reducedRepresentation L) s) (f m)
        (a.linearEquiv.symm (a.linearEquiv (s.central.toSubmodule.mkQ v))))
    rw [a.linearEquiv.symm_apply_apply]
    rfl

/-- The B.4.2 linear-two branch supplies the complete original natural
quotient marking, including the actual LT-action and component quotient. -/
def irreducibleFourMarking
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (F' : BinaryField) (hF : F'.degree = 2)
    (a : ActionEquiv (s.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype) (linearNatural F' 2)) :
    PSLTwoFourMarking T L (fullMovedSection L).space.toSubmodule := by
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let b := fullSectionComponentEquiv hj s
  let d := fourNaturalEquiv F' hF
  let e := composeAction (ExtensionConsequences.actionSymm b) (composeAction a d)
  let c := CommonMarking.of_source h hmany hL hn hmove
  refine ⟨c, ?_, fullSectionFourMarking c e⟩
  exact ⟨F, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, card_field],
    ⟨(reducedImageEquivMovedImage h hmany hL hn).symm.trans
      (e.groupEquiv.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL)⟩⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
