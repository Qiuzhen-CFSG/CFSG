module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification.QuasisimpleRows

/-!
# The literal moved section and its central quotient

The offender section and full normalizer section have the same moved space
and central quotient. Their component intertwiners preserve those quotient
maps. When the central subspace vanishes, these maps construct the one-copy
SL₃(2) marking on the original U, including its source component quotient.

Source: Aschbacher--Smith 13.1.10(3), pp.871--872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Compose actor and vector coordinates through the same intermediate action. -/
def composeAction {D E H V W X : Type*} [Group D] [Group E] [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    {τ : Representation (ZMod 2) H X} (a : ActionEquiv ρ σ) (b : ActionEquiv σ τ) :
    ActionEquiv ρ τ :=
  ⟨a.groupEquiv.trans b.groupEquiv, a.linearEquiv.trans b.linearEquiv,
    fun g v => (congrArg b.linearEquiv (a.intertwines g v)).trans (b.intertwines _ _)⟩

/-- When the literal central subspace is zero, its quotient map is an
isomorphism on the moved section, with the same component action. -/
@[expose] def sectionQuotientEquiv {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : MovedSection ρ K) (hz : s.central.toSubmodule = ⊥) :
    ActionEquiv (s.space.toRepresentation.comp K.subtype) (s.action.comp K.subtype) where
  groupEquiv := MulEquiv.refl _
  linearEquiv := (s.central.toSubmodule.quotEquivOfEqBot hz).symm
  intertwines _ _ := rfl

/-- The zero-kernel quotient coordinates intertwine the whole original actor,
not just its distinguished component. -/
theorem sectionQuotientEquiv_intertwines {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {K : Subgroup D}
    (s : MovedSection ρ K) (hz : s.central.toSubmodule = ⊥)
    (g : D) (v : s.space.toSubmodule) :
    (sectionQuotientEquiv s hz).linearEquiv (s.space.toRepresentation g v) =
      s.central.quotientRepresentation g ((sectionQuotientEquiv s hz).linearEquiv v) := by
  rfl

/-- The one-copy marking is on the original U, obtained through its actual
central quotient and the section coordinates, with no abstract-carrier shortcut. -/
def singleThreeMarking
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (hz : s.central.toSubmodule = ⊥)
    (a : ActionEquiv (s.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype)
      (linearNatural BinaryField.two 3)) : LinearThreeMarking T L := by
  have hj := componentImage_le_reducedOffender h hL hn hmove
  let c := componentSectionEquiv h hmany hL hn hj s
  let q := sectionQuotientEquiv s hz
  let e := composeAction c (composeAction q a)
  let r : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 1 → Fin 3 → ZMod 2) := {
    toFun := fun v _ => v
    invFun := fun v => v 0
    left_inv := fun _ => rfl
    right_inv := fun v => funext fun _ => congrArg v (Subsingleton.elim _ _)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  refine ⟨CommonMarking.of_source h hmany hL hn hmove, ?_, 1, by decide, by decide, ?_⟩
  · exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨e.groupEquiv.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 3)).symm⟩⟩
  · refine ⟨⟨e.groupEquiv, e.linearEquiv.trans r, ?_⟩⟩
    intro g v
    change r (e.linearEquiv (componentRepresentation g v)) = _
    rw [e.intertwines]
    rfl

/-- The retained irreducible case yields a complete single-natural marking,
or retains its nonzero central extension for the rank-four argument. -/
theorem singleThree_marked_or_central
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hmove : L = ⁅L, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (s : MovedSection
      ((reducedRepresentation L).comp (offenderSubgroup (reducedRepresentation L)).subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))))
    (a : IsLinearNatural (s.action.comp
      ((NormalizerReducedAction.componentImage L).subgroupOf
        (offenderSubgroup (reducedRepresentation L))).subtype) BinaryField.two 3) :
    Nonempty (FourWayMarking.{u,u} T L) ∨ s.central.toSubmodule ≠ ⊥ := by
  by_cases hz : s.central.toSubmodule = ⊥
  · obtain ⟨a⟩ := a
    exact Or.inl ⟨.linearThree (singleThreeMarking h hmany hL hn hmove s hz a)⟩
  · exact Or.inr hz

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterB.SourceInduction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The moved section carries the action of the entire original normalizer. -/
def fullMovedSection (L : Subgroup G) :
    MovedSection (reducedRepresentation L) (NormalizerReducedAction.componentImage L) := by
  let : (NormalizerReducedAction.componentImage L).Normal := reducedComponent_normal L
  exact MovedSection.ofNormal _ _

/-- Passing from the offender actor to the original normalizer preserves the
component action on the actual central quotient. -/
def fullSectionComponentEquiv {L : Subgroup G}
    {H : Subgroup (NormalizerReducedAction.Star L)}
    (hCH : NormalizerReducedAction.componentImage L ≤ H)
    (s : MovedSection ((reducedRepresentation L).comp H.subtype)
      ((NormalizerReducedAction.componentImage L).subgroupOf H)) :
    ActionEquiv
      (s.action.comp ((NormalizerReducedAction.componentImage L).subgroupOf H).subtype)
      ((fullMovedSection L).action.comp (NormalizerReducedAction.componentImage L).subtype) := by
  apply MovedSection.componentEmbeddingEquiv (fullMovedSection L) s
    (subgroupOfEquivOfLe hCH) (LinearMap.id) Function.injective_id
  · intro g v
    rfl
  · rw [Submodule.map_id, moved_comp_map, map_subgroupOf_eq_of_le hCH]

def fullSectionCoordinates {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)] :
    Additive (normalizerMoved L) ≃ₗ[ZMod 2] (fullMovedSection L).space.toSubmodule := by
  let c := (movedCoordinates L).toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let lc : Additive (normalizerMoved L) ≃ₗ[ZMod 2]
      moved (reducedRepresentation L) (NormalizerReducedAction.componentImage L) :=
    c.toLinearEquiv (fun a v => ZMod.map_smul c a v)
  exact lc.trans (LinearEquiv.ofEq _ _ (fullMovedSection L).space_eq.symm)

omit [Finite G] in
theorem fullSectionCoordinates_equivariant
    {L : Subgroup G} [IsElementaryAbelian 2 (normalizerMoved L)]
    (m : NormalizerReducedAction.Ambient L) (u : normalizerMoved L) :
    fullSectionCoordinates (Additive.ofMul (action L m u)) =
      (fullMovedSection L).space.toRepresentation (NormalizerReducedAction.quotient L m)
        (fullSectionCoordinates (Additive.ofMul u)) := by
  apply Subtype.ext
  exact movedCoordinates_equivariant L m u

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Classification
