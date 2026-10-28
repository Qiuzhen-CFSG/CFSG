module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.LocalFamily
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Placement
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The literal offender actor for a residual component

For `B ∈ cComponentsIn (J (DR₁))`, this file fixes the actual quotient and
the actual subgroup on which B.5.1 is to be used.  Put

```
  π : Y/O₂(Y),   P = ((B ⊔ R₁) ≤ Y).map π,
  B⁺ = (B ≤ Y).map π,   BP = B⁺.subgroupOf P,
  σ = residualRepresentation.comp P.subtype,
  Q = offenderSubgroup σ.
```

The map from the original component to `BP` is onto and has kernel exactly
`O₂(B)`.  Its action is the same literal conjugation action as the marked
component representation.  The remaining source facts (relative normality in
`N_G(K)`, the commutator equality, and the offender containment) are kept as
fields of `OffenderSourceInput`: they are source deductions, rather than
consequences of the weaker normality in `B ⊔ T`.  The final constructor then
assembles the genuine `QuasisimpleSourceHypothesis` and applies only the
projective-line B.5.1 contract.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed p.1070 (PDF p.1087), and B.5.1, printed pp.99–103.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory ChapterA.Section04
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ResidualNormalizer
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

/-! The four literal subgroups used by the source application. -/

def residualOffenderQuotient : (Y L F) →* (Y L F ⧸ pCore 2 (Y L F)) :=
  QuotientGroup.mk' (pCore 2 (Y L F))

def residualOffenderActor (B : Subgroup G) :
    Subgroup (Y L F ⧸ pCore 2 (Y L F)) :=
  ((B ⊔ F.Ri L 1).subgroupOf (Y L F)).map (residualOffenderQuotient (L := L) (F := F))

def residualOffenderComponentPlus (B : Subgroup G) :
    Subgroup (Y L F ⧸ pCore 2 (Y L F)) :=
  (B.subgroupOf (Y L F)).map (residualOffenderQuotient (L := L) (F := F))

def residualOffenderComponent (B : Subgroup G) :
    Subgroup (residualOffenderActor (L := L) (F := F) B) :=
  (residualOffenderComponentPlus (L := L) (F := F) B).subgroupOf
    (residualOffenderActor (L := L) (F := F) B)

def residualOffenderAction
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) (B : Subgroup G) :
    letI := (d.residualSpan_reduced hSylow).elementary
    Representation (ZMod 2) (residualOffenderActor (L := L) (F := F) B)
      (Additive ((E F).subgroupOf (Y L F))) := by
  letI := (d.residualSpan_reduced hSylow).elementary
  exact (d.residualRepresentation hSylow).comp
    (residualOffenderActor (L := L) (F := F) B).subtype

def residualOffenderSubgroup
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) (B : Subgroup G) :
    letI := (d.residualSpan_reduced hSylow).elementary
    Subgroup (residualOffenderActor (L := L) (F := F) B) := by
  letI := (d.residualSpan_reduced hSylow).elementary
  exact offenderSubgroup (d.residualOffenderAction hSylow B)

omit [Finite G] in
theorem residualOffenderComponentPlus_le_actor {B : Subgroup G}
    :
    residualOffenderComponentPlus (L := L) (F := F) B ≤
      residualOffenderActor (L := L) (F := F) B := by
  apply map_mono
  exact subgroupOf_mono (Y L F) (le_sup_left : B ≤ B ⊔ F.Ri L 1)

omit [Finite G] in
theorem residualOffenderComponent_map_subtype {B : Subgroup G}
    :
    (residualOffenderComponent (L := L) (F := F) B).map
        (residualOffenderActor (L := L) (F := F) B).subtype =
      residualOffenderComponentPlus (L := L) (F := F) B := by
  exact map_subgroupOf_eq_of_le (residualOffenderComponentPlus_le_actor (L := L) (F := F))

/-- The original component maps onto the distinguished subgroup `BP`. -/
def residualComponentToOffender
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    B →* residualOffenderComponent (L := L) (F := F) B := by
  let hBY : B ≤ Y L F := hB.1.trans J_le_Y
  let hBP := residualOffenderComponentPlus_le_actor (L := L) (F := F) (B := B)
  let f : B →* (Y L F ⧸ pCore 2 (Y L F)) :=
    (residualOffenderQuotient (L := L) (F := F)).comp (inclusion hBY)
  let fc : B →* residualOffenderComponentPlus (L := L) (F := F) B :=
    f.codRestrict _ (by
      intro b
      exact ⟨⟨b, hBY b.property⟩, b.property, rfl⟩)
  exact (subgroupOfEquivOfLe hBP).symm.toMonoidHom.comp fc

omit [Finite G] in
theorem residualComponentToOffender_surjective
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    Function.Surjective (residualComponentToOffender hB) := by
  intro x
  let hBY : B ≤ Y L F := hB.1.trans J_le_Y
  let hBP := residualOffenderComponentPlus_le_actor (L := L) (F := F) (B := B)
  let f : B →* (Y L F ⧸ pCore 2 (Y L F)) :=
    (residualOffenderQuotient (L := L) (F := F)).comp (inclusion hBY)
  let fc : B →* residualOffenderComponentPlus (L := L) (F := F) B :=
    f.codRestrict _ (by
      intro b
      exact ⟨⟨b, hBY b.property⟩, b.property, rfl⟩)
  obtain ⟨b, hb, he⟩ := x.property
  refine ⟨⟨b, hb⟩, ?_⟩
  apply (subgroupOfEquivOfLe hBP).injective
  change (fc ⟨b, hb⟩ : residualOffenderComponentPlus (L := L) (F := F) B) =
    subgroupOfEquivOfLe hBP x
  apply Subtype.ext
  change residualOffenderQuotient (L := L) (F := F) b =
    ((subgroupOfEquivOfLe hBP) x : (Y L F ⧸ pCore 2 (Y L F)))
  exact he

theorem residualComponentToOffender_ker
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    (residualComponentToOffender hB).ker = pCore 2 B := by
  let hBY : B ≤ Y L F := hB.1.trans J_le_Y
  let hBP := residualOffenderComponentPlus_le_actor (L := L) (F := F) (B := B)
  let f : B →* (Y L F ⧸ pCore 2 (Y L F)) :=
    (residualOffenderQuotient (L := L) (F := F)).comp (inclusion hBY)
  let fc : B →* residualOffenderComponentPlus (L := L) (F := F) B :=
    f.codRestrict _ (by
      intro b
      exact ⟨⟨b, hBY b.property⟩, b.property, rfl⟩)
  change ((subgroupOfEquivOfLe hBP).symm.toMonoidHom.comp fc).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ (subgroupOfEquivOfLe hBP).symm.injective]
  exact (MonoidHom.ker_codRestrict f _ _).trans
    (residual_component_projection_ker hB)

/-- The quotient actor map intertwines the original marked action with the
restricted action on `P`. -/
theorem residualComponentToOffender_equivariant
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (b : B) (v : Additive ((E F).subgroupOf (Y L F))) :
    letI := (d.residualSpan_reduced hSylow).elementary
    d.residualComponentRepresentation hSylow (hB.1.trans J_le_Y) b v =
      d.residualOffenderAction hSylow B
        ((residualOffenderComponent (L := L) (F := F) B).subtype
          (residualComponentToOffender hB b)) v := by
  let _ := (d.residualSpan_reduced hSylow).elementary
  rfl

/-! The source facts that are needed to make the B.5.1 application.  They are
kept explicit because normality in `B ⊔ T` does not imply normality in
`N_G(K)`, and because FF for the full `Y/O₂(Y)` action does not by itself
restrict to the actor `P`. -/

structure OffenderSourceInput (κ : GroupClass.{u})
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) where
  relative_normal :
    (B.subgroupOf (normalizer (K F : Set G))).Normal
  commutator_eq :
    ⁅B, Stellmacher.elementaryAbelianMaxJ (F.Ri L 1)⁆ = B
  component_le_offender :
    residualOffenderComponent (L := L) (F := F) B ≤ d.residualOffenderSubgroup hSylow B
  quasisimple : IsQuasisimple
    ((residualOffenderComponent (L := L) (F := F) B).subgroupOf
      (d.residualOffenderSubgroup hSylow B))
  sqtk : IsSQTK κ
    ((residualOffenderComponent (L := L) (F := F) B).subgroupOf
      (d.residualOffenderSubgroup hSylow B))
  fitting :
    generalizedFitting (d.residualOffenderSubgroup hSylow B) =
      (residualOffenderComponent (L := L) (F := F) B).subgroupOf
        (d.residualOffenderSubgroup hSylow B) ⊔
        center (d.residualOffenderSubgroup hSylow B)
  twoCore :
    pCore 2 (d.residualOffenderSubgroup hSylow B) = ⊥
  generated :
    letI := (d.residualSpan_reduced hSylow).elementary
    offenderSubgroup
      ((d.residualOffenderAction hSylow B).comp
        (d.residualOffenderSubgroup hSylow B).subtype) = ⊤

/-- The exact B.5.1 hypothesis on the actual offender-generated actor. -/
theorem offenderSourceHypothesis
    {κ : GroupClass.{u}}
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (h : OffenderSourceInput d κ hSylow hB) :
    letI := (d.residualSpan_reduced hSylow).elementary
    ChapterB.QuasisimpleSource.QuasisimpleSourceHypothesis
      ((d.residualOffenderAction hSylow B).comp
        (d.residualOffenderSubgroup hSylow B).subtype) κ
      ((residualOffenderComponent (L := L) (F := F) B).subgroupOf
        (d.residualOffenderSubgroup hSylow B)) := by
  let _ := (d.residualSpan_reduced hSylow).elementary
  let ρ := d.residualOffenderAction hSylow B
  let Q := d.residualOffenderSubgroup hSylow B
  let BP := (residualOffenderComponent (L := L) (F := F) B).subgroupOf Q
  have hfaith : Function.Injective (ρ.comp Q.subtype) := by
    apply (d.residualRepresentation_faithful hSylow).comp
    exact (residualOffenderActor (L := L) (F := F) B).subtype_injective.comp
      Q.subtype_injective
  refine ⟨Module.Finite.of_finite, hfaith, h.quasisimple, h.sqtk, h.fitting, h.twoCore,
    h.generated⟩

/-- The complete six-clause source conclusion on the literal action. -/
theorem offenderSourceClassification
    {κ : GroupClass.{u}}
    (earlier : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,u} κ)
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (h : OffenderSourceInput d κ hSylow hB) :
      letI := (d.residualSpan_reduced hSylow).elementary
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((d.residualOffenderAction hSylow B).comp
        (d.residualOffenderSubgroup hSylow B).subtype)
      ((residualOffenderComponent (L := L) (F := F) B).subgroupOf
        (d.residualOffenderSubgroup hSylow B))) :=
  by
    let _ := (d.residualSpan_reduced hSylow).elementary
    exact earlier _ _ _ _ (offenderSourceHypothesis (d := d) hSylow hB h)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
