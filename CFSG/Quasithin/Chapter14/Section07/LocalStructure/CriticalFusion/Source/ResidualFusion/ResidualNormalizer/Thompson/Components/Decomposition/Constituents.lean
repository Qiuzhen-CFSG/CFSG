module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.LocalFamily
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import Theory.Representation.BinaryOffender.Homogeneous.Basic

/-!
# The constituent application in 14.7.67(4)

This file records the complete interface needed for the third clause of
14.3.4.  The module used by that clause is the literal `R₂(BT)`, with
`BT = B ⊔ T`; the original reduced module `E` is kept as a separate ambient
submodule and is never silently identified with all of `R₂(BT)`.

`EarlierConstituentClassification` is the universal earlier-source contract.
It quantifies over the actual homogeneous `IsIrrPlusWith` family in
`R₂(BT)`, retains the hypotheses used in the Thompson branch, and returns a
`TransferredConstituent`.  The latter contains the source-space transfer to
the original `E`-action, the FSU fields, the vanishing fixed space, and a
marked action.  The marked action uses `alternatingNatural 5` in the A₅ case
and `linearNatural BinaryField.two 3` (repeated at most twice) in the L₃(2)
case.  Thus the source theorem is not replaced by a quotient-name assertion,
and no claim that all of `E` lies in `R₂(BT)` is made.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
14.3.4(3), printed p.990, and its application in 14.7.67(4), printed
p.1070 (PDF p.1087).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section02 Chapter12.Section08 Theory.GroupTheory
open ResidualNormalizer ResidualNormalizer.Components

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace ResidualNormalizer.Components

/-- The literal local group to which 14.3.4(3) is applied. -/
abbrev BT (B : Subgroup G) (T : Sylow 2 G) : Subgroup G := B ⊔ (T : Subgroup G)

/-- The component and Sylow subgroups viewed inside `BT`. -/
abbrev componentInBT (B : Subgroup G) (T : Sylow 2 G) : Subgroup (BT B T) :=
  B.subgroupOf (BT B T)

abbrev sylowInBT (B : Subgroup G) (T : Sylow 2 G) : Subgroup (BT B T) :=
  (T : Subgroup G).subgroupOf (BT B T)

omit [Finite G] in
theorem componentInBT_le {B : Subgroup G} (T : Sylow 2 G) : B ≤ BT B T := le_sup_left

omit [Finite G] in
theorem sylowInBT_le {B : Subgroup G} (T : Sylow 2 G) :
    (T : Subgroup G) ≤ BT B T := le_sup_right

omit [Finite G] in
theorem componentInBT_le_join
    {B : Subgroup G} (hB : B ≤ Y L F) : BT B T ≤ Y L F ⊔ (T : Subgroup G) := by
  exact sup_le (hB.trans le_sup_left) le_sup_right

/-- Restrict a representation to an invariant subspace and to a subgroup.
This is the literal action on a selected constituent; it does not replace the
ambient action by an action on an abstract isomorphic copy. -/
def restrictedSubrepresentation
    {D : Type u} [Group D] {U : Type u} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (K : Subgroup D)
    (I : Submodule (ZMod 2) U)
    (hI : K ≤ subspaceStabilizer ρ I) :
    Subrepresentation (ρ.comp K.subtype) where
  toSubmodule := I
  apply_mem_toSubmodule g v hv := (hI g.property v).2 hv

/-- The FSU fields used by the source application, with all actions literal. -/
structure FSUData
    {D : Type u} [Group D] {U : Type u} [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (K T : Subgroup D)
    (S : Subrepresentation (ρ.comp K.subtype)) : Prop where
  tInvariant : T ≤ subspaceStabilizer ρ S.toSubmodule
  ff : Representation.BinaryOffender.IsFFModule (ρ.comp K.subtype)
  fixed_eq_bot : fixedSpace (ρ.comp K.subtype) (⊤ : Subgroup K) = ⊥

/-- A canonical `R₂(BT)` constituent and its source model marking. -/
structure CanonicalConstituent
    (B : Subgroup G) (T : Sylow 2 G)
    (I : Submodule (ZMod 2)
      (Additive (Chapter12.Section02.ReducedModule (BT B T)))) where
  irrPlus : IsIrrPlusWith
      (Chapter12.Section02.reducedRepresentation (BT B T))
      (componentInBT B T) (sylowInBT B T) I
  space : Subrepresentation
      ((Chapter12.Section02.reducedRepresentation (BT B T)).comp
        (componentInBT B T).subtype)
  space_eq : space.toSubmodule = I
  fsu : FSUData (Chapter12.Section02.reducedRepresentation (BT B T))
    (componentInBT B T) (sylowInBT B T) space
  model : SmallMovedAction space.toRepresentation

end ResidualNormalizer.Components

namespace Data
variable (d : Data T L V F W)

/-- A source constituent transferred to the original action on `E`.

The `source` field is a constituent of the literal `R₂(BT)` module.  The
`space` field is a subrepresentation of the original action on `E`; the
linear equivalence and intertwining equation are the transfer data. -/
structure TransferredConstituent
    (d : Data T L V F W)
    [IsElementaryAbelian 2 ((E F).subgroupOf (Y L F))]
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (I : Submodule (ZMod 2)
      (Additive (Chapter12.Section02.ReducedModule (ResidualNormalizer.Components.BT B T))))
    (hI : IsIrrPlusWith
      (Chapter12.Section02.reducedRepresentation (ResidualNormalizer.Components.BT B T))
      (ResidualNormalizer.Components.componentInBT B T)
      (ResidualNormalizer.Components.sylowInBT B T) I) where
  source : CanonicalConstituent B T I
  space : letI := (d.residualSpan_reduced hSylow).elementary
    Subrepresentation (d.residualComponentRepresentation hSylow (hB.1.trans J_le_Y))
  coordinates : letI := (d.residualSpan_reduced hSylow).elementary
    source.space.toSubmodule ≃ₗ[ZMod 2] space.toSubmodule
  intertwines : letI := (d.residualSpan_reduced hSylow).elementary
    ∀ (b : B) (v : source.space.toSubmodule),
      coordinates (source.space.toRepresentation
        ⟨⟨(b : G), (ResidualNormalizer.Components.componentInBT_le (B := B) T) b.property⟩,
          b.property⟩ v) =
        space.toRepresentation b (coordinates v)
  /-- The source constituent really is supported in the original ambient `E`. -/
  ambient_image_le :
    Chapter12.Section02.subspaceImage (ResidualNormalizer.Components.BT B T)
      source.space.toSubmodule ≤ E F
  /-- The original component action has the marked small model. -/
  model : letI := (d.residualSpan_reduced hSylow).elementary
    SmallMovedAction space.toRepresentation

/-- The universal earlier-source clause for 14.3.4(3), specialized only at
the actual source data used by 14.7.67(4).  The clause is universal in the
ambient data and in every member of the canonical homogeneous family. -/
def EarlierConstituentClassification (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (d : Data T L V F W)
      [IsElementaryAbelian 2 ((E F).subgroupOf (Y L F))]
    (_hKstar : K F ∈ Chapter1.LStar G T)
    (_hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (_hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G))
    (_hD : ¬ IsPGroup 2 (D F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (I : Submodule (ZMod 2)
      (Additive (Chapter12.Section02.ReducedModule
        (ResidualNormalizer.Components.BT B T))))
    (hI : IsIrrPlusWith
      (Chapter12.Section02.reducedRepresentation (ResidualNormalizer.Components.BT B T))
      (ResidualNormalizer.Components.componentInBT B T)
      (ResidualNormalizer.Components.sylowInBT B T) I),
      Nonempty (TransferredConstituent d hSylow hB I hI)

/-- Apply the universal 14.3.4(3) clause to one literal homogeneous
constituent.  All five source hypotheses remain explicit. -/
theorem constituent_application
    (d : Data T L V F W)
    (earlier : EarlierConstituentClassification G)
    (hKstar : K F ∈ Chapter1.LStar G T)
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (I : Submodule (ZMod 2)
      (Additive (Chapter12.Section02.ReducedModule
        (ResidualNormalizer.Components.BT B T))))
    (hI : IsIrrPlusWith
      (Chapter12.Section02.reducedRepresentation (ResidualNormalizer.Components.BT B T))
      (ResidualNormalizer.Components.componentInBT B T)
      (ResidualNormalizer.Components.sylowInBT B T) I) :
    letI := (d.residualSpan_reduced hSylow).elementary
    Nonempty (TransferredConstituent d hSylow hB I hI) := by
  let := (d.residualSpan_reduced hSylow).elementary
  exact earlier d hKstar hDM hSylow hBaum hD hB I hI

/-- The application records the faithful local membership and the genuine FF
action supplied by the Thompson preparation alongside the selected
constituent.  This is the interface consumed by the later B.5.1 extraction. -/
structure AppliedConstituent
    (d : Data T L V F W)
    [IsElementaryAbelian 2 ((E F).subgroupOf (Y L F))]
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (I : Submodule (ZMod 2)
      (Additive (Chapter12.Section02.ReducedModule (ResidualNormalizer.Components.BT B T))))
    (hI : IsIrrPlusWith
      (Chapter12.Section02.reducedRepresentation (ResidualNormalizer.Components.BT B T))
      (ResidualNormalizer.Components.componentInBT B T)
      (ResidualNormalizer.Components.sylowInBT B T) I) where
  local_member : B ∈ Chapter1.L G (T : Subgroup G) :=
    d.residual_component_mem_localFamily hSylow hB
  faithful : B ∈ MainForward.faithfulLocalComponents T :=
    d.residual_component_faithful hSylow hB
  ambient_ff :
    letI := (d.residualSpan_reduced hSylow).elementary
    Representation.BinaryOffender.IsFFModule (d.residualRepresentation hSylow)
  constituent : TransferredConstituent d hSylow hB I hI

/-- Package one selected constituent together with all source outputs. -/
theorem apply_constituent
    (d : Data T L V F W)
    (earlier : EarlierConstituentClassification G)
    (hKstar : K F ∈ Chapter1.LStar G T)
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤
      normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (I : Submodule (ZMod 2)
      (Additive (Chapter12.Section02.ReducedModule
        (ResidualNormalizer.Components.BT B T))))
    (hI : IsIrrPlusWith
      (Chapter12.Section02.reducedRepresentation (ResidualNormalizer.Components.BT B T))
      (ResidualNormalizer.Components.componentInBT B T)
      (ResidualNormalizer.Components.sylowInBT B T) I) :
    letI := (d.residualSpan_reduced hSylow).elementary
    Nonempty (AppliedConstituent d hSylow hB I hI) := by
  let := (d.residualSpan_reduced hSylow).elementary
  obtain ⟨c⟩ := constituent_application d earlier hKstar hDM hSylow hBaum hD hB I hI
  have hff := d.residualRepresentation_isFF hDM hSylow hBaum hD
  exact ⟨{
    local_member := d.residual_component_mem_localFamily hSylow hB
    faithful := d.residual_component_faithful hSylow hB
    ambient_ff := hff
    constituent := c }⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
