module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.NaturalDual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointTransport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SectionTransport
public import Theory.GroupTheory.PCoreRestriction

/-!
# The component intersection of a point two-core

Intersecting the intrinsic two-core of a point stabilizer with the component
lands in the intrinsic two-core of the component point stabilizer. This only
uses restriction of a normal two-subgroup; it does not identify the two cores.
Equivariant coordinates then transport both this containment and best offending
to the actual natural-plus-dual representation.

The final lemma isolates the two independent numerical inputs: the rank-four
conclusion of B.4.9(2iii) and the rank-at-most-three point-core calculation.
Neither input, nor the existence of coordinates, is asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49, printed p.1145, and B.4.9(2iii), printed p.92.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight

open Subgroup Representation.BinaryOffender
open Chapter2.ComponentRefinement.LieType.Binary

variable {K D V W : Type*} [Group K] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Restriction accounts for the intersection with the component. No normality
of the component is needed for this containment. -/
theorem core_subgroupOf_le (P L : Subgroup K) :
    (localTwoCore P).subgroupOf L ≤ localTwoCore (P.subgroupOf L) := by
  let R := P ⊓ L
  have h := inf_pCoreIn_le_of_le 2 (show R ≤ P from inf_le_left)
  let e : R ≃* P.subgroupOf L :=
    { toFun := fun x => ⟨⟨x, x.property.2⟩, x.property.1⟩
      invFun := fun x => ⟨x, x.property, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  intro x hx
  have hxP := localTwoCore_le P hx
  obtain ⟨y, hy, he⟩ := h ⟨⟨hxP, x.property⟩, hx⟩
  refine ⟨e y, ?_, ?_⟩
  · rw [← pCore_map_iso 2 e]
    exact ⟨y, hy, rfl⟩
  · exact Subtype.ext he

/-- A point in an invariant submodule has exactly the expected component
stabilizer. The full ambient actor is retained on the left. -/
theorem pointStabilizer_subgroupOf (ρ : Representation (ZMod 2) K V)
    (L : Subgroup K) (z : V) :
    (pointStabilizer ρ z).subgroupOf L =
      pointStabilizer (ρ.comp L.subtype) z := rfl

/-- The component part of an offender in the ambient point two-core lands
in the concrete model point two-core. -/
theorem map_component_core_le
    (ρ : Representation (ZMod 2) K V) (σ : Representation (ZMod 2) D W)
    (U₀ : Subrepresentation ρ) (L : Subgroup K) (e : L ≃* D)
    (E : U₀.toSubmodule ≃ₗ[ZMod 2] W)
    (hE : ∀ (l : L) v, E (U₀.toRepresentation l v) = σ (e l) (E v))
    (z : U₀.toSubmodule) (P A : Subgroup K)
    (hP : P = pointStabilizer U₀.toRepresentation z)
    (hA : A ≤ localTwoCore P) :
    (A.subgroupOf L).map e.toMonoidHom ≤ localTwoCore (pointStabilizer σ (E z)) := by
  have h := map_mono (f := e.toMonoidHom)
    ((subgroupOf_mono L hA).trans (core_subgroupOf_le P L))
  rw [localTwoCore_map_equiv, hP, pointStabilizer_subgroupOf,
    pointStabilizer_map_equivariant (U₀.toRepresentation.comp L.subtype) σ e E hE] at h
  exact h

/-- The explicit numerical B.4.9(2iii) input used in the middle-node case.
This concerns the actual natural matrix action and its contragredient. -/
def NaturalDualBestRank : Prop :=
  ∀ A : Subgroup (PSL 4), IsBestOffender (BinaryGeometry.naturalDual 4) A → rank A = 4

/-- The independent geometric calculation still required of the concrete model. -/
def NaturalDualPointCoreBound : Prop :=
  ∀ (z : Vector 4 × Module.Dual (ZMod 2) (Vector 4))
    (A : Subgroup (PSL 4)),
    A ≤ localTwoCore (pointStabilizer (BinaryGeometry.naturalDual 4) z) →
      IsElementaryTwo A → rank A ≤ 3

/-- Assemble the concrete rank contradiction once coordinate selection and
the point-core calculation have been proved. -/
theorem exclude_of_coordinates [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (L P A : Subgroup K)
    (e : L ≃* PSL 4) (U₀ : Subrepresentation ρ)
    (c : NaturalDualCoordinates ρ L e U₀) (z : U₀.toSubmodule)
    (hP : P = pointStabilizer U₀.toRepresentation z)
    (hAL : A ≤ L) (hAP : A ≤ localTwoCore P)
    (hA : IsBestOffender ρ A)
    (hB49 : NaturalDualBestRank) (hgeometry : NaturalDualPointCoreBound) : False := by
  have hb := best_subrepresentation_model ρ (BinaryGeometry.naturalDual 4)
    U₀ L e c.coordinates c.equivariant hAL hA
  have hc := map_component_core_le ρ (BinaryGeometry.naturalDual 4)
    U₀ L e c.coordinates c.equivariant z P A hP hAP
  have hr := hgeometry (c.coordinates z) _ hc hb.1
  rw [hB49 _ hb] at hr
  omega

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight
