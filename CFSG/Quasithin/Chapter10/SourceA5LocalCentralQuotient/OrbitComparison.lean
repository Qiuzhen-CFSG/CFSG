module
public import CFSG.Quasithin.Chapter10.SourceA5LocalCentralQuotient
public import Theory.GroupTheory.ReducedNormal.SubspaceCentralImage

/-!
# Original orbit coordinates for the local central quotient

The original Sylow orbit image is the central orbit span of the seed's
quotient image. Its canonical representation equivalence with V/C_V(L₀)
retains every original representative and the action of the literal L₀.
This connects homogeneous model comparisons to the unchanged faithful
local actor and its cubic bound.

Source: Aschbacher–Smith, 3.2.2(3) and the local inputs to D.3.4–5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L : Subgroup G}

/-- The actual Sylow orbit image of the original homogeneous seed. -/
abbrev sourceLocalOrbitImage (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :=
  quotientImage (ReducedNormal.representation (localJoin T L))
    ((localOrbit T L).subgroupOf (localJoin T L))
    (orbitSpan (ReducedNormal.representation (localJoin T L))
      ((T : Subgroup G).subgroupOf (localJoin T L)) D.seedSpace)
    (orbitSpan_component_invariant _ D.homogeneous.normalizes D.homogeneous.isIrrPlus)

/-- The model carrier is the central orbit span of the original seed image. -/
theorem source_local_orbit_image_eq_centralOrbitSpan
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (sourceLocalOrbitImage D).toSubmodule =
      centralOrbitSpan (ReducedNormal.representation (localJoin T L))
        ((localOrbit T L).subgroupOf (localJoin T L))
        ((T : Subgroup G).subgroupOf (localJoin T L)) D.homogeneous.normalizes
        (quotientImage (ReducedNormal.representation (localJoin T L))
          ((localOrbit T L).subgroupOf (localJoin T L)) D.seedSpace
            D.homogeneous.invariant).toSubmodule :=
  orbitSpan_quotientImage _ _ _ _ _

local instance localComparisonElementary
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.moduleSubgroup := D.module_elementary

/-- The ambient orbit image and the local literal quotient are canonically
isomorphic, with the original representative retained. -/
theorem source_local_quotient_orbit_image_equiv
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    let U := D.moduleSubgroup.subgroupOf (localJoin T L)
    let := (source_parabolic_module_reduced D).normal
    let q := QuotientGroup.mk' (centralizer (U : Set (localJoin T L)))
    ∀ τ : Representation (ZMod 2) ((localJoin T L) ⧸ centralizer (U : Set (localJoin T L)))
      (Additive (sourceLocalCentralQuotient D)),
      (∀ (m : localJoin T L) (v : D.moduleSubgroup),
        τ (q m) (Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D) v)) =
          Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D)
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.join_normalizes_module m.property) v).mp
                v.property⟩)) →
      ∃ a : (sourceLocalOrbitImage D).toRepresentation.Equiv
          ((τ.comp q).comp ((localOrbit T L).subgroupOf (localJoin T L)).subtype),
        ∀ w : orbitSpan (ReducedNormal.representation (localJoin T L))
            ((T : Subgroup G).subgroupOf (localJoin T L)) D.seedSpace,
          a ⟨(fixedSpace (ReducedNormal.representation (localJoin T L))
              ((localOrbit T L).subgroupOf (localJoin T L))).mkQ w.val,
                ⟨w.val,w.property,rfl⟩⟩ =
            Additive.ofMul (QuotientGroup.mk' (sourceLocalCentralizer D)
              ⟨w.val.toMul.val.val,by
                rw [D.module_eq_subspaceImage]
                exact mem_map_of_mem _ (mem_map_of_mem _ w.property)⟩) := by
  dsimp only
  let := (source_parabolic_module_reduced D).normal
  intro τ hτ
  let W := orbitSpan (ReducedNormal.representation (localJoin T L))
    ((T : Subgroup G).subgroupOf (localJoin T L)) D.seedSpace
  have hW : (⊤ : Subgroup (localJoin T L)) ≤
      subspaceStabilizer (ReducedNormal.representation (localJoin T L)) W := by
    dsimp only [W]
    rw [←D.local_orbitSpan_eq_sylowSpan]
    exact orbitSpan_invariant _ ⊤ _
  exact ReducedNormal.exists_actual_central_image_equiv (localJoin T L) W hW (localOrbit T L) le_sup_left
    D.moduleSubgroup D.module_eq_subspaceImage.symm D.join_normalizes_module
    (τ.comp (QuotientGroup.mk' _)) hτ

end CFSG.Quasithin.Chapter10
