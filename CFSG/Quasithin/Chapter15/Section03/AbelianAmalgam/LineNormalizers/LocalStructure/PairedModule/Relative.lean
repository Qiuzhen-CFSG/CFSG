module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.Section
public import Theory.ElementaryAbelian.Quotient

/-!
# Comparing the binary section with the relative group quotient

The original `U = V_E` maps to `G_E/E` using its actual inclusion in
`G_E = N_G(E)`. Its kernel is exactly `E ∩ U`, and its range is the image
of the relative subgroup of `G_E`. The binary first isomorphism theorem
identifies `SectionSpace V E` with this range, preserving projection and
conjugation. No ambient normality of `E` in `G` is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170, notation `Ǧ_E = G_E/E`.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
variable {G : Type*} [Group G]
variable (V E : Subgroup G) [IsElementaryAbelian 2 (lineV V E)]
variable [IsMulCommutative V] (hEV : E ≤ V)

/-- The actual map from `U` into the relative quotient `G_E/E`. -/
noncomputable def ambientProjection :
    lineV V E →* (lineNormalizer E ⧸ E.subgroupOf (lineNormalizer E)) :=
  (QuotientGroup.mk' (E.subgroupOf (lineNormalizer E))).comp
    (inclusion (lineV_le_lineNormalizer V E hEV))

omit [IsElementaryAbelian 2 (lineV V E)] in
/-- The group projection kills exactly the line inside `U`. -/
theorem ambientProjection_ker :
    (ambientProjection V E hEV).ker = E.subgroupOf (lineV V E) := by
  ext u
  change QuotientGroup.mk' (E.subgroupOf (lineNormalizer E)) _ = 1 ↔ _
  exact QuotientGroup.eq_one_iff _

omit [IsElementaryAbelian 2 (lineV V E)] in
/-- Its image is the image of the actual relative subgroup of `G_E`. -/
theorem ambientProjection_range :
    (ambientProjection V E hEV).range =
      ((lineV V E).subgroupOf (lineNormalizer E)).map
        (QuotientGroup.mk' (E.subgroupOf (lineNormalizer E))) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨⟨u, lineV_le_lineNormalizer V E hEV u.property⟩, u.property, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩

/-- The relative image inherits its elementary abelian structure from `U`. -/
noncomputable instance ambientProjection_range_elementary :
    IsElementaryAbelian 2 (ambientProjection V E hEV).range :=
  IsElementaryAbelian.of_surjective _ (ambientProjection V E hEV).rangeRestrict_surjective

/-- The binary form of the actual relative quotient projection. -/
noncomputable def ambientLinearProjection :
    Additive (lineV V E) →ₗ[ZMod 2] Additive (ambientProjection V E hEV).range :=
  (ambientProjection V E hEV).rangeRestrict.toAdditive.toZModLinearMap 2

/-- The binary projection covers the whole actual image. -/
theorem ambientLinearProjection_surjective :
    Function.Surjective (ambientLinearProjection V E hEV) :=
  (ambientProjection V E hEV).rangeRestrict_surjective

/-- Its binary kernel agrees with the published line subspace. -/
theorem ambientLinearProjection_ker :
    (ambientLinearProjection V E hEV).ker = lineSubspace V E := by
  ext v
  change (ambientProjection V E hEV).rangeRestrict v.toMul = 1 ↔
    v.toMul ∈ E.subgroupOf (lineV V E)
  rw [← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict, ambientProjection_ker]

/-- The binary section is the actual image of `U` in `G_E/E`. -/
noncomputable def sectionEquivAmbient :
    SectionSpace V E ≃ₗ[ZMod 2] Additive (ambientProjection V E hEV).range :=
  (Submodule.quotEquivOfEq _ _ (ambientLinearProjection_ker V E hEV).symm).trans
    ((ambientLinearProjection V E hEV).quotKerEquivOfSurjective
      (ambientLinearProjection_surjective V E hEV))

/-- The comparison retains the original quotient representatives. -/
theorem sectionEquivAmbient_projection (v : Additive (lineV V E)) :
    sectionEquivAmbient V E hEV (sectionProjection V E v) =
      ambientLinearProjection V E hEV v := rfl

/-- The comparison also retains conjugation in the relative quotient. -/
theorem ambientProjection_conjugation (g : lineNormalizer E) (v : Additive (lineV V E)) :
    ambientProjection V E hEV (spanRepresentation V E g v).toMul =
      QuotientGroup.mk' (E.subgroupOf (lineNormalizer E)) g *
        ambientProjection V E hEV v.toMul *
          (QuotientGroup.mk' (E.subgroupOf (lineNormalizer E)) g)⁻¹ := by
  change QuotientGroup.mk' (E.subgroupOf (lineNormalizer E)) _ =
    QuotientGroup.mk' (E.subgroupOf (lineNormalizer E)) g *
      QuotientGroup.mk' (E.subgroupOf (lineNormalizer E)) _ *
        (QuotientGroup.mk' (E.subgroupOf (lineNormalizer E)) g)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule
