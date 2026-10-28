module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals

/-!
# The exact two-parabolic geometry above a PSL3 Borel

The scalar quotient carries the two maximal matrix parabolics to distinct
maximal projective parabolics. They intersect in the Borel and generate
the full group; every proper Borel overgroup lies in one of them.
This is the model geometry used in source 2.5.2(2), printed p.551.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

/-- Coatom descent through a surjection, used for the actual scalar quotient. -/
private theorem coatom_of_comap {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (P : Subgroup B)
    (hp : IsCoatom (P.comap f)) : IsCoatom P := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_, ?_⟩
  · intro he
    exact hp.ne_top (by rw [he, comap_top])
  · intro J hJ hPJ
    apply (comap_le_comap_of_surjective hf).mp
    exact (isCoatom_iff_ge_of_le.mp hp).2 (J.comap f)
      (fun he => hJ ((comap_injective hf) (he.trans (comap_top f).symm))) (comap_mono hPJ)

/-- Both standard projective parabolics are ordinary maximal subgroups. -/
theorem projective_parabolics_isCoatom :
    IsCoatom (pointParabolic F) ∧ IsCoatom (lineParabolic F) := by
  constructor
  · apply coatom_of_comap (projection F) (projection_surjective F)
    rw [pointParabolic_comap]
    exact pointParabolicSL_isCoatom F
  · apply coatom_of_comap (projection F) (projection_surjective F)
    rw [lineParabolic_comap]
    exact lineParabolicSL_isCoatom F

/-- The standard projective parabolics meet in the literal Borel. -/
theorem projective_parabolics_inf : pointParabolic F ⊓ lineParabolic F = borel F := by
  apply comap_injective (projection_surjective F)
  rw [comap_inf, pointParabolic_comap, lineParabolic_comap, borel_comap]
  rfl

/-- The two maximal projective parabolics are distinct. -/
theorem projective_parabolics_ne : pointParabolic F ≠ lineParabolic F := by
  intro he
  have hs := parabolics_sup_eq_top F
  rw [he, sup_idem] at hs
  exact (projective_parabolics_isCoatom F).2.ne_top hs

end Matrix.PSL3.LinearThree
