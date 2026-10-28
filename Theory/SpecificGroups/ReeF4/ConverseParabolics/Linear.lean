module

public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.LeviRetraction
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Linear.FullLeviRepresentation
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical

/-!
# Full linear-side Ree parabolic calculations

The root radical is nonidentity by the proved linear-seed calculation and the
matrix-preserving comparison with the Ree model. The full parabolic normalizes
this radical, and its retraction onto the full fixed Levi has precisely this
radical as kernel. The proved SL₂-times-field-torus isomorphism of that
full Levi supplies a surjective parabolic projection with exactly this
two-group kernel.

Self-centralization in the full parabolic follows from the faithful action
of the full Levi on the radical abelianization, including the complementary
torus action. The actual matrix comparison transports that calculation to
the converse's parabolic and intrinsic radical. All these conclusions hold
for `m ≥ 1` without an ambient simplicity hypothesis.

Sources: Aschbacher–Smith F.1.12(I)(5), printed p.263, and Theorem 0.1.2(1),
printed p.4 (`refs/quasithin.pdf`); GLS3 §§2.6 and 3.2.
-/

public noncomputable section

namespace ReeF4.ConverseParabolics

open Subgroup LargeLocalSeeds
open SectionGeometry.LinearRadical (fullLevi)

/-- Nontriviality transfers along the actual seed-to-model matrix comparison. -/
theorem linear_radical_ne_bot {m : ℕ} (hm : 1 ≤ m) : radical m .linear ≠ ⊥ := by
  let d := canonicalLocalBlockInput m
  intro hR
  have hstd : standardRadical d .linear = ⊥ :=
    (map_eq_bot_iff_of_injective _ d.modelEquiv.injective).mp
      ((standardRadical_map_eq d .linear).trans hR)
  have hseed : seedRadical d .linear = ⊥ := by
    rw [seedRadical, hstd, bot_subgroupOf]
  exact linearCore_ne_bot hm d ((seedRadical_linear_eq_twoCore hm d).symm.trans hseed)

/-- In characteristic two the existing projective seed projection is an
actual SL₂ projection over the same coefficient field. -/
def linearSeedProjectionSL {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    standardSeed d .linear →* Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) :=
  (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm.toMonoidHom.comp
    (LinearProjection.projection hm d)

theorem linearSeedProjectionSL_surjective {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    Function.Surjective (linearSeedProjectionSL hm d) :=
  (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm.surjective.comp
    (LinearProjection.projection_surjective hm d)

theorem linearSeedProjectionSL_ker {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    (linearSeedProjectionSL hm d).ker = seedRadical d .linear := by
  unfold linearSeedProjectionSL
  rw [MonoidHom.ker_comp_of_injective _ _
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm.injective,
    LinearProjection.projection_ker]

/-- Extend a representation of the full Levi through the proved radical retraction. -/
def linearProjectionOfLeviHom {m : ℕ}
    (ρ : fullLevi m →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ) :
    parabolic m .linear →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ :=
  ρ.comp (linearLeviRetraction m)

/-- Faithfulness on the full Levi leaves exactly the specified root radical. -/
theorem linearProjectionOfLeviHom_ker {m : ℕ}
    (ρ : fullLevi m →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ)
    (hρ : Function.Injective ρ) :
    (linearProjectionOfLeviHom ρ).ker = intrinsicRadical m .linear := by
  unfold linearProjectionOfLeviHom
  rw [MonoidHom.ker_comp_of_injective _ _ hρ, linearLeviRetraction_ker]

/-- The full-parabolic projection has a two-group kernel once the separate
faithful representation of its full Levi has been constructed. -/
theorem linearProjectionOfLeviHom_ker_isPGroup {m : ℕ}
    (ρ : fullLevi m →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ)
    (hρ : Function.Injective ρ) : IsPGroup 2 (linearProjectionOfLeviHom ρ).ker := by
  rw [linearProjectionOfLeviHom_ker ρ hρ]
  exact intrinsicRadical_isPGroup m .linear

/-- The full linear parabolic projects onto SL₂ times the complementary field torus. -/
def linearProjection {m : ℕ} (hm : 1 ≤ m) :
    parabolic m .linear →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ :=
  linearProjectionOfLeviHom (linearFullLeviEmbedding hm)

theorem linearProjection_surjective {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (linearProjection hm) :=
  (linearFullLeviEquiv hm).surjective.comp (linearLeviRetraction_surjective m)

/-- The projection kills precisely the root-defined radical inside the parabolic. -/
theorem linearProjection_ker {m : ℕ} (hm : 1 ≤ m) :
    (linearProjection hm).ker = intrinsicRadical m .linear :=
  linearProjectionOfLeviHom_ker (linearFullLeviEmbedding hm)
    (linearFullLeviEmbedding_injective hm)

theorem linearProjection_ker_isPGroup {m : ℕ} (hm : 1 ≤ m) :
    IsPGroup 2 (linearProjection hm).ker :=
  linearProjectionOfLeviHom_ker_isPGroup (linearFullLeviEmbedding hm)
    (linearFullLeviEmbedding_injective hm)

/-- The linear projection required for odd-prime rank bounds in the full parabolic. -/
theorem exists_linearProjection {m : ℕ} (hm : 1 ≤ m) :
    ∃ π : parabolic m .linear →*
      Matrix.SpecialLinearGroup (Fin 2) (CoefficientField m) × (CoefficientField m)ˣ,
      IsPGroup 2 π.ker :=
  ⟨linearProjection hm, linearProjection_ker_isPGroup hm⟩

/-- Self-centralization is inside the full parabolic, with its complementary torus. -/
theorem linear_intrinsicRadical_centralizer_le {m : ℕ} (hm : 1 ≤ m) :
    centralizer (intrinsicRadical m .linear : Set (parabolic m .linear)) ≤
      intrinsicRadical m .linear := by
  unfold intrinsicRadical
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic,
    radical_eq_rootRadical]
  exact SectionGeometry.LinearRadical.centralizer_le_radical m hm

end ReeF4.ConverseParabolics
