module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Projection.FixedLevi
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.LeviQuotient
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalStructure

/-!
# The linear Ree seed projection with its exact two-group kernel

The root-defined radical is normal relative to the fixed seed. The proved
unique fixed Levi–radical factorization identifies the quotient by this
radical with the entire fixed Levi. Its twisted-diagonal matrix comparison
then gives PSL₂ over exactly the Ree coefficient field. The quotient map is
surjective and the Levi inclusion supplies fixed lifts. Injectivity of the
Levi comparison leaves exactly the specified radical as kernel.

The radical is a two-group because it embeds in the proved unitriangular
positive subgroup. Neither generation by involutions nor exactness of an
arbitrary fixed-point functor is used. This supplies the concrete projection
input to the intrinsic-core assembly, not the full source theorem or the
separate radical order q^11.

Source: Aschbacher–Smith F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`;
GLS3 §§2.3–2.4 for the exceptional-twist subsystem construction.
-/

public noncomputable section
namespace ReeF4.LargeLocalSeeds.LinearProjection
open Subgroup
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
variable {m : ℕ}

/-- The actual fixed linear seed maps onto PSL₂ over its Ree coefficient field. -/
def projection (hm : 1 ≤ m) (d : LocalBlockInput m) :
    standardSeed d .linear →* LinearQuotient m := by
  letI := seedRadical_normal d .linear
  exact (fixedLeviEquivPSL hm d).toMonoidHom.comp
    ((fixedLeviEquivSeedQuotient d .linear).symm.toMonoidHom.comp
      (QuotientGroup.mk' (seedRadical d .linear)))

/-- Unique fixed factorization and the faithful Levi comparison give surjectivity. -/
theorem projection_surjective (hm : 1 ≤ m) (d : LocalBlockInput m) :
    Function.Surjective (projection hm d) := by
  let := seedRadical_normal d .linear
  exact (fixedLeviEquivPSL hm d).surjective.comp
    ((fixedLeviEquivSeedQuotient d .linear).symm.surjective.comp
      (QuotientGroup.mk'_surjective (seedRadical d .linear)))

/-- The kernel is precisely the original root-defined radical. -/
theorem projection_ker (hm : 1 ≤ m) (d : LocalBlockInput m) :
    (projection hm d).ker = seedRadical d .linear := by
  let := seedRadical_normal d .linear
  unfold projection
  rw [MonoidHom.ker_comp_of_injective _ _ (fixedLeviEquivPSL hm d).injective,
    MonoidHom.ker_comp_of_injective _ _
      (fixedLeviEquivSeedQuotient d .linear).symm.injective,
    QuotientGroup.ker_mk']

/-- The projection restricts to the actual matrix identification on the fixed
Levi, so its inverse gives a fixed lift of every target element. -/
theorem projection_fixedLevi (hm : 1 ≤ m) (d : LocalBlockInput m)
    (l : fixedLevi d .linear) :
    projection hm d (fixedLeviInclusion d .linear l) =
      fixedLeviEquivPSL hm d l := by
  let := seedRadical_normal d .linear
  change fixedLeviEquivPSL hm d
    ((fixedLeviEquivSeedQuotient d .linear).symm
      (QuotientGroup.mk' (seedRadical d .linear)
        (fixedLeviInclusion d .linear l))) = _
  rw [← fixedLeviEquivSeedQuotient_apply, MulEquiv.symm_apply_apply]

end LinearProjection

/-- The concrete projection, exact root kernel and its two-group property,
with no additional local-structure or fixed-point-surjectivity premises. -/
theorem exists_linearSeedProjection {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    ∃ f : standardSeed d .linear →* LinearQuotient m,
      Function.Surjective f ∧ f.ker = seedRadical d .linear ∧
        IsPGroup 2 (seedRadical d .linear) :=
  ⟨LinearProjection.projection hm d, LinearProjection.projection_surjective hm d,
    LinearProjection.projection_ker hm d, seedRadical_isPGroup d .linear⟩

end ReeF4.LargeLocalSeeds
