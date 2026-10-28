module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Ratio
public import Theory.Representation.BinaryOffender.ActionImage
/-!
# Non-FF sections of the deleted A₅ tensor square

The full-normalizer bound exceeds twice the elementary actor rank, hence
in particular exceeds the FF threshold. Passing to the actual action image
removes any kernel of an ambient section action while retaining its normal
A₅ product marking. The original D.3.9 two-section argument can therefore
use the same non-FF comparison for natural and deleted local types.

Source: Aschbacher–Smith D.3.7 and D.3.9, printed pp.197–200.
-/

public section
namespace BinaryPermutation.FiveTensorSquare
open Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- A faithful actor extending the marked deleted square is non-FF. -/
theorem not_ff_of_marked_normal_range
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : Alt × Alt →* H) [i.range.Normal]
    (e : Representation.Equiv (ρ.comp i) deletedAction) : ¬ IsFFModule ρ := by
  rintro ⟨A,hA,hsmall⟩
  have h := faithful_actor_ratio_gt_two ρ hρ i e hA
  omega

/-- The actual faithful image of a marked deleted-square section is non-FF. -/
theorem image_not_ff_of_marked_normal_range
    (ρ : Representation (ZMod 2) H U)
    (i : Alt × Alt →* H) [i.range.Normal]
    (e : Representation.Equiv (ρ.comp i) deletedAction) :
    ¬ IsFFModule (imageRepresentation ρ) := by
  let j : Alt × Alt →* actionImage ρ := (actionHom ρ).comp i
  have hj : j.range = i.range.map (actionHom ρ) := MonoidHom.range_comp _ _
  let : j.range.Normal := by
    rw [hj]
    exact Subgroup.Normal.map inferInstance (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
  let e' : Representation.Equiv ((imageRepresentation ρ).comp j) deletedAction := {
    __ := e.toLinearEquiv
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap k v }
  exact not_ff_of_marked_normal_range (imageRepresentation ρ)
    (imageRepresentation_injective ρ) j e'
end BinaryPermutation.FiveTensorSquare
