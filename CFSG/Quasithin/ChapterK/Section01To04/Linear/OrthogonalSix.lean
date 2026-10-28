module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.OrthogonalSix.Assembly
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior

/-!
# The six-dimensional orthogonal branch of K.3.2

The actual exterior-square/permutation intertwiner and the full offender
conclusions for identified A₈ and S₈ actors are exported here. On A₈ the best
offenders have rank three, generate the group, and give ratio one; there are no
strong offenders. On S₈ the best offenders generate the group and the ratio is
three quarters. The full linear normalizer is the actual S₈ image. A faithful
ambient action with the specified normal A₈ restriction therefore has exactly
these two possibilities, with its marked subgroup and intertwiner preserved.
`source_case` constructs the corrected B.4.2(10) catalogue entry for the original
SQTK action from identification of its restricted exterior-square module.
Exhaustion of the restricted modules remains the independent recognition input.

The final theorem applies the no-strong-offender result to the literal V₆
image in the ten-dimensional exterior module. The independent §12.5 parabolic
comparison must supply the block actor and its intertwiner. No offender
conclusion is included in those comparison premises.

Source: Aschbacher–Smith, K.3.2.2–3, printed p.455/PDF p.466,
and B.4.2(10), printed p.86/PDF p.97.
-/

public section

open Representation Representation.BinaryOffender
open Atlas.Order20160A8
namespace CFSG.Quasithin.ChapterK.Linear.OrthogonalSix

/-- The literal B.7.1 consumer in K.3.2.3. The independent parabolic comparison
supplies the faithful block actor and its intertwiner; no offender property is
assumed of the six-dimensional image. -/
theorem exterior_restriction_exclusion
    (f : subspaceActionImage (SL5TenDimensional.exteriorAction 2) SL5ExteriorSquare.V₆ →*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hf : Function.Injective f)
    (E : SL5ExteriorSquare.V₆ ≃ₗ[ZMod 2] Bivectors.Six (ZMod 2))
    (hE : ∀ g v, E (subspaceImageRepresentation (SL5TenDimensional.exteriorAction 2)
      SL5ExteriorSquare.V₆ g v) = Bivectors.exteriorMap (f g).val (E v))
    {A : Subgroup SL5TenDimensional.Group}
    (hA : IsMinimalBestOffender (SL5TenDimensional.exteriorAction 2) A)
    (hstable : ∀ a ∈ A, ∀ w ∈ SL5ExteriorSquare.V₆,
      SL5TenDimensional.exteriorAction 2 a w ∈ SL5ExteriorSquare.V₆)
    (hmove : subspaceCommutator (SL5TenDimensional.exteriorAction 2) SL5ExteriorSquare.V₆ A ≠ ⊥) :
    False := by
  apply Exterior.restriction_exclusion hA hstable hmove
  apply not_strong_of_alternating_embedding
    (sl4EquivAlternating.toMonoidHom.comp f) (sl4EquivAlternating.injective.comp hf)
    (E.trans exteriorEquivNatural)
  intro g v
  change exteriorEquivNatural (E (subspaceImageRepresentation
    (SL5TenDimensional.exteriorAction 2) SL5ExteriorSquare.V₆ g v)) = _
  exact (congrArg exteriorEquivNatural (hE g v)).trans
    (exteriorEquivNatural_intertwines (f g) (E v))

end CFSG.Quasithin.ChapterK.Linear.OrthogonalSix
