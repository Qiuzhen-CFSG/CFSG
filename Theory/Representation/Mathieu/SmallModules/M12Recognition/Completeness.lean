module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.Completeness
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointExtension

/-!
# Recognition of the small faithful binary M₁₂ module

Every faithful binary representation of the actual M₁₂ of dimension at most
ten is equivalent to its twelve-point augmentation space modulo constants.
In particular, this proves the intrinsic module-recognition input for the
M₁₂ case of Aschbacher--Smith G.7.3(2).

The order-eleven bound forces dimension ten and an irreducible restriction
to the actual M₁₁ point stabilizer. The complete M₁₁ classification identifies
that restriction with the reference heart. Transport through this equivalence
makes the point actions agree literally, and extension rigidity identifies the
entire M₁₂ action. Thus the recognition predicate has the actual identity group
marking; no action of Aut(M₁₂) on twelve points is needed.

All classification inputs of `M12Recognition` are discharged here. This
extension avoids an import cycle with the earlier conditional reduction.
The ambient generalized-Fitting and rank arguments remain with Chapter G.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3(2),
printed p.348 (PDF p.359), citing G. D. James, *The modular characters of
the Mathieu groups*, J. Algebra 27 (1973), 57--111.
-/

public section
namespace Representation.MathieuSmall.M12Recognition
open Sporadic.Mathieu

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) M12 V)

/-- A faithful binary M₁₂ representation of dimension at most ten is equivalent
to the actual ten-dimensional heart, with the original group marking. -/
theorem equiv_heart_of_faithful_finrank_le_ten
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Nonempty (ρ.Equiv m12HeartRepresentation) := by
  obtain ⟨e⟩ := PointClassification.point_restriction_equiv ρ hf hd
  have E := coordinateEquiv ρ e.toLinearEquiv
  rw [PointExtension.eq_of_point_agreement _ (coordinateRepresentation_on_point ρ e)] at E
  exact ⟨E⟩

/-- The M₁₂ recognition input for G.7.3(2), including an actual group
automorphism and an equivariant linear equivalence. Faithfulness and the
degree bound already force irreducibility, so no separate premise is needed. -/
theorem isM12Heart_of_faithful_finrank_le_ten
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10) :
    IsM12Heart ρ :=
  ⟨MulEquiv.refl M12, equiv_heart_of_faithful_finrank_le_ten ρ hf hd⟩

end Representation.MathieuSmall.M12Recognition
