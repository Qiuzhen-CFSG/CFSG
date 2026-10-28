module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Action
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# The literal outer-stabilizer discrepancy in H.15.1

The source weight-two family has 22 vectors. Its inner and full outer
stabilizers have orders 20160 and 40320, respectively. The latter therefore
cannot be isomorphic to the actual PSL(3,4) carrier, whose order is 20160.
This diagnostic keeps the outer statement separate from the inner-stabilizer
identification used by 8.1.1.

Source: Aschbacher--Smith, H.15.1(1), printed p.398, and 8.1.1, printed p.712.
-/

public section
namespace MathieuCode

/-- The literal full-outer version of the printed L3(4) claim fails by order.
This does not contradict the inner-stabilizer clause actually used in 8.1.1. -/
theorem m22WeightTwoVector_outer_not_equiv_PSL (i : Fin 22) :
    ¬ Nonempty (m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i) ≃*
      Matrix.PSL3Four.PSL) := by
  rintro ⟨e⟩
  have h := Nat.card_congr e.toEquiv
  rw [m22WeightTwoVector_outer_stabilizer_card, Matrix.PSL3Four.card_PSL] at h
  omega

theorem m22WeightTwoFamily_outer_not_equiv_PSL {v : M22Cocode}
    (hv : v ∈ m22WeightTwoFamily) :
    ¬ Nonempty (m22CocodeStabilizer m22OuterCocodeRepresentation v ≃* Matrix.PSL3Four.PSL) := by
  obtain ⟨i, rfl⟩ := hv
  exact m22WeightTwoVector_outer_not_equiv_PSL i

end MathieuCode
