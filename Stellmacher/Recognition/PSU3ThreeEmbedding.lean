module

public import Stellmacher.Recognition.PSU3ThreeCoordinates
public import Theory.SpecificGroups.PSL3Two.UnitaryRepresentation
public import Theory.SpecificGroups.PSL3Two.NonSolvable

/-!
# A proper nonsolvable subgroup of PSU₃(3)

The faithful unitary representation of SL₃(2) over the computable field of
order nine transports to ABG's standard matrix group over `GaloisField 3 2`.
Its projective image remains faithful because determinant-one scalar matrices
in dimension three are trivial in characteristic three. The image is proper:
PSU₃(3) contains an element whose order divides none of three, four, or seven,
whereas every element of SL₃(2) has order dividing one of these numbers.

Since SL₃(2) is nonsolvable, this proper subgroup excludes PSU₃(3) from the
minimal-simple groups, including every group satisfying `ABG.IsPSU3 G 3`.

Source: the concrete matrix representation and the element-order calculations
in the imported modules; the defining proper-subgroup condition for minimal
simplicity.
-/

namespace Stellmacher.Recognition.PSU3Three

/-- The concrete binary linear subgroup of the standard PSU₃(3). -/
public noncomputable def sl3TwoEmbedding :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* ABG.PSU3 3 1 (by decide) :=
  lift Matrix.PSL3Two.unitaryRepresentation Matrix.PSL3Two.unitaryRepresentation_unitary

public theorem sl3TwoEmbedding_injective : Function.Injective sl3TwoEmbedding :=
  lift_injective _ _ Matrix.PSL3Two.unitaryRepresentation_injective

/-- The embedded SL₃(2) is a proper subgroup of the actual projective model. -/
public theorem sl3TwoEmbedding_range_lt_top : sl3TwoEmbedding.range < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  exact fun h => not_surjective sl3TwoEmbedding (MonoidHom.range_eq_top.mp h)

/-- A proper injective homomorphism from the actual binary matrix group. -/
public theorem exists_injective_sl3_two_hom :
    ∃ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* ABG.PSU3 3 1 (by decide),
      Function.Injective f ∧ f.range < ⊤ :=
  ⟨sl3TwoEmbedding, sl3TwoEmbedding_injective, sl3TwoEmbedding_range_lt_top⟩

/-- The standard projective unitary group PSU₃(3) is not minimal simple. -/
public theorem not_isMinimalSimple : ¬ IsMinimalSimple (ABG.PSU3 3 1 (by decide)) := by
  intro h
  exact not_surjective sl3TwoEmbedding
    (h.surjective_of_injective not_isSolvable_sl3_two
      sl3TwoEmbedding sl3TwoEmbedding_injective)

end Stellmacher.Recognition.PSU3Three

/-- The unitary-three recognition alternative never gives a minimal simple group. -/
public theorem Stellmacher.Recognition.not_isMinimalSimple_of_isPSU3_three
    {G : Type*} [Group G] [Finite G] (hG : ABG.IsPSU3 G 3) : ¬ IsMinimalSimple G := by
  intro h
  exact PSU3Three.not_isMinimalSimple ((isMinimalSimple_iff_of_isPSU3_three hG).mp h)
