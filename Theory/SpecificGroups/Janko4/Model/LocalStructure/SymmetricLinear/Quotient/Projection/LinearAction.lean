module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.Generators
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.Projection.LinearAction.Certificates

/-!
# The actual max4 action on the three-dimensional binary section

The checked 31-row numerator and 28-row denominator lie in the original
112-dimensional representation. Compatible pairs preserve the numerator and
induce the specified action on its quotient coordinates. They form a
submonoid of the finite product of the actual matrix carrier with SL₃(2),
so they are also closed under inverses. The checked coordinate map makes the
induced matrix unique. This constructs the homomorphism on the literal
subgroup closure, with ordinary multiplication and no inversion of matrices.

Source: ATLAS J4G1-max4W1 and J4G1-f2r112B0, attributed in
`SymmetricLinear.Model` and `Janko4.Model.Data`. The local factor is used in
Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528.
See `LinearAction/source/README.md` for the certificate provenance.
-/

public section
namespace Janko4.LocalStructure.SymmetricLinear.Projection
open Matrix

namespace LinearSection
/-- A simultaneous action on the numerator and its three quotient coordinates.
The equation on `basis` uses the actual 112-dimensional matrix of `g`.
The equation on `quotient` says that the denominator is preserved. -/
@[expose] def Compatible (g : Model) (s : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Prop :=
  ∃ t : Matrix (Fin 31) (Fin 31) (ZMod 2),
    t * basis = basis * toMatrix g ∧ t * quotient = quotient * (s : Matrix (Fin 3) (Fin 3) (ZMod 2))

private lemma compatible_one : Compatible 1 1 := by
  refine ⟨1, ?_, ?_⟩ <;> simp [map_one]

private lemma compatible_mul {g h : Model} {s t : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hg : Compatible g s) (hh : Compatible h t) : Compatible (g * h) (s * t) := by
  obtain ⟨a, ha, hqa⟩ := hg
  obtain ⟨b, hb, hqb⟩ := hh
  refine ⟨a * b, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, map_mul]
  · rw [Matrix.mul_assoc, hqb, ← Matrix.mul_assoc, hqa, Matrix.mul_assoc]
    exact congrArg (quotient * ·) (Matrix.SpecialLinearGroup.coe_mul s t).symm

private def compatibleMonoid : Submonoid (Model × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) where
  carrier := {p | Compatible p.1 p.2}
  one_mem' := compatible_one
  mul_mem' := fun ha hb => compatible_mul ha hb

private lemma compatible_inv {g : Model} {s : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : Compatible g s) : Compatible g⁻¹ s⁻¹ := by
  let x : Model × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := (g, s)
  have hx : x ∈ compatibleMonoid := h
  have hi : x⁻¹ ∈ compatibleMonoid := by
    rw [← one_mul x⁻¹, ← pow_one x, ← pow_orderOf_eq_one x,
      ← pow_sub x (orderOf_pos x)]
    exact compatibleMonoid.pow_mem hx _
  exact hi

private lemma compatible_unique {g : Model} {s t : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (hs : Compatible g s) (ht : Compatible g t) : s = t := by
  obtain ⟨a, ha, hqa⟩ := hs
  obtain ⟨b, hb, hqb⟩ := ht
  have h : quotient * (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) = quotient * (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    calc
      quotient * (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) = a * quotient := hqa.symm
      _ = a * (basis * coordinates) := by rw [basis_coordinates]
      _ = b * (basis * coordinates) := by rw [← Matrix.mul_assoc, ha, ← hb, Matrix.mul_assoc]
      _ = quotient * (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by rw [basis_coordinates, hqb]
  exact Subtype.ext (quotient_mul_injective _ _ h)

private def liftGroup : Subgroup Model where
  carrier := {g | ∃ s, Compatible g s}
  one_mem' := ⟨1, compatible_one⟩
  mul_mem' := by
    rintro g h ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s * t, compatible_mul hs ht⟩
  inv_mem' := by
    rintro g ⟨s, hs⟩
    exact ⟨s⁻¹, compatible_inv hs⟩

private lemma first_compatible : Compatible first firstLinear :=
  ⟨firstAction, first_basis, first_quotient⟩

private lemma second_compatible : Compatible second secondLinear :=
  ⟨secondAction, second_basis, second_quotient⟩

private lemma max4_le_liftGroup : max4Subgroup ≤ liftGroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨firstLinear, first_compatible⟩
  · exact ⟨secondLinear, second_compatible⟩

private lemma exists_linear (g : max4Subgroup) : ∃ s, Compatible g s :=
  max4_le_liftGroup g.property
end LinearSection

open LinearSection in
/-- The action of the literal max4 subgroup on the binary section U31/U28,
with ordinary matrix multiplication on quotient coordinates. -/
noncomputable def linearHom : max4Subgroup →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun g := Classical.choose (exists_linear g)
  map_one' := compatible_unique (Classical.choose_spec (exists_linear 1)) compatible_one
  map_mul' g h := compatible_unique (Classical.choose_spec (exists_linear (g * h)))
    (compatible_mul (Classical.choose_spec (exists_linear g))
      (Classical.choose_spec (exists_linear h)))

lemma linearHom_spec (g : max4Subgroup) : LinearSection.Compatible g (linearHom g) :=
  Classical.choose_spec (LinearSection.exists_linear g)

/-- The same numerator representative realizes the actual ambient action and
its induced quotient action. In particular zero quotient coordinates remain
zero, so this is an action on U31/U28. -/
lemma linearHom_section_action (g : max4Subgroup) (v : Fin 31 → ZMod 2) :
    ∃ w : Fin 31 → ZMod 2,
      w ᵥ* LinearSection.basis = (v ᵥ* LinearSection.basis) ᵥ* toMatrix (g : Model) ∧
      w ᵥ* LinearSection.quotient =
        (v ᵥ* LinearSection.quotient) ᵥ* (linearHom g : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  obtain ⟨t, ht, hq⟩ := linearHom_spec g
  refine ⟨v ᵥ* t, ?_, ?_⟩
  · rw [Matrix.vecMul_vecMul, ht, Matrix.vecMul_vecMul]
  · rw [Matrix.vecMul_vecMul, hq, Matrix.vecMul_vecMul]

lemma linearHom_first : linearHom first = firstLinear :=
  LinearSection.compatible_unique (linearHom_spec _) LinearSection.first_compatible

lemma linearHom_second : linearHom second = secondLinear :=
  LinearSection.compatible_unique (linearHom_spec _) LinearSection.second_compatible

end Janko4.LocalStructure.SymmetricLinear.Projection
