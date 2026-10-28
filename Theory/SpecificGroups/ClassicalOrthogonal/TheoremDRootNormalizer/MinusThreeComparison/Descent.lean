module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison.Model

/-!
# Faithful quadratic descent of the unitary exterior square

If the actual second compound matrices preserve the concrete descent space,
they induce a faithful action by isometries of its norm quadratic form.
Quadratic preservation follows from the Pfaffian identity; faithfulness follows
because the descent vectors span all bivectors after extending scalars.
The sole premise here is subspace invariance. No commutator-image conclusion
is assumed or asserted. This isolates the two independent matrix and group
generation obligations in the twisted A₃/D₃ comparison (GLS3 §2.7).
-/

public noncomputable section
namespace ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
open Atlas.Order20160A8.Bivectors

variable (n : ℕ) [NeZero n]

/-- The literal unitary exterior matrices preserve the specified descent vectors. -/
@[expose] def Descends : Prop := ∀ (g : SU n) (v : Space n),
  exterior n g (toBivector n v) ∈ descentSpace n

variable (hD : Descends n)

private def descendedMap (g : SU n) : Space n →ₗ[FixedField n] Space n :=
  (descentEquiv n).symm.toLinearMap.comp
    ((((exterior n g).toLinearMap.restrictScalars (FixedField n)).comp
      (toBivector n)).codRestrict (descentSpace n) (hD g))

private theorem toBivector_descendedMap (g : SU n) (v : Space n) :
    toBivector n (descendedMap n hD g v) = exterior n g (toBivector n v) := by
  exact congrArg Subtype.val ((descentEquiv n).apply_symm_apply
    ⟨exterior n g (toBivector n v), hD g v⟩)

private def descendedEquiv (g : SU n) : Space n ≃ₗ[FixedField n] Space n where
  __ := descendedMap n hD g
  invFun := descendedMap n hD g⁻¹
  left_inv v := by
    apply toBivector_injective n
    change toBivector n (descendedMap n hD g⁻¹ (descendedMap n hD g v)) = toBivector n v
    rw [toBivector_descendedMap, toBivector_descendedMap]
    change (exterior n g⁻¹ * exterior n g) (toBivector n v) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    apply toBivector_injective n
    change toBivector n (descendedMap n hD g (descendedMap n hD g⁻¹ v)) = toBivector n v
    rw [toBivector_descendedMap, toBivector_descendedMap]
    change (exterior n g * exterior n g⁻¹) (toBivector n v) = _
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

/-- The full orthogonal group of the explicit six-dimensional norm form. -/
abbrev FullOrthogonal := Minus.Orthogonal (FixedField n) (Space n) (form n)

/-- Its literal commutator subgroup, before any projective quotient. -/
abbrev Omega := Minus.Omega (FixedField n) (Space n) (form n)

/-- Restriction of the actual exterior square, in the displayed norm coordinates. -/
def orthogonalAction : SU n →* FullOrthogonal n where
  toFun g := ⟨descendedEquiv n hD g, by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    apply Subtype.ext
    rw [← pfaffian_toBivector, ← pfaffian_toBivector]
    exact (congrArg pfaffian (toBivector_descendedMap n hD g v)).trans
      (exterior_pfaffian n g (toBivector n v))⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply toBivector_injective n
    change toBivector n (descendedMap n hD 1 v) = toBivector n v
    rw [toBivector_descendedMap, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    apply toBivector_injective n
    change toBivector n (descendedMap n hD (g * h) v) =
      toBivector n (descendedMap n hD g (descendedMap n hD h v))
    rw [toBivector_descendedMap, toBivector_descendedMap, toBivector_descendedMap,
      map_mul]
    rfl

/-- The constructed action intertwines with the genuine six-minor representation. -/
theorem orthogonalAction_intertwines (g : SU n) (v : Space n) :
    toBivector n ((orthogonalAction n hD g).val v) =
      exterior n g (toBivector n v) := toBivector_descendedMap n hD g v

/-- Faithfulness follows on the descent space, without any group-order comparison. -/
theorem orthogonalAction_injective : Function.Injective (orthogonalAction n hD) := by
  intro g h he
  apply exterior_injective n
  apply LinearEquiv.toLinearMap_injective
  apply bivector_ext n
  intro v
  change exterior n g (toBivector n v) = exterior n h (toBivector n v)
  rw [← orthogonalAction_intertwines n hD, ← orthogonalAction_intertwines n hD, he]

end ClassicalOrthogonal.TheoremDRootNormalizer.MinusThreeComparison
