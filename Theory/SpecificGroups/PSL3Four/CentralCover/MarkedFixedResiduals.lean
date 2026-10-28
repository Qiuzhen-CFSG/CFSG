module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals
public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphFieldKernel.Source

/-!
# Fixed residuals for one marked four-cover action

Each statement retains one actual cover automorphism and its projective
compatibility equation. A standard graph-field lift exists on every elementary
central cover. Together with an already marked graph or field lift, it supplies
the other factor needed by the existing residual calculations. The mixed row
uses the central two-kernel and the coprime elementary-nine image directly.

Source: Aschbacher–Smith, I.2.2(3b), pp.409–410, and 15.3.38, pp.1136–1137.
No simultaneous conjugacy of the original graph and field actors is required.
-/

public noncomputable section
namespace Matrix.PSL3Four
open Subgroup
variable {E : Type*} [Group E] [Finite E]

omit [Finite E] in
private theorem FourCover.kernel_sq (c : FourCover E)
    (z : E) (hz : z ∈ c.toMonoidHom.ker) : z ^ 2 = 1 := by
  let := c.center_isKleinFour
  let w : center E := ⟨z, c.ker_le_center hz⟩
  have h := Monoid.pow_exponent_eq_one w
  rw [IsKleinFour.exponent_two] at h
  exact congrArg Subtype.val h

omit [Finite E] in
private theorem FourCover.descends_of_compatible (c : FourCover E)
    (a : MulAut E) (b : MulAut PSL)
    (hc : ∀ x, c.toMonoidHom (a x) = b (c.toMonoidHom x)) :
    c.toCover.autMap c.ker_eq_center a = b := by
  ext x
  obtain ⟨y, rfl⟩ := c.surjective x
  rw [c.toCover.autMap_apply, hc]

/-- The actual graph lift needs no separately supplied field lift. -/
def FourCover.graphResidualEquivOfCompatible (c : FourCover E) (a : MulAut E)
    (ha : ∀ x, c.toMonoidHom (a x) = PSL3.OuterSolvable.graph F (c.toMonoidHom x)) :
    pResidual 2 a.fixedSubgroup ≃* ProjectiveSpecialLinearGroup (Fin 2) F := by
  let := c.isPerfect
  let h := CentralCover.GraphFieldKernel.exists_graphField_lift
    c.toMonoidHom c.surjective c.ker_le_center c.kernel_sq
  let z := Classical.choose h
  have hz := (Classical.choose_spec h).1
  have ha' := c.descends_of_compatible a _ ha
  have hz' := c.descends_of_compatible z _ hz
  let b : CoverActions E c := {
    graph := a
    field := a⁻¹ * z
    graph_compatible := ha
    field_compatible := fun x => by
      rw [← c.toCover.autMap_apply c.ker_eq_center, map_mul, map_inv, ha', hz']
      change ((PSL3.OuterSolvable.graph F)⁻¹ *
        (PSL3.OuterSolvable.graph F * pslFrobenius)) (c.toMonoidHom x) = _
      rw [inv_mul_cancel_left] }
  exact b.graphResidualEquivPSL2Four

/-- The actual field lift needs no separately supplied graph lift. -/
def FourCover.fieldResidualEquivOfCompatible (c : FourCover E) (a : MulAut E)
    (ha : ∀ x, c.toMonoidHom (a x) = pslFrobenius (c.toMonoidHom x)) :
    pResidual 2 a.fixedSubgroup ≃* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) := by
  let := c.isPerfect
  let h := CentralCover.GraphFieldKernel.exists_graphField_lift
    c.toMonoidHom c.surjective c.ker_le_center c.kernel_sq
  let z := Classical.choose h
  have hz := (Classical.choose_spec h).1
  have ha' := c.descends_of_compatible a _ ha
  have hz' := c.descends_of_compatible z _ hz
  let b : CoverActions E c := {
    graph := z * a⁻¹
    field := a
    graph_compatible := fun x => by
      rw [← c.toCover.autMap_apply c.ker_eq_center, map_mul, map_inv, hz', ha']
      change ((PSL3.OuterSolvable.graph F * pslFrobenius) * pslFrobenius⁻¹)
        (c.toMonoidHom x) = _
      rw [mul_inv_cancel_right]
    field_compatible := ha }
  exact b.fieldResidualEquivPSL3Two

/-- The actual mixed lift has elementary-nine residual, independently of any
choice of compatible graph and field factors on the cover. -/
def FourCover.graphFieldResidualEquivOfCompatible (c : FourCover E) (a : MulAut E)
    (ha : ∀ x, c.toMonoidHom (a x) =
      (PSL3.OuterSolvable.graph F * pslFrobenius) (c.toMonoidHom x)) :
    pResidual 2 a.fixedSubgroup ≃* Multiplicative (Fin 2 → ZMod 3) := by
  let b := PSL3.OuterSolvable.graph F * pslFrobenius
  let f := MulAut.fixedResidualMap 2 a b c.toMonoidHom ha
  let e := projectiveGraphFieldResidualEquiv
  have hi : Function.Injective f := by
    apply MonoidHom.injective_of_isPPerfect_of_coprime_abelian_image
      (Subgroup.isPPerfect_pResidual 2) f
      (MulAut.fixedResidualMap_ker_le_center 2 a b c.toMonoidHom ha c.ker_le_center)
      (MulAut.fixedResidualMap_ker_isPGroup 2 a b c.toMonoidHom ha c.ker_isTwoGroup)
    · intro x y
      apply e.injective
      simp only [map_mul]
      exact mul_comm _ _
    · exact (by decide : Nat.Coprime 2 3)
    · intro x
      apply e.injective
      rw [map_pow, map_one]
      change (3 : ℕ) • (e (f x)).toAdd = 0
      exact ZModModule.char_nsmul_eq_zero 3 _
  exact (MulEquiv.ofBijective f ⟨hi, MulAut.fixedResidualMap_surjective 2 a b
    c.toMonoidHom c.surjective c.ker_le_center c.ker_isTwoGroup ha⟩).trans e

end Matrix.PSL3Four
end
