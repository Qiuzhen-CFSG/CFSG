module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The special affine group on the natural two-dimensional module

The group is the actual semidirect product of the additive plane by SL₂(F).
Its translation subgroup is the kernel of the linear-part homomorphism.
The quotient and conjugation formulas keep the natural action explicit.

This is the common local model for the point and line stabilizers in PSL₃,
as used in Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Matrix.SL2
variable (F : Type*) [Field F]
def naturalAction : SL(2, F) →* MulAut (Multiplicative (Fin 2 → F)) where
  toFun g := (SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change SpecialLinearGroup.toLin' 1 (Multiplicative.toAdd v) = Multiplicative.toAdd v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change SpecialLinearGroup.toLin' (g * h) (Multiplicative.toAdd v) =
      SpecialLinearGroup.toLin' g (SpecialLinearGroup.toLin' h (Multiplicative.toAdd v))
    rw [map_mul]
    rfl
abbrev Affine := Multiplicative (Fin 2 → F) ⋊[naturalAction F] SL(2, F)
@[simp] theorem naturalAction_apply (g : SL(2, F)) (v : Multiplicative (Fin 2 → F)) :
    Multiplicative.toAdd (naturalAction F g v) = g.val *ᵥ Multiplicative.toAdd v := rfl

/-- The translation subgroup, defined as the kernel of the linear-part map. -/
def translations : Subgroup (Affine F) :=
  (SemidirectProduct.rightHom : Affine F →* SL(2, F)).ker

instance translations_normal : (translations F).Normal :=
  inferInstanceAs (SemidirectProduct.rightHom : Affine F →* SL(2, F)).ker.Normal

/-- Translations are precisely the image of the additive vector group. -/
theorem range_inl_eq_translations :
    (SemidirectProduct.inl : Multiplicative (Fin 2 → F) →* Affine F).range =
      translations F := SemidirectProduct.range_inl_eq_ker_rightHom

/-- The vector coordinates on the translation subgroup. -/
noncomputable def translationsEquiv : Multiplicative (Fin 2 → F) ≃* translations F :=
  (MonoidHom.ofInjective SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr (range_inl_eq_translations F))

@[simp] theorem translationsEquiv_apply (v : Multiplicative (Fin 2 → F)) :
    (translationsEquiv F v : Affine F) = SemidirectProduct.inl v := rfl

/-- The quotient by translations retains exactly the linear part. -/
def quotientTranslationsEquiv : (Affine F ⧸ translations F) ≃* SL(2, F) :=
  QuotientGroup.quotientKerEquivOfRightInverse SemidirectProduct.rightHom
    SemidirectProduct.inr SemidirectProduct.rightHom_inr

@[simp] theorem quotientTranslationsEquiv_mk (g : Affine F) :
    quotientTranslationsEquiv F (QuotientGroup.mk' (translations F) g) = g.right := rfl

/-- Conjugation on translations is the literal natural matrix action. -/
theorem conjugate_inl (g : Affine F) (v : Multiplicative (Fin 2 → F)) :
    g * SemidirectProduct.inl v * g⁻¹ =
      SemidirectProduct.inl (naturalAction F g.right v) := by
  apply SemidirectProduct.ext
  · simp [mul_comm, mul_left_comm]
  · simp

end Matrix.SL2
