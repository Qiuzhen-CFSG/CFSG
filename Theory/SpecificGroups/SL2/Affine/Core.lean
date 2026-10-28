module

public import Theory.SpecificGroups.SL2.Affine
public import Theory.SpecificGroups.SL2.TwoCore
public import Theory.ElementaryAbelian.Quotient

/-!
# The two-core of the special affine plane group

In characteristic two the translations are elementary abelian and normal.
Every normal two-subgroup maps trivially into SL₂(F), by `SL2.TwoCore`,
so translations are exactly O₂. The quotient equivalence records its value
on each affine element, retaining the actual linear part.

Source: the local calculation in Aschbacher–Smith, F.1.12(I)(1),
printed pp.262–264. The core calculation also includes the binary field.
-/

@[expose] public section
open Matrix
open scoped MatrixGroups
namespace Matrix.SL2
variable (F : Type*) [Field F] [CharP F 2]

instance plane_elementary : IsElementaryAbelian 2 (Multiplicative (Fin 2 → F)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro v
    apply Multiplicative.toAdd.injective
    ext i
    simp [pow_two, CharTwo.add_self_eq_zero]

instance translations_elementary : IsElementaryAbelian 2 (translations F) :=
  IsElementaryAbelian.of_surjective (translationsEquiv F).toMonoidHom
    (translationsEquiv F).surjective

theorem translations_isPGroup : IsPGroup 2 (translations F) :=
  IsElementaryAbelian.isPGroup 2 _

/-- The translation plane is the full two-core, including over F₂. -/
theorem affine_twoCore_eq [Finite F] : pCore 2 (Affine F) = translations F := by
  apply le_antisymm
  · let f : Affine F →* SL(2, F) := SemidirectProduct.rightHom
    have hn : ((pCore 2 (Affine F)).map f).Normal :=
      Subgroup.Normal.map inferInstance f SemidirectProduct.rightHom_surjective
    have hle : (pCore 2 (Affine F)).map f ≤ pCore 2 SL(2, F) :=
      le_sSup ⟨hn, pCore_isPGroup.map f⟩
    rw [twoCore_eq_bot F] at hle
    exact (Subgroup.map_eq_bot_iff (pCore 2 (Affine F))).mp (le_bot_iff.mp hle)
  · exact le_sSup ⟨inferInstance, translations_isPGroup F⟩

/-- The actual quotient by O₂ is the special linear group. -/
noncomputable def affineCoreQuotientEquiv [Finite F] :
    (Affine F ⧸ pCore 2 (Affine F)) ≃* SL(2, F) :=
  (QuotientGroup.quotientMulEquivOfEq (affine_twoCore_eq F)).trans
    (quotientTranslationsEquiv F)

@[simp] theorem affineCoreQuotientEquiv_mk [Finite F] (g : Affine F) :
    affineCoreQuotientEquiv F (QuotientGroup.mk' (pCore 2 (Affine F)) g) = g.right := rfl
end Matrix.SL2
