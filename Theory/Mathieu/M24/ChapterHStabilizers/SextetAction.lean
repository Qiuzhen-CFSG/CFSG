module

public import Theory.Mathieu.M24.LocalGeometry.SextetCore
public import Theory.Representation.HexacodeAction.Field
public import Theory.GroupTheory.SolvableResidual

/-!
# The genuine sextet quotient and its native conjugation module

The affine hexacode coordinates identify the intrinsic two-core of the native
standard sextet stabilizer with the additive hexacode. Conjugation becomes the
literal six-dimensional binary hexacode action. The terminal derived subgroup
acts linearly on its compatible three-dimensional F4 structure.

The intrinsic quotient is the actual hexacode automorphism group. Its action
on the six tetrads is surjective with a kernel of order three and does not
split, preserving the covering group in the source statement.

Source: Aschbacher–Smith H.14.1(2), printed pp.396–397, citing Aschbacher,
*Sporadic Groups*, 19.9. The affine model and nonsplitting certificates are
reused from the ATLAS ports of Gerald Höhn and ATLAS contributors, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research and
Attribution License 1.0; see `LICENSES/ATLAS.txt`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.SextetAction
open M24LocalGeometry M24LocalGeometry.SextetCore Atlas.Codes
open Representation.Hexacode
noncomputable section

abbrev Stabilizer := sextetStabilizer standardSextet
abbrev Kernel := pCore 2 Stabilizer
abbrev Quotient := Stabilizer ⧸ Kernel

/-- The intrinsic quotient's action on the six tetrads. -/
def quotientColumns : Quotient →* Equiv.Perm (Fin 6) :=
  hexCoordinateSixHom.comp coreQuotientEquiv.toMonoidHom

theorem quotientColumns_mk (g : Stabilizer) :
    quotientColumns (QuotientGroup.mk g) = columnHom g := rfl

theorem quotientColumns_surjective : Function.Surjective quotientColumns :=
  hexCoordinateSix_surjective.comp coreQuotientEquiv.surjective

theorem quotient_card : Nat.card Quotient = 2160 :=
  (Nat.card_congr coreQuotientEquiv.toEquiv).trans hexAutomorphisms_card

theorem quotientColumns_kernel_card : Nat.card quotientColumns.ker = 3 := by
  have he : quotientColumns.ker.map coreQuotientEquiv.toMonoidHom =
      hexCoordinateSixHom.ker := by
    rw [quotientColumns, ← MonoidHom.comap_ker]
    apply Subgroup.map_comap_eq_self
    rw [coreQuotientEquiv.toMonoidHom.range_eq_top_of_surjective coreQuotientEquiv.surjective]
    exact le_top
  calc
    Nat.card quotientColumns.ker =
        Nat.card (quotientColumns.ker.map coreQuotientEquiv.toMonoidHom) :=
      (Subgroup.card_map_of_injective coreQuotientEquiv.injective).symm
    _ = 3 := by rw [he, hexCoordinateSix_kernel, Nat.card_zpowers, hexZ_order]

theorem quotientColumns_nonsplit :
    ¬ ∃ s : Equiv.Perm (Fin 6) →* Quotient,
      quotientColumns.comp s = MonoidHom.id _ := by
  rintro ⟨s, hs⟩
  exact hex_no_section ⟨coreQuotientEquiv.toMonoidHom.comp s, hs⟩

theorem quotient_not_symmetric : ¬ Nonempty (Quotient ≃* Equiv.Perm (Fin 6)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr e.toEquiv
  rw [quotient_card, Nat.card_eq_fintype_card, Fintype.card_perm] at hc
  norm_num at hc

/-- Translation coordinates in the native intrinsic two-core. -/
def translation : Multiplicative hexacode →* Kernel :=
  (sextetEquiv.symm.toMonoidHom.comp sextetTranslation).codRestrict _ (by
    intro t
    change sextetEquiv.symm (sextetTranslation t) ∈ pCore 2 Stabilizer
    rw [← quotientHom_ker]
    change sextetQuotient (sextetEquiv (sextetEquiv.symm (sextetTranslation t))) = 1
    rw [sextetEquiv.apply_symm_apply, sextetQuotient_translation])

theorem translation_bijective : Function.Bijective translation := by
  constructor
  · intro x y h
    exact sextetTranslation_injective
      (sextetEquiv.symm.injective (congrArg Subtype.val h))
  · intro g
    have hg : sextetEquiv g.val ∈ sextetQuotient.ker := by
      change g.val ∈ quotientHom.ker
      rw [quotientHom_ker]
      exact g.property
    rw [sextetQuotient_kernel] at hg
    obtain ⟨t, ht⟩ := hg
    refine ⟨t, Subtype.ext ?_⟩
    change sextetEquiv.symm (sextetTranslation t) = g.val
    rw [ht, sextetEquiv.symm_apply_apply]

def translationEquiv : Multiplicative hexacode ≃* Kernel :=
  MulEquiv.ofBijective translation translation_bijective

/-- The same translation coordinates with the core included in native M24. -/
def ambientTranslationEquiv : Multiplicative hexacode ≃* core :=
  translationEquiv.trans (Kernel.equivMapOfInjective Stabilizer.subtype
    Stabilizer.subtype_injective)

private theorem affine_conjugation (x : SextetAffineGroup) (t : Multiplicative hexacode) :
    x * SemidirectProduct.inl t * x⁻¹ =
      SemidirectProduct.inl (hexAffineAction x.right t) := by
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  rw [mul_inv_rev]
  have he := SemidirectProduct.inl_aut (φ := hexAffineAction) x.right t
  rw [map_inv] at he
  calc
    _ = SemidirectProduct.inl x.left *
        (SemidirectProduct.inr x.right * SemidirectProduct.inl t *
          (SemidirectProduct.inr x.right)⁻¹) * (SemidirectProduct.inl x.left)⁻¹ := by
      group
    _ = SemidirectProduct.inl x.left * SemidirectProduct.inl (hexAffineAction x.right t) *
        (SemidirectProduct.inl x.left)⁻¹ := by rw [← he]
    _ = _ := by rw [← map_inv, ← map_mul, ← map_mul]; congr 1; simp [mul_comm, mul_left_comm]

theorem translationEquiv_conjugation (g : Stabilizer) (t : Multiplicative hexacode) :
    g * (translationEquiv t).val * g⁻¹ =
      (translationEquiv (hexAffineAction (quotientHom g) t)).val := by
  apply sextetEquiv.injective
  simp only [map_mul, map_inv]
  change sextetEquiv g * sextetEquiv (sextetEquiv.symm (sextetTranslation t)) *
    (sextetEquiv g)⁻¹ =
    sextetEquiv (sextetEquiv.symm (sextetTranslation (hexAffineAction (quotientHom g) t)))
  simp only [sextetEquiv.apply_symm_apply]
  have h := congrArg sextetAffineEquiv
    (affine_conjugation (sextetAffineEquiv.symm (sextetEquiv g)) t)
  simp only [map_mul, map_inv, sextetAffineEquiv.apply_symm_apply] at h
  exact h

/-- The binary natural action is the actual conjugation action on the native core. -/
theorem natural_action (g : Stabilizer) (v : hexacode) :
    g * (translationEquiv (Multiplicative.ofAdd v)).val * g⁻¹ =
      (translationEquiv (Multiplicative.ofAdd (action (quotientHom g) v))).val :=
  translationEquiv_conjugation g _

theorem ambientTranslationEquiv_conjugation (g : Stabilizer)
    (v : hexacode) :
    g.val * (ambientTranslationEquiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (ambientTranslationEquiv
        (Multiplicative.ofAdd (action (quotientHom g) v))).val :=
  congrArg Subtype.val (natural_action g v)

theorem residual_sign (g : Subgroup.solvableResidual Stabilizer) :
    hexSign (quotientHom g.val) = 1 := by
  let f := hexSign.comp quotientHom
  have h := Subgroup.map_solvableResidual_le f
  rw [Subgroup.solvableResidual_eq_bot (G := ℤˣ)] at h
  exact Subgroup.mem_bot.mp (h ⟨g.val, g.property, rfl⟩)

/-- In these coordinates the terminal derived subgroup acts linearly over F4. -/
theorem residual_field_linear (g : Subgroup.solvableResidual Stabilizer)
    (r : F) (v : hexacode) :
    action (quotientHom g.val) (r • v) = r • action (quotientHom g.val) v :=
  action_even_smul _ (residual_sign g) r v

end
end Sporadic.Mathieu.M24ChapterHStabilizers.SextetAction
