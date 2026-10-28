module
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetSplitExtension

/-!
# The six-fixed-point scalar and its affine complement

The splitting section in the concrete ATLAS sextet stabilizer has order 2160.
It normalizes the scalar cubic because that cubic is the kernel of the hexacode
coordinate action. The scalar fixes exactly the zero-labelled point of each
of the six tetrads. The semidirect-product decomposition proves that the
section and translations have trivial intersection and generate the stabilizer.

These are the affine inputs to Aschbacher–Smith H.15.7(1), printed pp.401–402.
The native coordinate comparison and intrinsic two-core identification are
separate inputs to the transport module, not asserted by these calculations.
The imported ATLAS constructions are due to Gerald Höhn and ATLAS contributors,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research
and Attribution License 1.0; see `LICENSES/ATLAS.txt`.
-/

@[expose] public section
namespace MathieuCode.SixPoint.SextetComplement
open Atlas.Codes
noncomputable section

def sectionHom : HexAutomorphisms →* Mathieu24CodeModel :=
  Atlas.Codes.sextetStabilizer.subtype.comp sextetSection

def sectionGroup : Subgroup Mathieu24CodeModel := sectionHom.range

def scalar : Mathieu24CodeModel := sectionHom hexZ

def scalarGroup : Subgroup Mathieu24CodeModel := Subgroup.zpowers scalar

theorem section_injective : Function.Injective sectionHom := by
  intro a b h
  simpa only [sextetQuotient_section] using congrArg sextetQuotient (Subtype.ext h)

theorem section_card : Nat.card sectionGroup = 2160 := by
  exact (Nat.card_congr (Equiv.ofInjective sectionHom section_injective)).symm.trans
    hexAutomorphisms_card

theorem scalar_order : orderOf scalar = 3 := by
  rw [scalar, orderOf_injective sectionHom section_injective, hexZ_order]

theorem scalar_card : Nat.card scalarGroup = 3 := by
  rw [scalarGroup, Nat.card_zpowers, scalar_order]

theorem section_normalizes_scalar :
    sectionGroup ≤ Subgroup.normalizer (scalarGroup : Set Mathieu24CodeModel) := by
  have h := hexCoordinateSixHom.ker.le_normalizer_map sectionHom
  rw [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, hexCoordinateSix_kernel,
    MonoidHom.map_zpowers] at h
  exact h

theorem section_le_stabilizer : sectionGroup ≤ Atlas.Codes.sextetStabilizer := by
  rintro _ ⟨g, rfl⟩
  exact (sextetSection g).property

theorem scalar_fixed_iff (p : Omega) : scalar.val p = p ↔ p.2 = 0 := by
  revert p
  decide +kernel

theorem scalar_fixed_card : Nat.card {p : Omega // scalar.val p = p} = 6 := by
  let e : {p : Omega // scalar.val p = p} ≃ {p : Omega // p.2 = 0} :=
    Equiv.subtypeEquivRight scalar_fixed_iff
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide +kernel

theorem translation_inf_section : sextetTranslation.range ⊓ sextetSection.range = ⊥ := by
  apply bot_unique
  rintro s ⟨⟨t, ht⟩, g, hg⟩
  have hz : g = 1 := by
    have h := congrArg sextetQuotient (hg.trans ht.symm)
    simpa only [sextetQuotient_section, sextetQuotient_translation] using h
  rw [Subgroup.mem_bot, ← hg, hz, map_one]

theorem translation_sup_section : sextetTranslation.range ⊔ sextetSection.range = ⊤ := by
  apply top_unique
  intro s _
  let x := sextetAffineEquiv.symm s
  have he : sextetTranslation x.left * sextetSection x.right = s := by
    change sextetAffineEquiv (SemidirectProduct.inl x.left) *
      sextetAffineEquiv (SemidirectProduct.inr x.right) = s
    rw [← map_mul, SemidirectProduct.inl_left_mul_inr_right,
      sextetAffineEquiv.apply_symm_apply]
  rw [← he]
  exact (sextetTranslation.range ⊔ sextetSection.range).mul_mem
    (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

/-- The translations viewed in the full coordinate group. -/
def translationGroup : Subgroup Mathieu24CodeModel :=
  sextetTranslation.range.map Atlas.Codes.sextetStabilizer.subtype

theorem translationGroup_inf_section : translationGroup ⊓ sectionGroup = ⊥ := by
  rw [sectionGroup, sectionHom, MonoidHom.range_comp, translationGroup,
    ← Subgroup.map_inf _ _ _ Atlas.Codes.sextetStabilizer.subtype_injective,
    translation_inf_section, Subgroup.map_bot]

theorem translationGroup_sup_section :
    translationGroup ⊔ sectionGroup = Atlas.Codes.sextetStabilizer := by
  rw [sectionGroup, sectionHom, MonoidHom.range_comp, translationGroup,
    ← Subgroup.map_sup, translation_sup_section, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

end
end MathieuCode.SixPoint.SextetComplement
