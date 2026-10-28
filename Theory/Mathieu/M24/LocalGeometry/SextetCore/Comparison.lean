module
public import Theory.Representation.MathieuCodeRestriction.AtlasComparison
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M24.LocalGeometry.Seed

/-!
# Native coordinates for the hexacode sextet stabilizer

The established linear Golay-code comparison conjugates each native design
permutation into the ATLAS code automorphism group. Faithfulness and the two
independently proved group orders make this coordinate homomorphism bijective.
The coordinate table maps the distinguished six tetrads to the literal parts
of `standardSextet`, so restriction identifies the actual stabilizers.

This reuses the ATLAS construction of Gerald Höhn and ATLAS contributors,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, under the ATLAS Research
and Attribution License 1.0; see `LICENSES/ATLAS.txt`. The native coordinate
comparison is in `MathieuCodeRestriction.AtlasComparison`. Source context:
Aschbacher–Smith H.14.1(2), printed pp.396–397.
-/

@[expose] public section
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.SextetCore
open MathieuCode

private theorem native_code_iff (g : M24) (v : Full) :
    v ∈ golay ↔ fullRepresentation g v ∈ golay := by
  constructor
  · exact golay_invariant g
  · intro h
    have hi := golay_invariant g⁻¹ h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hi

/-- Coordinate conjugation of the native design group into the ATLAS Golay group. -/
noncomputable def toAtlas : M24 →* Atlas.Codes.Mathieu24CodeModel :=
  (atlasPointEquiv.symm.permCongrHom.toMonoidHom.comp M24.subtype).codRestrict _ (by
    intro g
    change Atlas.Codes.CodePreserving (atlasPointEquiv.symm.permCongr g.val)
    intro w
    rw [mem_atlas_golay_iff, mem_atlas_golay_iff, atlasWordEquiv_permute]
    exact native_code_iff g _)

theorem toAtlas_injective : Function.Injective toAtlas := by
  intro g h he
  apply Subtype.ext
  exact atlasPointEquiv.symm.permCongrHom.injective (congrArg Subtype.val he)

/-- Surjectivity uses the independently proved orders after constructing the faithful map. -/
theorem toAtlas_bijective : Function.Bijective toAtlas := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨toAtlas_injective, m24_order.trans Atlas.Codes.mathieu24_order.symm⟩

noncomputable def groupEquiv : M24 ≃* Atlas.Codes.Mathieu24CodeModel :=
  MulEquiv.ofBijective toAtlas toAtlas_bijective

theorem groupEquiv_apply (g : M24) :
    (groupEquiv g).val = atlasPointEquiv.symm.permCongr g.val := rfl

/-- Reindex a partition along the proved coordinate bijection. -/
noncomputable def nativeParts (S : Finset (Finset Atlas.Codes.Omega)) :
    Finset (Finset (Fin 24)) := S.image (fun A => A.image atlasPointEquiv)

theorem nativeParts_injective : Function.Injective nativeParts :=
  Finset.image_injective (Finset.image_injective atlasPointEquiv.injective)

theorem nativeParts_distinguished :
    nativeParts Atlas.Codes.distinguishedUnorderedSextet.val = standardSextet.parts := by
  decide +kernel

theorem nativeParts_equivariant (g : M24) (S : Finset (Finset Atlas.Codes.Omega)) :
    nativeParts (Atlas.Codes.permuteSextetParts (groupEquiv g).val S) =
      g • nativeParts S := by
  simp only [nativeParts, Atlas.Codes.permuteSextetParts,
    Finset.smul_finset_def, Finset.image_image]
  apply Finset.image_congr
  intro A _
  change (A.image (groupEquiv g).val).image atlasPointEquiv =
    (A.image atlasPointEquiv).image (g.val)
  simp only [Finset.image_image]
  apply Finset.image_congr
  intro a _
  change atlasPointEquiv (atlasPointEquiv.symm (g.val (atlasPointEquiv a))) = _
  exact atlasPointEquiv.apply_symm_apply _

theorem mem_sextet_iff (g : M24) :
    groupEquiv g ∈ Atlas.Codes.sextetStabilizer ↔
      g ∈ sextetStabilizer standardSextet := by
  rw [Atlas.Codes.sextetStabilizer_mem_iff]
  change Atlas.Codes.permuteSextetParts (groupEquiv g).val
    Atlas.Codes.distinguishedUnorderedSextet.val =
    Atlas.Codes.distinguishedUnorderedSextet.val ↔
      g • standardSextet.parts = standardSextet.parts
  rw [← nativeParts_injective.eq_iff, nativeParts_equivariant, nativeParts_distinguished]

noncomputable def sextetHom : sextetStabilizer standardSextet →* Atlas.Codes.SextetStabilizer :=
  (groupEquiv.toMonoidHom.comp (sextetStabilizer standardSextet).subtype).codRestrict _
    (fun g => (mem_sextet_iff g.val).mpr g.property)

theorem sextetHom_bijective : Function.Bijective sextetHom := by
  constructor
  · intro g h he
    apply Subtype.ext
    exact groupEquiv.injective (congrArg Subtype.val he)
  · intro g
    obtain ⟨h, hh⟩ := groupEquiv.surjective g.val
    refine ⟨⟨h, (mem_sextet_iff h).mp (hh ▸ g.property)⟩, ?_⟩
    exact Subtype.ext hh

/-- An equivalence of the literal sextet stabilizers, retaining the point coordinates. -/
noncomputable def sextetEquiv :
    sextetStabilizer standardSextet ≃* Atlas.Codes.SextetStabilizer :=
  MulEquiv.ofBijective sextetHom sextetHom_bijective

theorem sextetEquiv_apply (g : sextetStabilizer standardSextet) :
    (sextetEquiv g).val.val = atlasPointEquiv.symm.permCongr g.val.val := rfl

end Sporadic.Mathieu.M24LocalGeometry.SextetCore
