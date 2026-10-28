module

public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Cores
public import Theory.Mathieu.M24.ChapterHStabilizers.SextetAction
public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodeZeroCoordinate

/-!
# Native quintet quotient and coordinate-zero translations

The literal quintet stabilizer is the preimage of the standard sextet
stabilizer under `MathieuCode.pointEmbedding`. The established coordinate
bijection sends the zero row of the first hexacode coordinate to native
point zero. An affine sextet element fixes this point precisely when its
linear part fixes that coordinate and its translation vanishes there.
Consequently the native quintet quotient is the hexacode coordinate
stabilizer, and its intrinsic two-core is the coordinate-zero translation
space. Conjugation agrees with `hexZeroLinear` through this same quotient.

The core identification reuses `CommonFour.sextet_core_comap` and
`CommonFour.quintet_core_eq`; no new elementary-subgroup classification is
needed. The ambient equivalence lands in `(pCore 2 Q).map Q.subtype`, the
literal kernel used by the Chapter H consumer. The independent recognition
of the hexacode action as the natural ΓL₂(4) action completes H.14.2(2).

Source: Aschbacher–Smith, H.14.2(2), printed p.397 of the combined
1 March 2004 manuscript, deduced there from H.14.1(2). The affine and
coordinate-zero constructions reuse the ATLAS ports of Gerald Höhn and
ATLAS contributors, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
under the ATLAS Research and Attribution License 1.0; see `LICENSES/ATLAS.txt`.
No new port is used here.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open Sporadic.Mathieu.M23Geometry
namespace Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.QuintetHexacode
noncomputable section

/-- The literal native quintet stabilizer. -/
abbrev Q := CommonFour.quintetStabilizer
/-- The ambient standard sextet stabilizer. -/
abbrev S := M24LocalGeometry.sextetStabilizer standardSextet
/-- The hexacode coordinate containing native point zero. -/
abbrev i0 : HexIndex := firstThree 0

/-- The restriction of the actual native point embedding. -/
def toSextet : Q →* S :=
  (pointEmbedding.comp Q.subtype).codRestrict _ (fun g => g.property)

/-- The inclusion is literally the native point embedding on underlying elements. -/
theorem toSextet_coe (g : Q) : (toSextet g).val = pointEmbedding g.val := by rfl

/-- Faithfulness is inherited from the native point embedding. -/
theorem toSextet_injective : Function.Injective toSextet := by
  intro g h he
  exact Subtype.ext (pointEmbedding_injective (congrArg Subtype.val he))

/-- The quintet image is exactly the point-zero stabilizer in the sextet group. -/
theorem toSextet_range (s : S) :
    s ∈ toSextet.range ↔ s.val.val 0 = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact pointEmbedding_fixed g.val
  · intro hs
    have hm : s.val ∈ pointEmbedding.range := by
      rw [pointEmbedding_range]
      exact hs
    obtain ⟨g, hg⟩ := hm
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change pointEmbedding g ∈ M24LocalGeometry.sextetStabilizer standardSextet
    rw [hg]
    exact s.property

/-- The zero row corresponds to the actual deleted native point. -/
@[simp] theorem atlasPointEquiv_zero : atlasPointEquiv (i0, 0) = 0 := by
  decide +kernel

/-- The affine model transported through the established native coordinate bijection. -/
def nativeAffineEquiv : SextetAffineGroup ≃* S :=
  sextetAffineEquiv.trans SextetCore.sextetEquiv.symm

/-- The affine equivalence retains the literal native point coordinates. -/
theorem nativeAffineEquiv_points (x : SextetAffineGroup) (p : Omega) :
    (nativeAffineEquiv x).val.val (atlasPointEquiv p) =
      atlasPointEquiv ((sextetAffineEquiv x).val.val p) := by
  have h := congrArg (fun g : SextetStabilizer => g.val.val p)
    (SextetCore.sextetEquiv.apply_symm_apply (sextetAffineEquiv x))
  change atlasPointEquiv.symm
    ((nativeAffineEquiv x).val.val (atlasPointEquiv p)) = _ at h
  exact (atlasPointEquiv.symm_apply_eq).mp h

/-- Fixing native point zero is exactly the coordinate-stabilizer and zero-translation condition. -/
theorem nativeAffineEquiv_fixed_zero_iff (x : SextetAffineGroup) :
    (nativeAffineEquiv x).val.val 0 = 0 ↔
      x.right.val.perm i0 = i0 ∧ x.left.toAdd.val i0 = 0 := by
  rw [← atlasPointEquiv_zero, nativeAffineEquiv_points,
    atlasPointEquiv.injective.eq_iff]
  constructor
  · intro hx
    have hp : x.right.val.perm i0 = i0 := congrArg Prod.fst hx
    have ht := congrArg (fun p : Omega => rowLabel p.2) hx
    rw [sextetAffineEquiv_coordinates, hp] at ht
    have h0 : rowLabel 0 = 0 := rfl
    simp only [h0, map_zero, zero_add, rowLabel.apply_symm_apply] at ht
    exact ⟨hp, ht⟩
  · rintro ⟨hp, ht⟩
    rw [sextetAffineEquiv_coordinates, hp]
    have h0 : rowLabel 0 = 0 := rfl
    simp only [h0, map_zero, zero_add, ht]
    rfl

/-- The native affine quotient is the linear part of the same affine element. -/
theorem nativeAffineEquiv_quotient (x : SextetAffineGroup) :
    SextetCore.quotientHom (nativeAffineEquiv x) = x.right := by
  change sextetQuotient
    (SextetCore.sextetEquiv (SextetCore.sextetEquiv.symm (sextetAffineEquiv x))) = _
  rw [SextetCore.sextetEquiv.apply_symm_apply, sextetQuotient_affine]

/-- The restricted sextet two-core is the intrinsic quintet two-core. -/
theorem core_comap : (pCore 2 S).comap toSextet = pCore 2 Q := by
  have he := CommonFour.sextet_core_comap.trans CommonFour.quintet_core_eq.symm
  ext g
  constructor
  · intro hg
    have hm : g.val ∈ SextetCore.core.comap pointEmbedding :=
      ⟨toSextet g, hg, rfl⟩
    rw [he] at hm
    obtain ⟨k, hk, hkg⟩ := hm
    exact (Subtype.ext hkg : k = g) ▸ hk
  · intro hg
    have hm : g.val ∈ (pCore 2 Q).map Q.subtype := ⟨g, hg, rfl⟩
    rw [← he] at hm
    obtain ⟨k, hk, hkg⟩ := hm
    change toSextet g ∈ pCore 2 S
    exact (Subtype.ext hkg : k = toSextet g) ▸ hk

/-- The actual sextet quotient restricted to the native quintet stabilizer. -/
def quotientHom : Q →* hexPointStabilizer i0 :=
  (SextetCore.quotientHom.comp toSextet).codRestrict _ (by
    intro g
    let x := nativeAffineEquiv.symm (toSextet g)
    have hx : nativeAffineEquiv x = toSextet g := nativeAffineEquiv.apply_symm_apply _
    have hf : (nativeAffineEquiv x).val.val 0 = 0 := by
      rw [hx]
      exact pointEmbedding_fixed g.val
    have hp := (nativeAffineEquiv_fixed_zero_iff x).mp hf
    change (SextetCore.quotientHom (toSextet g)).val.perm i0 = i0
    rw [← hx, nativeAffineEquiv_quotient]
    exact hp.1)

/-- Every hexacode coordinate stabilizer element lifts with zero translation. -/
theorem quotientHom_surjective : Function.Surjective quotientHom := by
  intro h
  let x : SextetAffineGroup := SemidirectProduct.inr h.val
  have hf : (nativeAffineEquiv x).val.val 0 = 0 :=
    (nativeAffineEquiv_fixed_zero_iff x).mpr ⟨h.property, rfl⟩
  obtain ⟨g, hg⟩ := (toSextet_range (nativeAffineEquiv x)).mpr hf
  refine ⟨g, Subtype.ext ?_⟩
  change SextetCore.quotientHom (toSextet g) = h.val
  rw [hg, nativeAffineEquiv_quotient]
  rfl

/-- The restricted affine quotient has precisely the intrinsic two-core as kernel. -/
theorem quotientHom_ker : quotientHom.ker = pCore 2 Q := by
  rw [← core_comap, ← SextetCore.quotientHom_ker]
  ext g
  exact Subtype.ext_iff

/-- The intrinsic native quotient is the genuine hexacode coordinate stabilizer. -/
def quotientEquiv : (Q ⧸ pCore 2 Q) ≃* hexPointStabilizer i0 :=
  (QuotientGroup.quotientMulEquivOfEq quotientHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective quotientHom quotientHom_surjective)

/-- The quotient equivalence uses the original affine quotient on representatives. -/
@[simp] theorem quotientEquiv_mk (g : Q) :
    quotientEquiv (QuotientGroup.mk g) = quotientHom g := by rfl

/-- Compatibility with the original native sextet quotient. -/
theorem quotientHom_coe (g : Q) :
    (quotientHom g).val = SextetCore.quotientHom (toSextet g) := by rfl

/-- A native sextet translation fixes the deleted point precisely when its coordinate vanishes. -/
theorem sextetTranslation_fixed_zero_iff (w : Multiplicative hexacode) :
    (M24ChapterHStabilizers.SextetAction.translationEquiv w).val.val.val 0 = 0 ↔
      w.toAdd.val i0 = 0 := by
  change (nativeAffineEquiv (SemidirectProduct.inl w)).val.val 0 = 0 ↔ _
  rw [nativeAffineEquiv_fixed_zero_iff]
  exact and_iff_right rfl

private def translationToSextet : Multiplicative (hexZeroCoordinate i0) →* S :=
  (pCore 2 S).subtype.comp
    (M24ChapterHStabilizers.SextetAction.translationEquiv.toMonoidHom.comp
      (hexZeroInclusion i0))

private theorem translationToSextet_mem (w : Multiplicative (hexZeroCoordinate i0)) :
    translationToSextet w ∈ toSextet.range :=
  (toSextet_range _).mpr ((sextetTranslation_fixed_zero_iff _).mpr w.toAdd.property)

private def translationLift : Multiplicative (hexZeroCoordinate i0) →* Q :=
  (MonoidHom.ofInjective toSextet_injective).symm.toMonoidHom.comp
    (translationToSextet.codRestrict _ translationToSextet_mem)

private theorem toSextet_translationLift (w : Multiplicative (hexZeroCoordinate i0)) :
    toSextet (translationLift w) = translationToSextet w :=
  MonoidHom.apply_ofInjective_symm toSextet_injective _

/-- Coordinate-zero translations lifted through the native point embedding. -/
def translation : Multiplicative (hexZeroCoordinate i0) →* pCore 2 Q :=
  translationLift.codRestrict _ (by
    intro w
    rw [← core_comap]
    change toSextet (translationLift w) ∈ pCore 2 S
    rw [toSextet_translationLift]
    exact (M24ChapterHStabilizers.SextetAction.translationEquiv _).property)

/-- The lifted translation is the original sextet translation under the point embedding. -/
theorem translation_toSextet (w : Multiplicative (hexZeroCoordinate i0)) :
    toSextet (translation w).val =
      (M24ChapterHStabilizers.SextetAction.translationEquiv (hexZeroInclusion i0 w)).val :=
  toSextet_translationLift w

/-- All intrinsic quintet core elements arise uniquely as coordinate-zero translations. -/
theorem translation_bijective : Function.Bijective translation := by
  constructor
  · intro u v he
    have hs := congrArg (fun g : pCore 2 Q => toSextet g.val) he
    rw [translation_toSextet, translation_toSextet] at hs
    have hw := M24ChapterHStabilizers.SextetAction.translationEquiv.injective (Subtype.ext hs)
    exact congrArg Multiplicative.ofAdd (Subtype.ext (congrArg Multiplicative.toAdd hw))
  · intro g
    have hg : toSextet g.val ∈ pCore 2 S := by
      change g.val ∈ (pCore 2 S).comap toSextet
      rw [core_comap]
      exact g.property
    obtain ⟨w, hw⟩ := M24ChapterHStabilizers.SextetAction.translationEquiv.surjective
      ⟨toSextet g.val, hg⟩
    have hzero : w.toAdd.val i0 = 0 := by
      apply (sextetTranslation_fixed_zero_iff w).mp
      rw [hw]
      exact pointEmbedding_fixed g.val.val
    refine ⟨Multiplicative.ofAdd ⟨w.toAdd, hzero⟩, ?_⟩
    apply Subtype.ext
    apply toSextet_injective
    rw [translation_toSextet]
    exact congrArg Subtype.val hw

/-- Translation coordinates on the intrinsic quintet two-core. -/
def translationEquiv : Multiplicative (hexZeroCoordinate i0) ≃* pCore 2 Q :=
  MulEquiv.ofBijective translation translation_bijective

/-- The core isomorphism retains the original sextet translation coordinates. -/
theorem translationEquiv_toSextet (w : Multiplicative (hexZeroCoordinate i0)) :
    toSextet (translationEquiv w).val =
      (M24ChapterHStabilizers.SextetAction.translationEquiv (hexZeroInclusion i0 w)).val :=
  translation_toSextet w

/-- Full conjugation on the intrinsic core is the coordinate-zero hexacode action. -/
theorem translationEquiv_conjugation (g : Q) (v : hexZeroCoordinate i0) :
    g * (translationEquiv (Multiplicative.ofAdd v)).val * g⁻¹ =
      (translationEquiv (Multiplicative.ofAdd
        (hexZeroLinear i0 (quotientEquiv (QuotientGroup.mk g)) v))).val := by
  apply toSextet_injective
  simp only [map_mul, map_inv, translationEquiv_toSextet, quotientEquiv_mk]
  exact M24ChapterHStabilizers.SextetAction.translationEquiv_conjugation (toSextet g) _

/-- The same coordinates on the core included in native M23. -/
def ambientTranslationEquiv : Multiplicative (hexZeroCoordinate i0) ≃*
    (pCore 2 Q).map Q.subtype :=
  translationEquiv.trans ((pCore 2 Q).equivMapOfInjective Q.subtype Q.subtype_injective)

/-- The same action formula in the native ambient M23, for the literal source kernel. -/
theorem ambientTranslationEquiv_conjugation (g : Q) (v : hexZeroCoordinate i0) :
    g.val * (ambientTranslationEquiv (Multiplicative.ofAdd v)).val * g.val⁻¹ =
      (ambientTranslationEquiv (Multiplicative.ofAdd
        (hexZeroLinear i0 (quotientEquiv (QuotientGroup.mk g)) v))).val :=
  congrArg Subtype.val (translationEquiv_conjugation g v)

/-- The ambient core coordinates commute with the actual M23-to-M24 point embedding. -/
theorem ambientTranslationEquiv_pointEmbedding (w : Multiplicative (hexZeroCoordinate i0)) :
    pointEmbedding (ambientTranslationEquiv w).val =
      (M24ChapterHStabilizers.SextetAction.ambientTranslationEquiv
        (hexZeroInclusion i0 w)).val :=
  congrArg Subtype.val (translationEquiv_toSextet w)

/-- The ambient translations act on native points by the literal ATLAS row formula. -/
theorem ambientTranslationEquiv_points (w : Multiplicative (hexZeroCoordinate i0))
    (i : HexIndex) (k : Fin 4) :
    (pointEmbedding (ambientTranslationEquiv w).val).val (atlasPointEquiv (i, k)) =
      atlasPointEquiv (i, rowLabel.symm (rowLabel k + w.toAdd.val.val i)) := by
  rw [ambientTranslationEquiv_pointEmbedding]
  change (nativeAffineEquiv (SemidirectProduct.inl (hexZeroInclusion i0 w))).val.val
    (atlasPointEquiv (i, k)) = _
  rw [nativeAffineEquiv_points]
  rfl

end
end Sporadic.Mathieu.M23Geometry.ChapterHLocalActions.QuintetHexacode
