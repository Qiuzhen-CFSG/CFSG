module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Quotient
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetSeed
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetComplement.NativeTransport
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetComplement.Geometry
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Hexacode

/-!
# Representative sextet complement: assembly from the native comparison

The concrete ATLAS section normalizes a cubic fixing six points. Its order
2160 equals the previously proved native normalizer order, so transport
identifies the whole normalizer with this section. The affine translation
complement identities and cubic conjugacy then produce a genuine native
sextet, with an actual native conjugator back to the standard sextet.

The native sextet-core development supplies the coordinate group isomorphism,
its stabilizer compatibility, and the intrinsic two-core identity. Thus
`cubicNormalizer_sextet_complement` proves the unconditional representative
geometry in Aschbacher–Smith H.15.7(1), printed pp.401–402. The variant
`cubicNormalizer_sextet_complement_normal` records normality inside the
sextet stabilizer. The original conditional assembly remains available.
-/

@[expose] public section

namespace MathieuCode.SixPoint
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise

/-- Conditional assembly; the native sextet-core calculation supplies all comparison inputs. -/
theorem cubicNormalizer_sextet_complement_of_atlas
    (e : M24 ≃* Atlas.Codes.Mathieu24CodeModel)
    (hc : ∀ g : M24, (e g).val = atlasPointEquiv.symm.permCongr g.val)
    (hs : Atlas.Codes.sextetStabilizer.map e.symm.toMonoidHom = sextetStabilizer standardSextet)
    (hk : Atlas.Codes.sextetStabilizer.pCoreIn 2 = SextetComplement.translationGroup) :
    ∃ S : Sextet,
      let N := Subgroup.normalizer (cubicSubgroup : Set M24)
      let H := sextetStabilizer S
      let K := (pCore 2 H).map H.subtype
      N ≤ H ∧ K ⊓ N = ⊥ ∧ K ⊔ N = H ∧
        ∃ g : M24, g.val • S.parts = standardSextet.parts := by
  obtain ⟨hN, hi, hs⟩ := SextetComplement.standard_complement_of_comparison e hc hs hk
  exact SextetComplement.representative_complement_of_standard
    (SextetComplement.nativeScalarGroup e)
    (SextetComplement.nativeScalarGroup_card e)
    (SextetComplement.nativeScalarGroup_fixed_card e hc) hN hi hs

/-- The native cubic normalizer complements the intrinsic two-core of a genuine sextet
stabilizer, and that sextet is conjugate to the standard sextet in native M24. -/
theorem cubicNormalizer_sextet_complement :
    ∃ S : Sextet,
      let N := Subgroup.normalizer (cubicSubgroup : Set M24)
      let H := sextetStabilizer S
      let K := (pCore 2 H).map H.subtype
      N ≤ H ∧ K ⊓ N = ⊥ ∧ K ⊔ N = H ∧
        ∃ g : M24, g.val • S.parts = standardSextet.parts := by
  have hs : Atlas.Codes.sextetStabilizer.map SextetCore.groupEquiv.symm.toMonoidHom =
      sextetStabilizer standardSextet :=
    (Subgroup.map_equiv_eq_comap_symm' SextetCore.groupEquiv.symm _).trans
      (Subgroup.ext SextetCore.mem_sextet_iff)
  have hk : Atlas.Codes.sextetStabilizer.pCoreIn 2 = SextetComplement.translationGroup := by
    change (pCore 2 Atlas.Codes.SextetStabilizer).map Atlas.Codes.sextetStabilizer.subtype = _
    rw [SextetCore.atlas_core_eq_kernel, Atlas.Codes.sextetQuotient_kernel]
    rfl
  exact cubicNormalizer_sextet_complement_of_atlas SextetCore.groupEquiv
    SextetCore.groupEquiv_apply hs hk

/-- The complement statement with normality explicitly relative to its sextet stabilizer. -/
theorem cubicNormalizer_sextet_complement_normal :
    ∃ S : Sextet,
      let N := Subgroup.normalizer (cubicSubgroup : Set M24)
      let H := sextetStabilizer S
      let K := (pCore 2 H).map H.subtype
      N ≤ H ∧ (K.subgroupOf H).Normal ∧ K ⊓ N = ⊥ ∧ K ⊔ N = H ∧
        ∃ g : M24, g.val • S.parts = standardSextet.parts := by
  obtain ⟨S, hN, hi, hs, hg⟩ := cubicNormalizer_sextet_complement
  refine ⟨S, hN, ?_, hi, hs, hg⟩
  change (((pCore 2 (sextetStabilizer S)).map (sextetStabilizer S).subtype).comap
    (sextetStabilizer S).subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective (sextetStabilizer S).subtype_injective]
  infer_instance

end MathieuCode.SixPoint
