module
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetComplement.AtlasSection
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Quotient
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.SextetSeed
public import Theory.Representation.MathieuCodeRestriction.AtlasComparison
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transporting the affine scalar complement to native M24

Given a group equivalence with the actual Golay coordinate action, the ATLAS
scalar becomes a native cubic with six fixed points. The section has order
2160 and normalizes this cubic. The previously proved native normalizer order
therefore identifies the section with the full normalizer.

The final conditional theorem transports the intersection and generation
identities to the intrinsic two-core of the native standard-sextet stabilizer.
Its explicit comparison and two-core premises are supplied by the independent
native sextet-core calculation; this module alone does not discharge them.

Source: Aschbacher–Smith H.15.7(1), printed pp.401–402. The underlying affine
model is the licensed ATLAS construction cited in `AtlasSection`.
-/

@[expose] public section
namespace MathieuCode.SixPoint.SextetComplement
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise
noncomputable section

variable (e : M24 ≃* Atlas.Codes.Mathieu24CodeModel)
variable (hc : ∀ g : M24, (e g).val = atlasPointEquiv.symm.permCongr g.val)

def nativeScalar : M24 := e.symm scalar

def nativeScalarGroup : Subgroup M24 := Subgroup.zpowers (nativeScalar e)

def nativeSection : Subgroup M24 := sectionGroup.map e.symm.toMonoidHom

include hc in
theorem nativeScalar_coordinates (p : Atlas.Codes.Omega) :
    (nativeScalar e).val (atlasPointEquiv p) = atlasPointEquiv (scalar.val p) := by
  have h := congrArg (fun g : Atlas.Codes.Mathieu24CodeModel => g.val p)
    (e.apply_symm_apply scalar)
  rw [hc] at h
  exact (atlasPointEquiv.symm_apply_eq).mp h

theorem nativeScalarGroup_card : Nat.card (nativeScalarGroup e) = 3 := by
  rw [nativeScalarGroup, Nat.card_zpowers, nativeScalar, MulEquiv.orderOf_eq, scalar_order]

include hc in
theorem nativeScalarGroup_fixed_card : Nat.card (FixedPoint (nativeScalarGroup e)) = 6 := by
  let f : {p : Atlas.Codes.Omega // scalar.val p = p} ≃ FixedPoint (nativeScalarGroup e) :=
    atlasPointEquiv.subtypeEquiv (by
      intro p
      rw [nativeScalarGroup, mem_fixedPoint_zpowers_iff]
      change scalar.val p = p ↔ (nativeScalar e).val (atlasPointEquiv p) = atlasPointEquiv p
      rw [nativeScalar_coordinates e hc, atlasPointEquiv.injective.eq_iff])
  exact (Nat.card_congr f).symm.trans scalar_fixed_card

theorem nativeScalarGroup_eq_map : nativeScalarGroup e = scalarGroup.map e.symm.toMonoidHom := by
  rw [scalarGroup, MonoidHom.map_zpowers]
  rfl

include hc in
theorem nativeSection_eq_normalizer :
    nativeSection e = Subgroup.normalizer (nativeScalarGroup e : Set M24) := by
  have hn : nativeSection e ≤ Subgroup.normalizer (nativeScalarGroup e : Set M24) := by
    rw [nativeScalarGroup_eq_map, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono section_normalizes_scalar
  apply Subgroup.eq_of_le_of_card_ge hn
  rw [normalizer_card _ (nativeScalarGroup_card e) (nativeScalarGroup_fixed_card e hc),
    nativeSection, Subgroup.card_map_of_injective e.symm.injective, section_card]

include hc in
theorem standard_complement_of_comparison
    (hs : Atlas.Codes.sextetStabilizer.map e.symm.toMonoidHom = sextetStabilizer standardSextet)
    (hk : Atlas.Codes.sextetStabilizer.pCoreIn 2 = translationGroup) :
    let N := Subgroup.normalizer (nativeScalarGroup e : Set M24)
    let H := sextetStabilizer standardSextet
    let K := (pCore 2 H).map H.subtype
    N ≤ H ∧ K ⊓ N = ⊥ ∧ K ⊔ N = H := by
  dsimp only
  rw [← nativeSection_eq_normalizer e hc]
  have hK : (sextetStabilizer standardSextet).pCoreIn 2 =
      translationGroup.map e.symm.toMonoidHom := by
    rw [← hs, ← Subgroup.map_pCoreIn_of_injective 2 _ _ e.symm.injective, hk]
  change nativeSection e ≤ sextetStabilizer standardSextet ∧
    (sextetStabilizer standardSextet).pCoreIn 2 ⊓ nativeSection e = ⊥ ∧
    (sextetStabilizer standardSextet).pCoreIn 2 ⊔ nativeSection e = sextetStabilizer standardSextet
  rw [hK, nativeSection, ← Subgroup.map_inf _ _ _ e.symm.injective,
    translationGroup_inf_section, Subgroup.map_bot, ← Subgroup.map_sup,
    translationGroup_sup_section, hs]
  exact ⟨hs ▸ Subgroup.map_mono section_le_stabilizer, rfl, rfl⟩

end
end MathieuCode.SixPoint.SextetComplement
