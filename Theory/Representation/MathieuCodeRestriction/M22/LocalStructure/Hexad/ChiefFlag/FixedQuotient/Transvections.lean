module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Inputs
public import Theory.Representation.CubicFixedSpace

/-!
# The full center-transvection input and the literal quotient fixed space

Faithfulness and the image of the actual kernel on V5 show that every
nonidentity element fixes a hyperplane of V5. The fixed space in V/V1 pulls
back to an invariant proper code subspace containing V5. Properness uses the
independent definition V5=[V,K] as the coinvariant kernel.

Source: Aschbacher--Smith, H.16.4(2),(5), printed p.403, 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag.FixedQuotientData
open Representation Representation.BinaryOffender
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- The literal center has dimension one. -/
theorem center_finrank (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2) center.toSubmodule = 1 := by
  have hl : V1 ≤ V5 := by
    change V1.toSubmodule ≤ V5.toSubmodule
    rw [codeCommutatorSubrepresentation_space]
    exact codeFixed_le_commutator h h24
  exact (sectionLowerEquiv codeAction hl).finrank_eq.trans
    (codeFixedSubrepresentation_finrank h)

theorem kernel_mem_radical (D : Actions E) (z : Kernel) :
    kernelAction z ∈ BinaryLinear.radical center.toSubmodule := by
  rw [← D.transvections_full]
  exact ⟨z, rfl⟩

/-- Every nonidentity kernel element has displacement one on V5; its fixed
space there consequently has dimension four. -/
theorem transvection_fixed_finrank (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (z : Kernel) (hz : z ≠ 1) :
    Module.finrank (ZMod 2) (fixedSpace V5.toRepresentation
      (Subgroup.zpowers (Subgroup.inclusion kernel_le_stabilizer z))) = 4 := by
  let a := Subgroup.inclusion kernel_le_stabilizer z
  let d := V5.toRepresentation a - LinearMap.id
  have hr : d.range ≤ center.toSubmodule := by
    rintro _ ⟨v, rfl⟩
    exact (kernel_mem_radical D z).2 v
  have hle := Submodule.finrank_mono hr
  rw [center_finrank h h24] at hle
  have hne : Module.finrank (ZMod 2) d.range ≠ 0 := by
    intro he
    have hd : d = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp he)
    have hk : kernelAction z = 1 := by
      apply LinearEquiv.ext
      intro v
      change V5.toRepresentation a v = v
      exact sub_eq_zero.mp (LinearMap.congr_fun hd v)
    exact hz (D.transvections_faithful (hk.trans (map_one kernelAction).symm))
  have hcodim : fixedCodim V5.toRepresentation (Subgroup.zpowers a) = 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    change Module.finrank (ZMod 2) d.range = 1
    omega
  have hf := fixedCodim_add_finrank V5.toRepresentation (Subgroup.zpowers a)
  have h5 := codeCommutatorSubrepresentation_finrank h h24
  change Module.finrank (ZMod 2) V5.toSubmodule = 5 at h5
  change Module.finrank (ZMod 2) (fixedSpace V5.toRepresentation (Subgroup.zpowers a)) = 4
  omega

/-- The full preimage of C_(V/V1)(K). -/
def fixedLift : Subrepresentation codeAction where
  toSubmodule := fixedCodeQuotient.comap V1.toSubmodule.mkQ
  apply_mem_toSubmodule g v hv := by
    let : (Kernel.subgroupOf Stabilizer).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer kernel_le_stabilizer).mpr
        stabilizer_le_normalizer
    change V1.quotientRepresentation g (V1.toSubmodule.mkQ v) ∈
      fixedSpace V1.quotientRepresentation (Kernel.subgroupOf Stabilizer)
    exact fixedSpace_apply_mem_of_normalizes _ _ g
      (by rw [Subgroup.normalizer_eq_top]; trivial) hv

/-- Membership records every actual displacement, relative to the stabilizer. -/
theorem mem_fixedLift (v : M22Code) :
    v ∈ fixedLift ↔ ∀ z : Kernel, m22OuterCodeRepresentation z.val v - v ∈ V1.toSubmodule := by
  change (∀ a : Kernel.subgroupOf Stabilizer,
    V1.quotientRepresentation a.val (V1.toSubmodule.mkQ v) = V1.toSubmodule.mkQ v) ↔ _
  constructor
  · intro hv z
    exact (Submodule.Quotient.eq V1.toSubmodule).mp
      (hv ⟨Subgroup.inclusion kernel_le_stabilizer z, z.property⟩)
  · intro hv a
    exact (Submodule.Quotient.eq V1.toSubmodule).mpr (hv ⟨a.val.val, a.property⟩)

theorem five_le_fixedLift (D : Actions E) : V5 ≤ fixedLift := by
  intro v hv
  apply (mem_fixedLift v).mpr
  intro z
  exact (kernel_mem_radical D z).2 (⟨v, hv⟩ : V5.toSubmodule)

/-- The pullback cannot be the whole code: otherwise every generating
commutator lies in V1, contradicting the independent dimensions one and five. -/
theorem fixedLift_ne_top
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    fixedLift ≠ ⊤ := by
  intro ht
  have hc : codeCommutator Kernel ≤ V1.toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨z, v⟩, rfl⟩
    exact (mem_fixedLift v).mp (ht ▸ (show v ∈ (⊤ : Subrepresentation codeAction) from trivial)) z
  have hd := Submodule.finrank_mono hc
  have h1 := codeFixedSubrepresentation_finrank h
  have h5 := codeCommutatorSubrepresentation_finrank h h24
  rw [codeCommutatorSubrepresentation_space] at h5
  change Module.finrank (ZMod 2) V1.toSubmodule = 1 at h1
  omega

end MathieuCode.Hexad.ChiefFlag.FixedQuotientData
