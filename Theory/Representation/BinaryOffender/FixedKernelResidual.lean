module
public import Theory.Representation.BinaryOffender.InvolutionFixedKernel
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.ElementaryAbelian.Basic

/-!
# Residuals fixing an involution-fixed support

The pointwise kernel of a subspace normalizes its intersection with any
normalized actor. On an invariant binary support, a group centralizing an
involution and fixing that involution's fixed space has elementary abelian
image. Its two-residual therefore fixes the whole support.

Application: the first decomposable support in Aschbacher--Smith 15.1.16(a),
printed p.1092. Normality and action maps are relative to the actual support.
-/

public section
open Subgroup Representation
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- Pointwise fixation preserves the kernel inside a normalized actor. -/
theorem pointwiseKernel_normalizes (ρ : Representation (ZMod 2) D V)
    (W : Submodule (ZMod 2) V) (A K : Subgroup D)
    (hn : K ≤ normalizer (A : Set D))
    (hk : K ≤ subspaceKernel ρ W ⊤) :
    K ≤ normalizer (subspaceKernel ρ W A : Set D) := by
  apply le_normalizer_iff.mpr
  intro k hkm a ha
  refine ⟨(mem_normalizer_iff.mp (hn hkm) a).mp ha.1,?_⟩
  intro w hw
  have hki := (hk (K.inv_mem hkm)).2 w hw
  change ρ (k * a * k⁻¹) w = w
  simp only [map_mul,Module.End.mul_apply,hki,ha.2 w hw,(hk hkm).2 w hw]

/-- The two-residual fixes the entire support once the action centralizes
the involution and fixes its fixed space pointwise. -/
theorem residual_fixes_support_of_involution_fixed
    (ρ : Representation (ZMod 2) D V) (U : Submodule (ZMod 2) V)
    (K : Subgroup D) (hKU : K ≤ subspaceStabilizer ρ U)
    (t : D) (htU : t ∈ subspaceStabilizer ρ U) (ht : t ^ 2 = 1)
    (hc : K ≤ centralizer ({t} : Set D))
    (hfix : ∀ k ∈ K, ∀ v ∈ U, ρ t v = v → ρ k v = v) :
    (pResidual 2 K).map K.subtype ≤ subspaceKernel ρ U ⊤ := by
  let σ := subspaceImageRepresentation ρ U
  let a := subspaceActionHom ρ U ⟨t,htU⟩
  have ha : a ^ 2 = 1 := by
    change (subspaceActionHom ρ U ⟨t,htU⟩) ^ 2 = 1
    rw [←map_pow]
    have he : (⟨t,htU⟩ : subspaceStabilizer ρ U) ^ 2 = 1 := Subtype.ext ht
    rw [he,map_one]
  let f := subgroupActionHom ρ U K hKU
  have hf : ∀ k : K, f k ∈ involutionFixedKernel σ a := by
    intro k
    constructor
    · apply mem_centralizer_singleton_iff.mpr
      apply (subspaceImageRepresentation_injective ρ U)
      ext v
      simp only [map_mul,Module.End.mul_apply]
      change ρ (k : D) (ρ t v) = ρ t (ρ (k : D) v)
      simp only [←Module.End.mul_apply,←map_mul]
      rw [mem_centralizer_singleton_iff.mp (hc k.property)]
    · intro v hv
      apply Subtype.ext
      apply hfix k k.property v v.property
      exact congrArg Subtype.val ((mem_fixedSpace_zpowers_iff σ a v).mp hv)
  let g := f.codRestrict (involutionFixedKernel σ a) hf
  let : IsElementaryAbelian 2 (involutionFixedKernel σ a) :=
    involutionFixedKernel_elementary σ (subspaceImageRepresentation_injective ρ U) a ha
  have hg : pResidual 2 K ≤ g.ker := pResidual_le_ker_of_isPGroup 2 g
    (IsElementaryAbelian.isPGroup 2 _)
  rintro _ ⟨k,hk,rfl⟩
  refine ⟨mem_top _,?_⟩
  intro v hv
  have he : f k = 1 := congrArg Subtype.val (hg hk)
  exact congrArg (fun b => (σ b ⟨v,hv⟩ : V)) he
end Representation.BinaryOffender
