module
public import Theory.Representation.BinaryOffender.Homogeneous.ActiveFactorTwist
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Inner quotient actions preserve homogeneous seeds

Normal two-subgroups act trivially on irreducible binary modules. An inner
action on the two-core quotient therefore has an explicit linear intertwiner.
For a seed with one active factor, only the twist of the specified normalizer
element is needed: its extension to the factor join identifies the conjugate
central image, and homogeneity recovers equality of the original seeds.

The constrained four-natural point orbit uses these results without assuming
invariance under every automorphism of the component.
Source: Aschbacher--Smith A.1.40--42 and D.3.6, pp.31--32 and196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender.Homogeneous
universe u

/-- An inner automorphism on the two-core quotient preserves every irreducible binary module. -/
theorem irreducible_twist_of_inner_twoCore
    {A V : Type*} [Group A] [Finite A] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) A V) [σ.IsIrreducible]
    (a : MulAut A) (h : quotientAut (pCore 2 A) a ∈ MulAut.innerSubgroup (A ⧸ pCore 2 A)) :
    ∃ c : V ≃ₗ[ZMod 2] V, ∀ g v, c (σ g v) = σ (a g) (c v) := by
  have hk := normal_p_subgroup_le_ker σ (pCore 2 A) pCore_isPGroup
  let τ := quotientOfLEKer σ (pCore 2 A) hk
  obtain ⟨x,hx⟩ := h
  let c := LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom x)
  refine ⟨c,?_⟩
  intro g v
  have he := DFunLike.congr_fun hx (QuotientGroup.mk' (pCore 2 A) g)
  rw [quotientAut_apply_mk] at he
  change x * QuotientGroup.mk' (pCore 2 A) g * x⁻¹ = QuotientGroup.mk' (pCore 2 A) (a g) at he
  change τ x (τ (QuotientGroup.mk' (pCore 2 A) g) v) =
    τ (QuotientGroup.mk' (pCore 2 A) (a g)) (τ x v)
  rw [←he,←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
  congr 2
  group

variable {G : Type*} {V : Type u} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A twist for the specified normalizing element suffices to fix the original homogeneous seed. -/
theorem IsIrrPlusWith.map_eq_of_active_factor_twist_at
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I) (t : T)
    (A B : Subgroup G) (hAB : A ⊔ B = X)
    (hB : I ≤ fixedSpace ρ B)
    (htA : t.val ∈ normalizer (A : Set G))
    (htB : t.val ∈ normalizer (B : Set G))
    (htwist : ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) A W)
      [σ.IsIrreducible],
        ∃ c : W ≃ₗ[ZMod 2] W, ∀ g v, c (σ g v) =
          σ (A.normalizerMonoidHom
            ⟨t.val⁻¹, (normalizer (A : Set G)).inv_mem htA⟩ g) (c v)) :
    I.map (ρ t.val) = I := by
  have hAX : A ≤ X := hAB ▸ le_sup_left
  have hBX : B ≤ X := hAB ▸ le_sup_right
  let S := quotientImage ρ X I hI.invariant
  let σ := S.toRepresentation
  let : σ.IsIrreducible := quotientImage_irreducible ρ hI.isIrrPlus
  have hBfix (b : B) (v : S.toSubmodule) : σ ⟨b.val, hBX b.property⟩ v = v := by
    apply Subtype.ext
    obtain ⟨w, hw, he⟩ := v.property
    change fixedQuotientRepresentation ρ X ⟨b.val, hBX b.property⟩ v.val = v.val
    rw [←he]
    change (fixedSpace ρ X).mkQ (ρ b.val w) = (fixedSpace ρ X).mkQ w
    have hbfix : ρ (b : G) w = w := hB hw b
    rw [hbfix]
  have hker : B.subgroupOf X ≤ σ.ker := by
    intro b hb
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    exact hBfix ⟨b.val, hb⟩
  have hgen : A.subgroupOf X ⊔ B.subgroupOf X = ⊤ := by
    rw [←subgroupOf_sup hAX hBX, hAB, subgroupOf_self]
  let τ : Representation (ZMod 2) A S.toSubmodule := σ.comp (inclusion hAX)
  let e := subgroupOfEquivOfLe hAX
  let : IsIrreducible (σ.comp (A.subgroupOf X).subtype) :=
    irreducible_restrict_of_sup_kernel σ _ _ hgen hker
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (σ.comp (A.subgroupOf X).subtype)).mpr inferInstance
  let n := X.normalizerMonoidHom
    ⟨t.val⁻¹, hI.normalizes (T.inv_mem t.property)⟩
  let a := A.normalizerMonoidHom ⟨t.val⁻¹, (normalizer (A : Set G)).inv_mem htA⟩
  obtain ⟨c, hc⟩ := htwist τ
  let E := ((c.conjRingEquiv.toMonoidHom).comp σ).eqLocus (σ.comp n.toMonoidHom)
  have hAE : A.subgroupOf X ≤ E := by
    intro x hx
    apply LinearMap.ext
    intro v
    change c (τ ⟨x.val, hx⟩ (c.symm v)) = σ (n x) v
    rw [hc, c.apply_symm_apply]
    rfl
  have hBE : B.subgroupOf X ≤ E := by
    intro x hx
    apply LinearMap.ext
    intro v
    change c (σ x (c.symm v)) = σ (n x) v
    have hnx : (n x).val ∈ B := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (mem_normalizer_iff.mp ((normalizer (B : Set G)).inv_mem htB) x.val).mp hx
    rw [hBfix ⟨x.val, hx⟩, hBfix ⟨(n x).val, hnx⟩, c.apply_symm_apply]
  have hE : (⊤ : Subgroup X) ≤ E := hgen ▸ sup_le hAE hBE
  apply hI.map_eq_of_central_twist ρ t c
  intro x v
  have he := LinearMap.congr_fun (hE (mem_top x)) (c v)
  change c (σ x (c.symm (c v))) = σ (n x) (c v) at he
  simpa only [c.symm_apply_apply] using he

end Representation.BinaryOffender.Homogeneous
