module
public import Theory.Representation.CubicClifford.Extension
public import Theory.Representation.NormalPSubgroupKernel

/-!
# Surjective intertwiners across a two-group quotient

Let K be normal in H with H/K a two-group. If a binary H-module has a
nonzero K-map into an irreducible H-module, then it has a surjective H-map
onto that module. The quotient acts on the nonzero space of K-intertwiners
and fixes a nonzero vector; irreducibility makes the resulting map onto.
The map obtained need not restrict to the particular initial K-map.

This is the Clifford Hom-space argument used for original local-module
recognition in Aschbacher--Smith 10.2.9, printed pp.751--752.
-/

public noncomputable section
open Representation
namespace Representation
variable {H V E : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

/-- A nonzero intertwiner on a normal subgroup gives a surjective ambient
intertwiner into an irreducible binary module when the quotient is a two-group. -/
theorem exists_surjective_intertwiner_of_twoGroup_quotient
    (K : Subgroup H) [K.Normal] (hQ : IsPGroup 2 (H ⧸ K))
    (τ : Representation (ZMod 2) H E) (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ]
    (f : IntertwiningMap (τ.comp K.subtype) (ρ.comp K.subtype)) (hf : f ≠ 0) :
    ∃ i : τ.IntertwiningMap ρ, Function.Surjective i := by
  open CubicClifford in
  have hm : f.toLinearMap ∈ homSpace K τ ρ := by
    intro k
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun (f.isIntertwining' k) (τ (k:H)⁻¹ x)
    change f (τ k (τ (k:H)⁻¹ x)) = ρ k (f (τ (k:H)⁻¹ x)) at he
    change ρ (k:H) (f (τ (k:H)⁻¹ x)) = f x
    simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
      Module.End.one_apply] using he.symm
  let : Nontrivial (CubicClifford.homSpace K τ ρ) :=
    ⟨⟨⟨f.toLinearMap,hm⟩,0,fun he => hf (IntertwiningMap.ext (congrArg Subtype.val he))⟩⟩
  have hc : ringChar (ZMod 2) = 2 := ringChar.eq (ZMod 2) 2
  obtain ⟨u,hu,hfix⟩ := pGroup_fix_nonzero_vector (F := ZMod 2)
    (by rw [hc]; decide)
    (by simpa only [hc] using hQ)
    (CubicClifford.homQuotientRepresentation K τ ρ)
  let i : τ.IntertwiningMap ρ := ⟨u.val,fun h => by
    ext x
    have he := congrArg Subtype.val (hfix (QuotientGroup.mk' K h))
    have hh := LinearMap.congr_fun he (τ h x)
    change ρ h (u.val (τ h⁻¹ (τ h x))) = u.val (τ h x) at hh
    simpa only [LinearMap.comp_apply,←Module.End.mul_apply,←map_mul,
      inv_mul_cancel,map_one,Module.End.one_apply] using hh.symm⟩
  have hin : i ≠ 0 := by
    intro hz
    apply hu
    apply Subtype.ext
    exact congrArg IntertwiningMap.toLinearMap hz
  exact ⟨i,(IsIrreducible.surjective_or_eq_zero i).resolve_right hin⟩
end Representation
