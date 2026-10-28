module

public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Ambient involution rank bounds

An involution fixing the intersection of a subspace with its image has
ambient displacement rank at most the codimension of that subspace. The
proof applies rank-nullity to the subspace and to its sum with its image.
A second bound uses a fixed subspace in one of two complementary summands
and the square-zero displacement on the other summand in characteristic two.

These are ambient linear-algebra steps in the maximal-intersection route
for Aschbacher–Smith E.6.24, printed p.255. In particular they do not transfer
its strict involution bound to a quotient representation.
-/

public section

open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure.FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem rankNullity_on (N : W →ₗ[ZMod 2] W) (U : Submodule (ZMod 2) W) :
    finrank (ZMod 2) (U.map N) + finrank (ZMod 2) ↥(U ⊓ LinearMap.ker N) =
      finrank (ZMod 2) U := by
  have hr := (N.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hr
  rw [← U.map_comap_subtype N.ker, Submodule.finrank_map_subtype_eq]
  exact hr

/-- If an involution fixes the intersection of a space with its image,
its ambient displacement rank is at most that space's codimension. -/
theorem fixedCodim_le_of_fixes_intersection
    (ρ : Representation (ZMod 2) A W) (t : A) (ht : t ^ 2 = 1)
    (U : Submodule (ZMod 2) W)
    (hfix : ∀ v ∈ U ⊓ U.map (ρ t), ρ t v = v) :
    fixedCodim ρ (zpowers t) ≤ finrank (ZMod 2) W - finrank (ZMod 2) U := by
  let N := ρ t - LinearMap.id
  have htt (v : W) : ρ t (ρ t v) = v := by
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
      using congrArg (fun a => ρ a v) ht
  have hNt (v : W) : N (ρ t v) = -N v := by
    change ρ t (ρ t v) - ρ t v = -(ρ t v - v)
    rw [htt]
    abel
  have hmaps : (U ⊔ U.map (ρ t)).map N = U.map N := by
    rw [Submodule.map_sup]
    apply sup_eq_left.mpr
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    rw [hNt]
    exact (U.map N).neg_mem (Submodule.mem_map_of_mem hv)
  have hE : U ⊓ U.map (ρ t) ≤ U ⊓ N.ker := by
    intro v hv
    exact ⟨hv.1, sub_eq_zero.mpr (hfix v hv)⟩
  have hdim_image := (Submodule.equivMapOfInjective (ρ t) (show Function.Involutive (ρ t) from htt).injective U).finrank_eq
  have hdim_sum := U.finrank_sup_add_finrank_inf_eq (U.map (ρ t))
  have hrU := rankNullity_on N U
  have hrL := rankNullity_on N (U ⊔ U.map (ρ t))
  rw [hmaps] at hrL
  have hE' := Submodule.finrank_mono hE
  have hk := Submodule.finrank_mono
    (show (U ⊔ U.map (ρ t)) ⊓ N.ker ≤ N.ker from inf_le_right)
  have hr := N.finrank_range_add_finrank_ker
  rw [fixedCodim_zpowers_eq_displacement_rank]
  change finrank (ZMod 2) N.range ≤ _
  omega

/-- An involution preserving the two summands and fixing F has small ambient
rank when twice the remaining fixed dimension is at most the moved dimension. -/
theorem fixedCodim_le_of_split
    (ρ : Representation (ZMod 2) A W) (t : A) (ht : t ^ 2 = 1)
    (U S F : Submodule (ZMod 2) W) (hsplit : IsCompl U S) (hFU : F ≤ U)
    (hfix : ∀ v ∈ F, ρ t v = v) (hS : S.map (ρ t) ≤ S)
    (hsmall : 2 * (finrank (ZMod 2) U - finrank (ZMod 2) F) ≤ finrank (ZMod 2) S) :
    fixedCodim ρ (zpowers t) ≤ finrank (ZMod 2) S := by
  let N := ρ t - LinearMap.id
  have hchar (v : W) : v + v = 0 := by
    have he : (1 + 1 : ZMod 2) = 0 := by decide
    simpa only [add_smul, one_smul, zero_smul] using congrArg (fun r => r • v) he
  have htt (v : W) : ρ t (ρ t v) = v := by
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
      using congrArg (fun a => ρ a v) ht
  have hNN (v : W) : N (N v) = 0 := by
    change ρ t (ρ t v - v) - (ρ t v - v) = 0
    rw [map_sub, htt]
    have h1 := hchar v
    have h2 := hchar (ρ t v)
    calc
      v - ρ t v - (ρ t v - v) = (v + v) - (ρ t v + ρ t v) := by abel
      _ = 0 := by rw [h1, h2, sub_self]
  have hF : F ≤ U ⊓ N.ker := by
    intro v hv
    exact ⟨hFU hv, sub_eq_zero.mpr (hfix v hv)⟩
  have himage : S.map N ≤ S ⊓ N.ker := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨S.sub_mem (hS (Submodule.mem_map_of_mem hv)) hv, hNN v⟩
  have htotal : N.range = U.map N ⊔ S.map N := by
    rw [← Submodule.map_sup, hsplit.sup_eq_top, Submodule.map_top]
  have hU := rankNullity_on N U
  have hS' := rankNullity_on N S
  have hFdim := Submodule.finrank_mono hF
  have himagedim := Submodule.finrank_mono himage
  have hr := Submodule.finrank_add_le_finrank_add_finrank (U.map N) (S.map N)
  rw [fixedCodim_zpowers_eq_displacement_rank]
  change finrank (ZMod 2) N.range ≤ _
  rw [htotal]
  omega

end Representation.RegularCyclicNormalClosure.FactorConstruction
