module
public import Theory.Representation.BinaryConjugationSection.SL2CubicFixed
/-!
# Cubic fixed points on a paired natural central section

On two natural SL₂ factors, a nontrivial cubic factor kills its own fixed
coordinate. For elements centralized by an exchanger, the other coordinate
then vanishes as well. Thus even an axis cubic has only central-kernel fixed
points on the exchanger-fixed subgroup. The full paired module itself can
have a nonzero axis fixed space; its exchanger-fixed part is the relevant
subgroup here.

Source: Aschbacher–Smith10.2.3(4), printed p.746.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A B : Subgroup G}
  {F : Type*} [Field F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- A cubic in either natural factor has only kernel fixed points on Z fixed by the exchanger. -/
theorem paired_natural_cubic_fixed_eq_kernel (q₁ q₂ : H →* SL(2,F))
    (c : BinaryConjugationSection H A B
      (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
    (hc : B ≤ centralizer (H : Set G))
    (Z : Subgroup G) (hZA : Z ≤ A) (t : G)
    (ht : t ∈ normalizer (A : Set G)) (hZt : Z ≤ centralizer ({t} : Set G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : A,
      ((c.coordinates ⟨t * a * t⁻¹,(mem_normalizer_iff.mp ht a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2)
    (b : H) (hb : orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3) :
    Z ⊓ centralizer ({(b : G)} : Set G) = Z ⊓ B := by
  apply le_antisymm
  · intro z hz
    let a : A := ⟨z,hZA hz.1⟩
    have htb : t * z * t⁻¹ = z := by
      rw [hZt hz.1 t (Set.mem_singleton _), mul_inv_cancel_right]
    have hrel : (c.coordinates a).toAdd.1 = f (c.coordinates a).toAdd.2 := by
      have hh := hswap a
      have hsub : (⟨t * a * t⁻¹,(mem_normalizer_iff.mp ht a).mp a.property⟩ : A) = a :=
        Subtype.ext htb
      rwa [hsub] at hh
    have hbb : (b : G) * z * (b : G)⁻¹ = z := by
      rw [hz.2 b (Set.mem_singleton _), mul_inv_cancel_right]
    have he : (Representation.prod (SL2.BinarySmall.natural.comp q₁)
        (SL2.BinarySmall.natural.comp q₂)) b (c.coordinates a).toAdd =
          (c.coordinates a).toAdd := by
      exact (c.equivariant b a).symm.trans
        (congrArg (fun y : A => (c.coordinates y).toAdd) (Subtype.ext hbb))
    have hzv : (c.coordinates a).toAdd = 0 := by
      rcases hb with hb | hb
      · have h1 := Matrix.SL2.cubic_fixed_eq_zero (q₁ b) hb
          (c.coordinates a).toAdd.1 (congrArg Prod.fst he)
        have h2 : (c.coordinates a).toAdd.2 = 0 := by
          apply f.injective
          rw [←hrel,h1,map_zero]
        exact Prod.ext h1 h2
      · have h2 := Matrix.SL2.cubic_fixed_eq_zero (q₂ b) hb
          (c.coordinates a).toAdd.2 (congrArg Prod.snd he)
        have h1 : (c.coordinates a).toAdd.1 = 0 := by rw [hrel,h2,map_zero]
        exact Prod.ext h1 h2
    exact ⟨hz.1,(c.coordinates_eq_one_iff a).mp (Multiplicative.toAdd.injective hzv)⟩
  · intro z hz
    refine ⟨hz.1,?_⟩
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact hc hz.2 b b.property
end Representation.BinaryConjugationSection
