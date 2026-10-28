module
public import Theory.Representation.BinaryConjugationSection.PairedSL2CubicFixed
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group
/-!
# Cubic fixed points with the original central summand retained

E.2.3 places the Sylow center in the moved module plus a subgroup centralizing
the actor. Decompose each central Sylow element along this product. Its moved
coordinates are fixed by the exchanger modulo the central coordinate kernel;
a cubic on either natural factor then kills both coordinates. This proves the
fixed-center equality before the central summand has been shown to vanish.

Source: Aschbacher–Smith 10.2.3(4), printed p.746.
-/
public section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A C : Subgroup G}
  {F : Type*} [Field F] [CharP F 2]
local instance centralSupplementFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

theorem paired_natural_cubic_fixed_eq_of_central_supplement (q₁ q₂ : H →* SL(2,F))
    (c : BinaryConjugationSection H A (A ⊓ centralizer (H : Set G))
      (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
    (hC : C ≤ centralizer (H : Set G))
    (Z : Subgroup G) (hZA : Z ≤ A ⊔ C) (t : G)
    (ht : t ∈ normalizer (A : Set G)) (htC : t ∈ normalizer (C : Set G))
    (hZt : Z ≤ centralizer ({t} : Set G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : A,
      ((c.coordinates ⟨t * a * t⁻¹,(mem_normalizer_iff.mp ht a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2)
    (b : H) (hb : orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3) :
    Z ⊓ centralizer ({(b : G)} : Set G) = Z ⊓ centralizer (H : Set G) := by
  have hCA : C ≤ normalizer (A : Set G) :=
    (hC.trans (centralizer_le c.section_le)).trans (Subgroup.centralizer_le_normalizer _)
  have hcoord (a a' : A) (k k' : C) (he : (a:G)*k = (a':G)*k') :
      c.coordinates a = c.coordinates a' := by
    have hd : ((a:G)⁻¹*a':G) ∈ C := by
      have heq : (a:G)⁻¹*a' = (k:G)*(k':G)⁻¹ := by
        calc
          (a:G)⁻¹*a' = (a:G)⁻¹*(a'*k')*(k':G)⁻¹ := by group
          _ = (a:G)⁻¹*(a*k)*(k':G)⁻¹ := by rw [he]
          _ = (k:G)*(k':G)⁻¹ := by group
      rw [heq]
      exact C.mul_mem k.property (C.inv_mem k'.property)
    have hh : c.coordinates (a⁻¹*a') = 1 :=
      (c.coordinates_eq_one_iff _).mpr ⟨(a⁻¹*a').property,hC hd⟩
    rw [map_mul,map_inv,inv_mul_eq_one] at hh
    exact hh
  apply le_antisymm
  · intro z hz
    have hzprod : z ∈ (A : Set G) * (C : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A C hCA]
      exact hZA hz.1
    obtain ⟨a,ha,k,hk,rfl⟩ := hzprod
    let a₀ : A := ⟨a,ha⟩
    let k₀ : C := ⟨k,hk⟩
    let aT : A := ⟨t*a*t⁻¹,(mem_normalizer_iff.mp ht a).mp ha⟩
    let kT : C := ⟨t*k*t⁻¹,(mem_normalizer_iff.mp htC k).mp hk⟩
    have htprod : (aT:G)*kT = (a₀:G)*k₀ := by
      change (t*a*t⁻¹)*(t*k*t⁻¹) = a*k
      calc
        (t*a*t⁻¹)*(t*k*t⁻¹) = t*(a*k)*t⁻¹ := by group
        _ = a*k := by rw [hZt hz.1 t (Set.mem_singleton _),mul_inv_cancel_right]
    have hrel : (c.coordinates a₀).toAdd.1 = f (c.coordinates a₀).toAdd.2 := by
      have hh := hswap a₀
      change (c.coordinates aT).toAdd.1 = _ at hh
      rw [hcoord aT a₀ kT k₀ htprod] at hh
      exact hh
    have hbk : (b:G)*k*(b:G)⁻¹ = k := by
      rw [hC hk b b.property,mul_inv_cancel_right]
    have hba : (b:G)*a*(b:G)⁻¹ = a := by
      apply mul_right_cancel (b := k)
      calc
        ((b:G)*a*(b:G)⁻¹)*k = ((b:G)*a*(b:G)⁻¹)*((b:G)*k*(b:G)⁻¹) := by rw [hbk]
        _ = (b:G)*(a*k)*(b:G)⁻¹ := by group
        _ = a*k := by rw [hz.2 b (Set.mem_singleton _),mul_inv_cancel_right]
    have he : (Representation.prod (SL2.BinarySmall.natural.comp q₁)
        (SL2.BinarySmall.natural.comp q₂)) b (c.coordinates a₀).toAdd =
          (c.coordinates a₀).toAdd := by
      exact (c.equivariant b a₀).symm.trans
        (congrArg (fun y : A => (c.coordinates y).toAdd) (Subtype.ext hba))
    have hzv : (c.coordinates a₀).toAdd = 0 := by
      rcases hb with hb | hb
      · have h1 := Matrix.SL2.cubic_fixed_eq_zero (q₁ b) hb
          (c.coordinates a₀).toAdd.1 (congrArg Prod.fst he)
        have h2 : (c.coordinates a₀).toAdd.2 = 0 := by
          apply f.injective
          rw [←hrel,h1,map_zero]
        exact Prod.ext h1 h2
      · have h2 := Matrix.SL2.cubic_fixed_eq_zero (q₂ b) hb
          (c.coordinates a₀).toAdd.2 (congrArg Prod.snd he)
        have h1 : (c.coordinates a₀).toAdd.1 = 0 := by rw [hrel,h2,map_zero]
        exact Prod.ext h1 h2
    have haC := ((c.coordinates_eq_one_iff a₀).mp (Multiplicative.toAdd.injective hzv)).2
    exact ⟨hz.1,(centralizer (H : Set G)).mul_mem haC (hC hk)⟩
  · intro z hz
    exact ⟨hz.1,fun y hy => Set.mem_singleton_iff.mp hy ▸ hz.2 b b.property⟩
end Representation.BinaryConjugationSection
