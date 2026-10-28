module
public import Theory.Representation.SL2.PairedOddAxes
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SL2.BinarySmallModels
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
# Odd fixed points on paired natural sections

An odd subgroup of SL₂ in characteristic two fixing a nonzero natural vector
is trivial. On an exchanger-fixed pair, one nonzero coordinate forces both
coordinates to be nonzero. Thus an odd actor with nontrivial paired image
has only central-kernel fixed points. The second theorem retains an original
central supplement instead of assuming that the section splits.

Source application: Aschbacher--Smith 10.2.3(4), printed p.746.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups Pointwise
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H A B C : Subgroup G}
  {F : Type*} [Field F] [CharP F 2]
local instance pairedOddFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

private theorem paired_odd_fixed_eq_zero (q₁ q₂ : H →* SL(2,F))
    (P : Subgroup H) (hodd : Odd (Nat.card P)) (hne : ¬ P ≤ q₁.ker ⊓ q₂.ker)
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (v : (Fin 2 → F) × (Fin 2 → F)) (hrel : v.1 = f v.2)
    (hfix : ∀ p ∈ P, ((q₁ p).val *ᵥ v.1, (q₂ p).val *ᵥ v.2) = v) : v = 0 := by
  by_contra hv
  have hv₂ : v.2 ≠ 0 := by
    intro he
    have hzero : v.1 = 0 := by rw [hrel,he,map_zero]
    exact hv (Prod.ext hzero he)
  have hv₁ : v.1 ≠ 0 := by
    intro he
    apply hv₂
    apply f.injective
    rw [←hrel,he,map_zero]
  apply hne
  exact le_inf
    (SL2.PairedOddAxes.le_kernel_of_nonzero_fixed q₁ P hodd v.1 hv₁
      (fun p hp => congrArg Prod.fst (hfix p hp)))
    (SL2.PairedOddAxes.le_kernel_of_nonzero_fixed q₂ P hodd v.2 hv₂
      (fun p hp => congrArg Prod.snd (hfix p hp)))

/-- Any odd actor with nontrivial paired image has only central-kernel fixed
points on the subgroup centralized by the original exchanger. -/
theorem paired_natural_odd_fixed_eq_kernel (q₁ q₂ : H →* SL(2,F))
    (c : BinaryConjugationSection H A B
      (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
    (hc : B ≤ centralizer (H : Set G))
    (Z : Subgroup G) (hZA : Z ≤ A) (t : G)
    (ht : t ∈ normalizer (A : Set G)) (hZt : Z ≤ centralizer ({t} : Set G))
    (f : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
    (hswap : ∀ a : A,
      ((c.coordinates ⟨t * a * t⁻¹,(mem_normalizer_iff.mp ht a).mp a.property⟩).toAdd).1 =
        f (c.coordinates a).toAdd.2)
    (P : Subgroup H) (hodd : Odd (Nat.card P)) (hne : ¬ P ≤ q₁.ker ⊓ q₂.ker) :
    Z ⊓ centralizer (P.map H.subtype : Set G) = Z ⊓ B := by
  apply le_antisymm
  · intro z hz
    let a : A := ⟨z,hZA hz.1⟩
    have htz : t * z * t⁻¹ = z := by
      rw [hZt hz.1 t (Set.mem_singleton _),mul_inv_cancel_right]
    have hrel : (c.coordinates a).toAdd.1 = f (c.coordinates a).toAdd.2 := by
      have hh := hswap a
      have hsub : (⟨t * a * t⁻¹,(mem_normalizer_iff.mp ht a).mp a.property⟩ : A) = a :=
        Subtype.ext htz
      rwa [hsub] at hh
    have hfix : ∀ p ∈ P,
        ((q₁ p).val *ᵥ (c.coordinates a).toAdd.1,
          (q₂ p).val *ᵥ (c.coordinates a).toAdd.2) = (c.coordinates a).toAdd := by
      intro p hp
      have hpz : (p:G) * z * (p:G)⁻¹ = z := by
        rw [hz.2 p (mem_map_of_mem H.subtype hp),mul_inv_cancel_right]
      exact (c.equivariant p a).symm.trans
        (congrArg (fun y : A => (c.coordinates y).toAdd) (Subtype.ext hpz))
    have hzv := paired_odd_fixed_eq_zero q₁ q₂ P hodd hne f _ hrel hfix
    exact ⟨hz.1,(c.coordinates_eq_one_iff a).mp (Multiplicative.toAdd.injective hzv)⟩
  · intro z hz
    refine ⟨hz.1,?_⟩
    rintro y ⟨p,hp,rfl⟩
    exact hc hz.2 p p.property

/-- Odd fixed points with the source central summand retained. No splitting
of the central cover or prime divisor of the odd actor is prescribed. -/
theorem paired_natural_odd_fixed_eq_of_central_supplement (q₁ q₂ : H →* SL(2,F))
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
    (P : Subgroup H) (hodd : Odd (Nat.card P)) (hne : ¬ P ≤ q₁.ker ⊓ q₂.ker) :
    Z ⊓ centralizer (P.map H.subtype : Set G) = Z ⊓ centralizer (H : Set G) := by
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
    have hfix : ∀ p ∈ P,
        ((q₁ p).val *ᵥ (c.coordinates a₀).toAdd.1,
          (q₂ p).val *ᵥ (c.coordinates a₀).toAdd.2) = (c.coordinates a₀).toAdd := by
      intro p hp
      have hpk : (p:G)*k*(p:G)⁻¹ = k := by
        rw [hC hk p p.property,mul_inv_cancel_right]
      have hpa : (p:G)*a*(p:G)⁻¹ = a := by
        apply mul_right_cancel (b := k)
        calc
          ((p:G)*a*(p:G)⁻¹)*k = ((p:G)*a*(p:G)⁻¹)*((p:G)*k*(p:G)⁻¹) := by rw [hpk]
          _ = (p:G)*(a*k)*(p:G)⁻¹ := by group
          _ = a*k := by rw [hz.2 p (mem_map_of_mem H.subtype hp),mul_inv_cancel_right]
      exact (c.equivariant p a₀).symm.trans
        (congrArg (fun y : A => (c.coordinates y).toAdd) (Subtype.ext hpa))
    have hzv := paired_odd_fixed_eq_zero q₁ q₂ P hodd hne f _ hrel hfix
    have haC := ((c.coordinates_eq_one_iff a₀).mp (Multiplicative.toAdd.injective hzv)).2
    exact ⟨hz.1,(centralizer (H : Set G)).mul_mem haC (hC hk)⟩
  · exact inf_le_inf_left _ (centralizer_le (map_subtype_le P))

end Representation.BinaryConjugationSection
