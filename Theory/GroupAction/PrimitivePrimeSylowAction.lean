module
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.BigOperators.Associated

/-!
# Primitive torus Sylows on binary elementary groups

If ordₚ(2) = n, the p-part of |GLₙ(2)| occurs entirely in the factor
2ⁿ−1. Consequently a faithful torus of order 2ⁿ−1 has index prime to p
in the full automorphism group of an elementary group of order 2ⁿ.
Its Sylow p-subgroup accounts for every p-subgroup of automorphisms
containing that Sylow image.

For an ambient p-group containing the torus Sylow, this identifies its
point stabilizer as the torus Sylow times the pointwise centralizer.
It does not assert that the whole p-group preserves the elementary group.
Source application: Aschbacher–Smith, proof of 5.1.17, printed p.640
(refs/quasithin.pdf), the action in the primitive-prime Sylow calculation.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {Z A : Type*} [Group Z] [Finite Z] [IsElementaryAbelian 2 Z]
  [Group A] [Finite A] {p n : ℕ} [Fact p.Prime]

omit [Finite A] in
theorem primitive_binary_torus_index
    (hn : 0 < n) (ho : orderOf (2 : ZMod p) = n)
    (hZ : Nat.card Z = 2^n) (f : A →* MulAut Z) (hf : Function.Injective f)
    (hA : Nat.card A = 2^n-1) : ¬ p ∣ f.range.index := by
  classical
  let i0 : Fin n := ⟨0,hn⟩
  let s : Finset (Fin n) := Finset.univ.erase i0
  have hpow : (2 : ZMod p)^n = 1 := by rw [←ho]; exact pow_orderOf_eq_one (2 : ZMod p)
  have hfree : ¬ p ∣ ∏ i ∈ s, (2^n-2^(i : ℕ)) := by
    intro hd
    obtain ⟨i,hi,hdi⟩ := ((Nat.prime_iff.mp (Fact.out : p.Prime)).dvd_finsetProd_iff _).mp hd
    have hi0 : 0 < (i : ℕ) := by
      have hh := (Finset.mem_erase.mp hi).1
      have hne : (i : ℕ) ≠ 0 := fun he => hh (Fin.ext he)
      omega
    have hi_le : 2^(i : ℕ) ≤ 2^n := Nat.pow_le_pow_right (by decide) i.isLt.le
    have hh := (ZMod.natCast_eq_zero_iff _ p).mpr hdi
    rw [Nat.cast_sub hi_le,Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,hpow] at hh
    have hsmall : n ≤ (i : ℕ) := by
      exact ho.ge.trans (orderOf_le_of_pow_eq_one hi0 (sub_eq_zero.mp hh).symm)
    omega
  obtain ⟨e,he⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le Z hZ.le
  have hd := card_dvd_of_injective e he
  have hcard : Nat.card (MulAut Z) = f.range.index * (2^n-1) := by
    rw [←f.range.index_mul_card,←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,hA]
  have hgl : Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) =
      (2^n-1) * ∏ i ∈ s, (2^n-2^(i : ℕ)) := by
    rw [Matrix.card_GL_field]
    simp only [ZMod.card]
    have hh := Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
      (fun i : Fin n => 2^n-2^(i : ℕ)) (Finset.mem_univ i0)
    simpa only [i0,Fin.val_mk,pow_zero] using hh.symm
  rw [hcard,hgl,mul_comm f.range.index] at hd
  have hq : 0 < 2^n-1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by decide))
  exact fun hh => hfree (hh.trans (Nat.dvd_of_mul_dvd_mul_left hq hd))

/-- A primitive-prime Sylow of a faithful binary torus is Sylow in the
full automorphism group of its elementary module. -/
theorem primitive_binary_torus_sylow
    (hn : 0 < n) (ho : orderOf (2 : ZMod p) = n)
    (hZ : Nat.card Z = 2^n) (f : A →* MulAut Z) (hf : Function.Injective f)
    (hA : Nat.card A = 2^n-1) (R : Sylow p A)
    (P : Subgroup (MulAut Z)) (hP : IsPGroup p P)
    (hRP : (R : Subgroup A).map f ≤ P) : P = (R : Subgroup A).map f := by
  let e := MonoidHom.ofInjective hf
  let S := R.mapSurjective e.surjective
  have hi : ¬ p ∣ ((R : Subgroup A).map f).index := by
    have heq : (R : Subgroup A).map f = (S : Subgroup f.range).map f.range.subtype := by
      change (R : Subgroup A).map f = ((R : Subgroup A).map e.toMonoidHom).map f.range.subtype
      rw [Subgroup.map_map]
      rfl
    rw [heq,index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul S.not_dvd_index
      (primitive_binary_torus_index hn ho hZ f hf hA)
  exact ((R.isPGroup'.map f).toSylow hi).is_maximal' hP hRP
end Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The point stabilizer in an arbitrary p-overgroup of a primitive torus
Sylow is the product of that Sylow and the pointwise centralizer. -/
theorem primitive_torus_point_stabilizer
    (Z A P : Subgroup G) [IsElementaryAbelian 2 Z]
    {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    (ho : orderOf (2 : ZMod p) = n) (hZ : Nat.card Z = 2^n)
    (hAZ : A ≤ normalizer (Z : Set G))
    (hf : Function.Injective (Z.normalizerMonoidHom.comp (inclusion hAZ)))
    (hA : Nat.card A = 2^n-1) (hP : IsPGroup p P) (R : Sylow p A)
    (hRP : (R : Subgroup A).map A.subtype ≤ P) :
    P ⊓ normalizer (Z : Set G) =
      (R : Subgroup A).map A.subtype ⊔ (P ⊓ centralizer (Z : Set G)) := by
  let Q := P ⊓ normalizer (Z : Set G)
  let α : Q →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion inf_le_right)
  let f : A →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hAZ)
  have hQ : IsPGroup p Q := hP.to_le inf_le_left
  have hr : (R : Subgroup A).map f ≤ α.range := by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨⟨a,hRP (mem_map_of_mem A.subtype ha),hAZ a.property⟩,rfl⟩
  have he : α.range = (R : Subgroup A).map f :=
    primitive_binary_torus_sylow hn ho hZ f hf hA R α.range
      (hQ.of_surjective α.rangeRestrict α.rangeRestrict_surjective) hr
  have hRZ : (R : Subgroup A).map A.subtype ≤ normalizer (Z : Set G) :=
    (map_subtype_le _).trans hAZ
  apply le_antisymm _ (sup_le (le_inf hRP hRZ)
    (le_inf inf_le_left (inf_le_right.trans (centralizer_le_normalizer _))))
  intro x hx
  have hm : α ⟨x,hx⟩ ∈ (R : Subgroup A).map f := he ▸ (show α ⟨x,hx⟩ ∈ α.range from ⟨_,rfl⟩)
  obtain ⟨a,ha,hae⟩ := hm
  have hk : (a : G)⁻¹*x ∈ centralizer (Z : Set G) := by
    let y : normalizer (Z : Set G) := ⟨(a : G)⁻¹*x,
      (normalizer (Z : Set G)).mul_mem
        ((normalizer (Z : Set G)).inv_mem (hAZ a.property)) hx.2⟩
    have hy : Z.normalizerMonoidHom y = 1 := by
      change Z.normalizerMonoidHom ((inclusion hAZ a)⁻¹ * inclusion inf_le_right ⟨x,hx⟩) = 1
      rw [map_mul,map_inv]
      change (f a)⁻¹ * α ⟨x,hx⟩ = 1
      rw [hae,inv_mul_cancel]
    have hh : y ∈ Z.normalizerMonoidHom.ker := hy
    rwa [normalizerMonoidHom_ker] at hh
  have hmem := ((R : Subgroup A).map A.subtype ⊔ (P ⊓ centralizer (Z : Set G))).mul_mem
    (mem_sup_left (mem_map_of_mem A.subtype ha))
    (mem_sup_right (show (a : G)⁻¹*x ∈ P ⊓ centralizer (Z : Set G) from
      ⟨P.mul_mem (P.inv_mem (hRP (mem_map_of_mem A.subtype ha))) hx.1,hk⟩))
  change (a : G) * ((a : G)⁻¹*x) ∈ (R : Subgroup A).map A.subtype ⊔
    (P ⊓ centralizer (Z : Set G)) at hmem
  simpa only [mul_inv_cancel_left] using hmem

end Subgroup
