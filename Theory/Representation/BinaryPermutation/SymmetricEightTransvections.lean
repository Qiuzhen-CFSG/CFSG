module

public import Theory.Representation.BinaryOffender.Basic
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections.Linear
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections.Permutations
import Mathlib.Tactic

/-!
# Transvection involutions in arbitrary faithful binary S₈-modules

An involution with fixed-space codimension one acts as a rank-one binary
transvection. The intrinsic permutation configurations exclude each of the
other three involution cycle types: three transpositions give a product of
order seven, while two and four transpositions violate the centralizer
identity for a triple of transvections. Faithfulness transfers these
operator obstructions back to S₈.

The conclusion uses the supplied group isomorphism, with no identification
of the representation as a natural, augmentation, or orthogonal module.
It supplies the intrinsic involution step for Aschbacher–Smith, *The
Classification of Quasithin Groups*, 13.8.25, printed p.960 (PDF p.977).
It does not assert the subsequent module-recognition or orthogonal-exclusion
conclusions of that source argument.
-/

public section

namespace Representation.SymmetricEightTransvections

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A transvection in any faithful binary linear action of S₈ is a transposition.
This uses only intrinsic permutation and rank-one operator relations. -/
theorem isSwap_of_transvection
    (φ : Equiv.Perm (Fin 8) →* (V ≃ₗ[ZMod 2] V))
    (hφ : Function.Injective φ) (a : Equiv.Perm (Fin 8))
    (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (ht : φ a ∈ LinearEquiv.transvections (ZMod 2) V) : a.IsSwap := by
  have hconj {b : Equiv.Perm (Fin 8)} (hb : IsConj a b) :
      φ b ∈ LinearEquiv.transvections (ZMod 2) V := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hb
    simpa only [map_mul, map_inv] using Linear.conjugate (φ g) (φ a) ht
  by_contra hs
  rcases involution_obstruction a ha ha2 hs with
    ⟨b, hb, hp, hn⟩ | ⟨b, g, hb, hab, hg, hn⟩
  · have hp' : (φ a * φ b) ^ 7 = 1 := by
      simpa only [map_mul, map_pow, map_one] using congrArg φ hp
    have hn' : φ a * φ b ≠ 1 := by
      intro h
      apply hn
      apply hφ
      simpa only [map_mul, map_one] using h
    rcases Linear.product_cube_or_fourth (φ a) (φ b) ht (hconj hb) with h3 | h4
    · have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp')
        (orderOf_dvd_of_pow_eq_one h3)
      norm_num at hd
      exact hn' hd
    · have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hp')
        (orderOf_dvd_of_pow_eq_one h4)
      norm_num at hd
      exact hn' hd
  · have ha' : φ a ≠ 1 := by
      intro h
      apply ha
      exact hφ (h.trans φ.map_one.symm)
    have hb' : φ b ≠ 1 := by
      intro h
      have hb1 : b = 1 := hφ (h.trans φ.map_one.symm)
      exact ha (isConj_one_left.mp (hb1 ▸ hb))
    have hcomm := Linear.commute_conjugate_of_triple (φ a) (φ b) (φ g)
      ht (hconj hb) (by simpa only [map_mul] using hconj hab) ha' hb' (hg.map φ)
    apply hn
    apply hφ
    simpa only [map_mul, map_inv] using hcomm.eq

open Representation.BinaryOffender Subgroup

private theorem fixedCodim_zpowers_eq_displacement {H : Type*} [Group H]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V) (a : H) :
    fixedCodim ρ (zpowers a) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) := by
  let f : V →ₗ[ZMod 2] V := ρ a - LinearMap.id
  have hk : f.ker = fixedSpace ρ (zpowers a) := by
    ext v
    have hg : ∀ x : zpowers a, x ∈ zpowers (⟨a, mem_zpowers a⟩ : zpowers a) := by
      intro x
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp x.property
      exact mem_zpowers_iff.mpr ⟨n, Subtype.ext hn⟩
    rw [show v ∈ fixedSpace ρ (zpowers a) ↔ ρ a v = v from
      Representation.mem_invariants_iff_of_forall_mem_zpowers
        (ρ.comp (zpowers a).subtype) ⟨a, mem_zpowers a⟩ hg v]
    exact sub_eq_zero
  have hn := f.finrank_range_add_finrank_ker
  have hc := fixedCodim_add_finrank ρ (zpowers a)
  rw [hk] at hn
  change Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) + _ = _ at hn
  omega

/-- In every faithful finite-dimensional binary S₈-module, an involution
whose cyclic fixed space has codimension one is a transposition under the
given group isomorphism. No module identification is assumed. -/
theorem isSwap_of_fixedCodim_eq_one {H : Type*} [Group H]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
    (hρ : Function.Injective ρ) (eH : H ≃* Equiv.Perm (Fin 8))
    (a : H) (ha : a ≠ 1) (ha2 : a ^ 2 = 1)
    (hc : fixedCodim ρ (zpowers a) = 1) : (eH a).IsSwap := by
  let e : H →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
      ρ.asGroupHom
  have he : Function.Injective e := fun x y h => hρ (congrArg LinearEquiv.toLinearMap h)
  have ht : e a ∈ LinearEquiv.transvections (ZMod 2) V := by
    have hd : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1 := by
      rw [← fixedCodim_zpowers_eq_displacement ρ a, hc]
    exact Linear.of_small_displacement (e a) hd
  apply isSwap_of_transvection (e.comp eH.symm.toMonoidHom)
    (he.comp eH.symm.injective) (eH a)
  · exact fun h => ha (eH.injective (h.trans eH.map_one.symm))
  · simpa only [map_pow, map_one] using congrArg eH ha2
  · simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eH.symm_apply_apply] using ht

end Representation.SymmetricEightTransvections
