module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers in commuting factors and a normalizing supplement

An element normalizing two disjoint commuting factors centralizes their
product exactly when it centralizes each coordinate. A normalizing
supplement that centralizes the element is retained in this decomposition.
Uniqueness of the product coordinates proves the first identity; cancellation
of the supplement coordinate proves the second.

Source application: Aschbacher--Smith, proof of 14.6.9, printed p.1026,
where the point centralizer is the product of the two block point
centralizers and the original Sylow subgroup.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

/-- A normalizing element fixes a product of disjoint commuting factors coordinatewise. -/
theorem sup_inf_centralizer_singleton_of_disjoint_of_commuting (A B : Subgroup G) (z : G)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (hzA : z ∈ normalizer (A : Set G)) (hzB : z ∈ normalizer (B : Set G)) :
    (A ⊔ B) ⊓ centralizer ({z} : Set G) =
      (A ⊓ centralizer ({z} : Set G)) ⊔ (B ⊓ centralizer ({z} : Set G)) := by
  apply le_antisymm
  · rintro g ⟨hg,hgz⟩
    have hg' : g ∈ (A : Set G) * (B : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right A B
        (hc.trans (centralizer_le_normalizer _))]
      exact hg
    obtain ⟨a,ha,b,hb,rfl⟩ := hg'
    have he : z * (a*b) * z⁻¹ = a*b := by
      rw [←mem_centralizer_singleton_iff.mp hgz,mul_inv_cancel_right]
    have he' : (z*a*z⁻¹)*(z*b*z⁻¹) = a*b := by
      simpa only [mul_assoc,inv_mul_cancel_left] using he
    have hp : ((⟨z*a*z⁻¹,(mem_normalizer_iff.mp hzA a).mp ha⟩ : A),
        (⟨z*b*z⁻¹,(mem_normalizer_iff.mp hzB b).mp hb⟩ : B)) =
        ((⟨a,ha⟩ : A),(⟨b,hb⟩ : B)) := mul_injective_of_disjoint hd he'
    have ha' : z*a*z⁻¹ = a := congrArg (fun p : A × B => (p.1 : G)) hp
    have hb' : z*b*z⁻¹ = b := congrArg (fun p : A × B => (p.2 : G)) hp
    exact mul_mem_sup ⟨ha,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp ha').symm⟩ ⟨hb,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hb').symm⟩
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

/-- A supplement centralizing the element survives intersection with its centralizer. -/
theorem sup_inf_centralizer_singleton_of_centralizing_supplement (K R : Subgroup G) (z : G)
    (hn : R ≤ normalizer (K : Set G)) (hz : R ≤ centralizer ({z} : Set G)) :
    (K ⊔ R) ⊓ centralizer ({z} : Set G) =
      (K ⊓ centralizer ({z} : Set G)) ⊔ R := by
  apply le_antisymm
  · rintro g ⟨hg,hgz⟩
    have hg' : g ∈ (K : Set G) * (R : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left K R hn]
      exact hg
    obtain ⟨k,hk,r,hr,rfl⟩ := hg'
    have hkz := (centralizer ({z} : Set G)).mul_mem hgz
      ((centralizer ({z} : Set G)).inv_mem (hz hr))
    rw [mul_inv_cancel_right] at hkz
    exact mul_mem_sup ⟨hk,hkz⟩ hr
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hz)

end Subgroup
