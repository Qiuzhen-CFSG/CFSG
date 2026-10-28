module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Centralizers in a disjoint normalized product

An element normalizing both factors of an internal semidirect product fixes
an element of the product exactly when it fixes each coordinate. Uniqueness
of the product coordinates gives the centralizer decomposition, without
assuming that the two factors commute.

The consumer is the actual odd-core/SL₂(3) decomposition of a cubic
centralizer in G2Recognition.MaximalCoreIntersection, in the analysis of
Aschbacher–Smith I.4.5, printed p.417.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem sup_inf_centralizer_of_normalized_disjoint (A B : Subgroup G) (z : G)
    (hn : B ≤ normalizer (A:Set G)) (hd : Disjoint A B)
    (hzA : z∈normalizer (A:Set G)) (hzB : z∈normalizer (B:Set G)) :
    (A⊔B) ⊓ centralizer ({z}:Set G)=
      (A ⊓ centralizer ({z}:Set G)) ⊔ (B ⊓ centralizer ({z}:Set G)) := by
  apply le_antisymm
  · rintro g ⟨hg,hgz⟩
    have hg' : g∈(A:Set G)*(B:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A B hn]
      exact hg
    obtain ⟨a,ha,b,hb,rfl⟩ := hg'
    have he : (z*a*z⁻¹)*(z*b*z⁻¹)=a*b := by
      calc
        _ = z*(a*b)*z⁻¹ := by group
        _ = a*b := by rw [←mem_centralizer_singleton_iff.mp hgz,mul_inv_cancel_right]
    have hp : ((⟨z*a*z⁻¹,(mem_normalizer_iff.mp hzA a).mp ha⟩:A),
        (⟨z*b*z⁻¹,(mem_normalizer_iff.mp hzB b).mp hb⟩:B)) =
        ((⟨a,ha⟩:A),(⟨b,hb⟩:B)) := mul_injective_of_disjoint hd he
    have ha' := congrArg (fun p : A×B => (p.1:G)) hp
    have hb' := congrArg (fun p : A×B => (p.2:G)) hp
    exact mul_mem_sup ⟨ha,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp ha').symm⟩ ⟨hb,mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hb').symm⟩
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
end Subgroup
