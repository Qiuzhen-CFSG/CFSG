module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Intersecting subgroup products inside commuting factors

For two disjoint commuting factors, products of subgroups intersect
coordinate by coordinate. Uniqueness of the two factor coordinates gives
the equality, without requiring the factor subgroups to be normal.
This is the direct-product calculation used in Aschbacher--Smith,
C.5.6(7)(iii), printed pp.158--159.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

theorem sup_inf_sup_eq_of_disjoint_commuting_factors (F E A B C D : Subgroup G)
    (hd : Disjoint F E) (hc : F ≤ centralizer (E : Set G))
    (hAF : A ≤ F) (hBE : B ≤ E) (hCF : C ≤ F) (hDE : D ≤ E) :
    (A ⊔ B) ⊓ (C ⊔ D) = (A ⊓ C) ⊔ (B ⊓ D) := by
  have hnAB : B ≤ normalizer (A : Set G) :=
    (hBE.trans ((le_centralizer_iff.mp hc).trans (centralizer_le hAF))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnCD : D ≤ normalizer (C : Set G) :=
    (hDE.trans ((le_centralizer_iff.mp hc).trans (centralizer_le hCF))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm
  · rintro g ⟨hgAB, hgCD⟩
    have hgAB' : g ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hnAB]
      exact hgAB
    have hgCD' : g ∈ (C : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left C D hnCD]
      exact hgCD
    obtain ⟨a, ha, b, hb, rfl⟩ := hgAB'
    obtain ⟨c, hc', d, hd', he⟩ := hgCD'
    have hp : ((⟨c, hCF hc'⟩ : F), (⟨d, hDE hd'⟩ : E)) =
        ((⟨a, hAF ha⟩ : F), (⟨b, hBE hb⟩ : E)) :=
      mul_injective_of_disjoint hd he
    have hca : c = a := congrArg (fun p : F × E => (p.1 : G)) hp
    have hdb : d = b := congrArg (fun p : F × E => (p.2 : G)) hp
    exact mul_mem_sup ⟨ha, hca ▸ hc'⟩ ⟨hb, hdb ▸ hd'⟩
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) (inf_le_right.trans le_sup_left))
      (le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right))

end Subgroup
