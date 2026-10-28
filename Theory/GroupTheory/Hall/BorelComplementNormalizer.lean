module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
/-!
# Preserving the actual Borel complement

For a two-group R and an odd group B, a subgroup D of B normalizing R
is exactly RD∩B. Thus actors preserving RD and B preserve D itself.
This is the torus-normalizer step of Aschbacher–Smith 2.4.12(1), p.532.
-/
public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G]

private theorem normal_product_intersection (R D B : Subgroup G)
    (hDR : D ≤ normalizer (R : Set G)) (hDB : D ≤ B) (hdis : Disjoint R B) :
    (R ⊔ D) ⊓ B = D := by
  apply le_antisymm _ (le_inf le_sup_right hDB)
  rintro z ⟨hz,hzB⟩
  have hz' : z ∈ (R : Set G)*(D : Set G) :=
    (coe_mul_of_right_le_normalizer_left R D hDR) ▸ hz
  obtain ⟨r,hr,d,hd,he⟩ := hz'
  have hrB : r ∈ B := by
    have hrd := B.mul_mem hzB (B.inv_mem (hDB hd))
    rw [←he,mul_inv_cancel_right] at hrd
    exact hrd
  have hr1 := disjoint_def.mp hdis hr hrB
  have hdZ : d = z := by simpa only [hr1,one_mul] using he
  exact hdZ ▸ hd

variable [Finite G]
theorem torusNormalizer_preserves_borel_complement
    (S R D B : Subgroup G) (hR : IsPGroup 2 R) (hB : Odd (Nat.card B))
    (hDB : D ≤ B) (hDR : D ≤ normalizer (R : Set G))
    (hS : S ≤ normalizer ((R ⊔ D : Subgroup G) : Set G)) :
    S ⊓ normalizer (B : Set G) ≤ normalizer (D : Set G) := by
  obtain ⟨k,hk⟩ := hR.exists_card_eq
  have hd : Disjoint R B := disjoint_of_coprime_natCard (by
    rw [hk]
    exact (Nat.coprime_two_left.mpr hB).pow_left k)
  have he := normal_product_intersection R D B hDR hDB hd
  exact he ▸ ((le_inf (inf_le_left.trans hS) inf_le_right).trans inf_normalizer_le_normalizer_inf)
end Subgroup
