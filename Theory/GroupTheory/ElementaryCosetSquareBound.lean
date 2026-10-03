module

public import Theory.GroupTheory.ElementaryCosetSquareRoots

/-!
# Exhausting square roots from an upper bound

The elementary cosets mF and m⁻¹F each contain |C_F(m)| roots of m².
When m has fourth power one and m² is outside F, these cosets are disjoint.
An upper bound of twice this centralizer order therefore forces all roots
in an overgroup K into the two cosets.

Source: the counting step in D. Parrott, *A characterization of the Tits'
simple group* (1972), printed p.682.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A sharp upper bound forces the two elementary root cosets to exhaust
all roots in the containing subgroup. -/
public theorem square_roots_mem_two_cosets_of_ncard_le (F K : Subgroup G) [IsElementaryAbelian 2 F]
    (hFK : F ≤ K) (m : G) (hm : m ∈ K) (hfour : m ^ 4 = 1)
    (hsq : m ^ 2 ∉ F)
    (hbound : {g : G | g ∈ K ∧ g ^ 2 = m ^ 2}.ncard ≤
      2 * Nat.card (F ⊓ centralizer ({m} : Set G) : Subgroup G)) :
    ∀ g ∈ K, g ^ 2 = m ^ 2 → m⁻¹ * g ∈ F ∨ m * g ∈ F := by
  let A : Set G := {g : G | m⁻¹ * g ∈ F ∧ g ^ 2 = m ^ 2}
  let B : Set G := {g : G | m * g ∈ F ∧ g ^ 2 = m ^ 2}
  let R : Set G := {g : G | g ∈ K ∧ g ^ 2 = m ^ 2}
  have hAB : Disjoint A B := Set.disjoint_left.mpr (by
    rintro g ⟨hg, _⟩ ⟨hg', _⟩
    apply hsq
    have hh := F.mul_mem hg' (F.inv_mem hg)
    convert hh using 1
    simp only [pow_two]
    group)
  have hsub : A ∪ B ⊆ R := by
    rintro g (⟨hg, hg2⟩ | ⟨hg, hg2⟩)
    · exact ⟨by simpa using K.mul_mem hm (hFK hg), hg2⟩
    · exact ⟨by simpa using K.mul_mem (K.inv_mem hm) (hFK hg), hg2⟩
  have hA : A.ncard = Nat.card (F ⊓ centralizer ({m} : Set G) : Subgroup G) :=
    ncard_square_coset F m
  have hB : B.ncard = Nat.card (F ⊓ centralizer ({m} : Set G) : Subgroup G) :=
    ncard_square_inverse_coset F m hfour
  have heq : A ∪ B = R := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_union_eq hAB, hA, hB, ← two_mul]
    exact hbound) (Set.toFinite _)
  intro g hg hg2
  have hh : g ∈ A ∪ B := heq.symm ▸ (show g ∈ R from ⟨hg,hg2⟩)
  exact hh.imp And.left And.left

end Subgroup
