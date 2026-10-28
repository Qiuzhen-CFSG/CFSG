module

public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Two independent cubic directions force order nine

The degree-one terminal case of Fong--Seitz (6G), printed p.50, uses the
elementary counting fact that two disjoint commuting subgroups of order three
inside the relevant Cartan subgroup force that subgroup to have order at least
nine.  This file isolates that counting step.  It does not construct the two
cubic directions; those remain source-specific data.
-/

public section
open Subgroup

namespace Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- Two disjoint commuting cubic subgroups force an order-nine subgroup. -/
theorem card_ge_nine_of_disjoint_commuting_cubic
    (H A B : Subgroup G)
    (hAH : A ≤ H) (hBH : B ≤ H)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hdisj : Disjoint A B)
    (hcomm : A ≤ centralizer (B : Set G)) :
    9 ≤ Nat.card H := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hdisj hcomm
  have hsup : Nat.card (A ⊔ B : Subgroup G) = 9 := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hA, hB]
  have hle : A ⊔ B ≤ H := sup_le hAH hBH
  exact hsup ▸ Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)

/-- An order-three Cartan cannot contain two independent commuting cubic factors. -/
theorem not_card_three_of_disjoint_commuting_cubic
    (H A B : Subgroup G)
    (hAH : A ≤ H) (hBH : B ≤ H)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hdisj : Disjoint A B)
    (hcomm : A ≤ centralizer (B : Set G))
    (hH : Nat.card H = 3) :
    False := by
  have h9 := card_ge_nine_of_disjoint_commuting_cubic H A B hAH hBH hA hB hdisj hcomm
  omega

end Theory.GroupTheory

