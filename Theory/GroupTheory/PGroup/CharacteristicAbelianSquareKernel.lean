module

public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini

/-!
# Extracting a characteristic elementary eight by squaring

An abelian characteristic subgroup of order at least 32 has first omega of
order at least eight if its squares lie in a center of order at most four.
The square homomorphism has image of order at most four, and its kernel is
first omega. Characteristicity and elementary abelianness pass to the ambient
image of that kernel.

This is the final counting step in the special order-128 argument associated
with MacWilliams, Trans. AMS 150 (1970), §4, and Janko–Thompson, Math. Z. 113
(1970), result 1.4(c), printed p.386.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsPGroup

/-- A large characteristic abelian subgroup with small central square image
contains a characteristic elementary subgroup of order at least eight. -/
public theorem exists_characteristic_elementary_eight_of_abelian {G : Type*} [Group G] [Finite G]
    (hZ : Nat.card (center G) ≤ 4)
    (hsq : ∀ x : G, x ^ 2 ∈ center G)
    (A : Subgroup G) [A.Characteristic] [IsMulCommutative A]
    (hA : 32 ≤ Nat.card A) :
    ∃ E : Subgroup G, E.Characteristic ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CommGroup A := IsMulCommutative.instCommGroup
  let f : A →* A := powMonoidHom 2
  let K := omega₁ A (p := 2)
  let E := K.map A.subtype
  let : K.Characteristic := omega₁_characteristic A
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hR : f.range.map A.subtype ≤ center G := by
    rintro x ⟨a, ⟨y, rfl⟩, rfl⟩
    exact hsq y
  have hr : Nat.card f.range ≤ 4 := by
    rw [← card_map_of_injective A.subtype_injective (K := f.range)]
    exact (card_le_of_le hR).trans hZ
  have hp := f.ker.card_mul_index
  rw [index_ker] at hp
  have hk : 8 ≤ Nat.card K := by
    change 8 ≤ Nat.card (omega₁ A (p := 2))
    rw [← IsPGroup.square_ker_eq_omega_one]
    change 8 ≤ Nat.card f.ker
    nlinarith
  refine ⟨E, inferInstance, IsElementaryAbelian.map_subtype, ?_⟩
  exact (card_map_of_injective A.subtype_injective).symm ▸ hk

end IsPGroup
