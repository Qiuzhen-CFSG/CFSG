module

public import Theory.GroupTheory.DihedralUniqueInvolutionProduct
public import Theory.ElementaryAbelian.Basic

/-!
# Elementary subgroup orders in two and four dihedral factors

Every elementary subgroup of a finite dihedral group has order at most four.
Projection into the factors bounds an elementary subgroup of a product by the
product of these orders. In particular the four square-dihedral factors in
Aschbacher–Smith 10.2.1 admit no elementary subgroup larger than 256.
-/

public section
open Subgroup
namespace Theory.GroupTheory

private theorem elementary_card_prod_bound
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (m n : ℕ)
    (hG : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A ≤ m)
    (hH : ∀ B : Subgroup H, IsElementaryAbelian 2 B → Nat.card B ≤ n)
    (E : Subgroup (G × H)) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ m * n := by
  let := hE
  calc
    Nat.card E ≤ Nat.card ((E.map (MonoidHom.fst G H)).prod
        (E.map (MonoidHom.snd G H))) :=
      card_le_of_le (le_prod_iff.mpr ⟨le_rfl,le_rfl⟩)
    _ = Nat.card (E.map (MonoidHom.fst G H)) *
        Nat.card (E.map (MonoidHom.snd G H)) := by
      rw [Nat.card_congr (prodEquiv _ _).toEquiv,Nat.card_prod]
    _ ≤ m * n := Nat.mul_le_mul (hG _ (hE.map _)) (hH _ (hE.map _))

/-- Two dihedral factors of order eight have elementary subgroups of order at
most sixteen. -/
theorem dihedral_square_elementary_card_le
    (E : Subgroup (DihedralGroup 4 × DihedralGroup 4))
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 16 := by
  have hbound (A : Subgroup (DihedralGroup 4)) (hA : IsElementaryAbelian 2 A) :
      Nat.card A ≤ 4 := by
    let := hA
    exact DihedralGroup.card_le_four_of_square_eq_one A
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A))
  exact elementary_card_prod_bound 4 4 hbound hbound E hE

/-- Four dihedral factors of order eight have elementary subgroups of order at
most 256. -/
theorem dihedral_four_elementary_card_le
    (E : Subgroup ((DihedralGroup 4 × DihedralGroup 4) ×
      (DihedralGroup 4 × DihedralGroup 4)))
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 256 :=
  elementary_card_prod_bound 16 16 dihedral_square_elementary_card_le
    dihedral_square_elementary_card_le E hE

/-- The bound applies to the actual subgroup under a specified recognition. -/
theorem dihedral_four_elementary_card_le_of_equiv
    {G : Type*} [Group G]
    (e : G ≃* ((DihedralGroup 4 × DihedralGroup 4) ×
      (DihedralGroup 4 × DihedralGroup 4)))
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 256 := by
  have h := dihedral_four_elementary_card_le (E.map e.toMonoidHom) (hE.map _)
  rwa [card_map_of_injective e.injective] at h

end Theory.GroupTheory
