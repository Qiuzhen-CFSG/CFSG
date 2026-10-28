module
public import Theory.GroupTheory.SpecificGroups.DihedralEightCentralizer
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.IndexNormal

/-!
# Maximum elementary subgroups of a product of two dihedral eight-groups

Every elementary subgroup of D8 has order at most four. Projection therefore
bounds elementary subgroups of D8 × D8 by sixteen. Equality forces the subgroup
to be the product of its two projections, each of index two and hence normal.

The actual Sylow involution centralizer in Aschbacher--Smith F.5.4(2--3)
uses this intrinsic calculation to normalize its endpoint elementary cores.
-/

public noncomputable section
namespace DihedralGroup
open Subgroup
local notation "D8" => DihedralGroup 4

theorem elementary_card_le_four (E : Subgroup D8) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 4 := by
  by_cases h : 4 ≤ Nat.card E
  · exact (card_le_of_le (le_centralizer_iff_isMulCommutative.mpr hE.toIsMulCommutative)).trans
      (centralizer_le_of_card_ge_four E h).2
  · omega

theorem product_elementary_card_le_sixteen (E : Subgroup (D8 × D8))
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 16 := by
  let A := E.map (MonoidHom.fst D8 D8)
  let B := E.map (MonoidHom.snd D8 D8)
  have hA := elementary_card_le_four A (hE.map _)
  have hB := elementary_card_le_four B (hE.map _)
  have hEAB : E ≤ A.prod B := fun x hx => ⟨⟨x,hx,rfl⟩,⟨x,hx,rfl⟩⟩
  have hcard := card_le_of_le hEAB
  rw [Nat.card_congr (prodEquiv A B).toEquiv,Nat.card_prod] at hcard
  nlinarith

theorem product_elementary_sixteen_normal (E : Subgroup (D8 × D8))
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 16) : E.Normal := by
  let A := E.map (MonoidHom.fst D8 D8)
  let B := E.map (MonoidHom.snd D8 D8)
  have hA := elementary_card_le_four A (hE.map _)
  have hB := elementary_card_le_four B (hE.map _)
  have hEAB : E ≤ A.prod B := fun x hx => ⟨⟨x,hx,rfl⟩,⟨x,hx,rfl⟩⟩
  have hprod : Nat.card (A.prod B) = Nat.card A * Nat.card B := by
    rw [Nat.card_congr (prodEquiv A B).toEquiv,Nat.card_prod]
  have hcard := card_le_of_le hEAB
  rw [hc,hprod] at hcard
  have hcA : Nat.card A = 4 := by nlinarith
  have hcB : Nat.card B = 4 := by nlinarith
  have hnA : A.Normal := normal_of_index_eq_two (by
    have hh := A.card_mul_index
    rw [hcA,nat_card] at hh
    omega)
  have hnB : B.Normal := normal_of_index_eq_two (by
    have hh := B.card_mul_index
    rw [hcB,nat_card] at hh
    omega)
  have heq : E = A.prod B := eq_of_le_of_card_ge hEAB (by rw [hprod,hcA,hcB,hc])
  rw [heq]
  infer_instance

end DihedralGroup
