module
public import Theory.GroupTheory.MaxElementaryImageComparison
/-! # Maximum elementary order with a shared central kernel
The image comparison still promotes an elementary subgroup to J(S) when its
kernel is already in the chosen maximum elementary subgroup. The exact
intersection cardinality replaces the disjoint-product calculation.
Source application: Aschbacher--Smith 2.5.7, exceptional PSL3(4) cover. -/
public section
open Subgroup
namespace Stellmacher
variable {G H:Type*} [Group G] [Finite G] [Group H]
theorem elementary_le_maxJ_of_image_bound_of_kernel_le
    (S A V:Subgroup G) (f:G→*H)
    (hA:A∈elementaryAbelianMaxSubgroups S) (hV:V≤S)
    [IsElementaryAbelian 2 V]
    (hc:V≤centralizer (A⊓f.ker:Set G)) (hk:V⊓f.ker≤A)
    (hb:Nat.card (A.map f)≤Nat.card (V.map f)) : V≤elementaryAbelianMaxJ S := by
  let C:=A⊓f.ker
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have he : IsElementaryAbelian 2 (V⊔C:Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc)
  have hint : V⊓C=V⊓f.ker := le_antisymm (inf_le_inf_left _ inf_le_right)
    (le_inf inf_le_left (le_inf hk inf_le_right))
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes V C
    ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
  rw [hint] at hprod
  have hlow : Nat.card A≤Nat.card (V⊔C:Subgroup G) := by
    apply Nat.le_of_mul_le_mul_left (c:=Nat.card (V⊓f.ker:Subgroup G)) _ Nat.card_pos
    calc
      _ = Nat.card (V⊓f.ker:Subgroup G)*Nat.card C*Nat.card (A.map f) := by
        rw [←IsElementaryAbelian.card_inf_ker_mul_card_map A f]; change
          Nat.card (V⊓f.ker:Subgroup G)*(Nat.card C*Nat.card (A.map f))=_
        ac_rfl
      _ ≤ Nat.card (V⊓f.ker:Subgroup G)*Nat.card C*Nat.card (V.map f) :=
        Nat.mul_le_mul_left _ hb
      _ = Nat.card V*Nat.card C := by
        rw [←IsElementaryAbelian.card_inf_ker_mul_card_map V f]; ac_rfl
      _ = _ := hprod
  exact le_sup_left.trans (le_sSup ⟨sup_le hV (inf_le_left.trans hA.1),he,
    fun B hBS hB => (hA.2.2 B hBS hB).trans hlow⟩)
end Stellmacher
