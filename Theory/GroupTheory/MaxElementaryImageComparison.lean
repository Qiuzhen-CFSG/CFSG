module
public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.NormalizedSupCard
/-! # Images of maximum elementary subgroups
A maximum elementary subgroup A has image at least as large as any elementary
V in the same two-subgroup that centralizes A intersect ker(f). Compare A with
V(A intersect ker(f)) using the exact kernel/image and product cardinalities.
Source application: Aschbacher--Smith 2.5.7, printed p.555. -/
public section
open Subgroup
open scoped IsMulCommutative
namespace Stellmacher
variable {G H:Type*} [Group G] [Finite G] [Group H]
theorem maxElementary_image_card_ge (S A V:Subgroup G) (f:G→*H)
    (hA:A∈elementaryAbelianMaxSubgroups S) (hV:V≤S)
    [IsElementaryAbelian 2 V]
    (hc:V≤centralizer (A⊓f.ker:Set G)) : Nat.card (V.map f)≤Nat.card (A.map f) := by
  let C := A⊓f.ker
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have he : IsElementaryAbelian 2 (V⊔C:Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc)
  have hmax : Nat.card (V⊔C:Subgroup G)≤Nat.card A :=
    hA.2.2 _ (sup_le hV (inf_le_left.trans hA.1)) he
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes V C
    ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
  have hCV : V⊓C≤V⊓f.ker := inf_le_inf_left V inf_le_right
  have hcard := Nat.card_le_card_of_injective (inclusion hCV) (inclusion_injective hCV)
  have hVprod := IsElementaryAbelian.card_inf_ker_mul_card_map V f
  have hAprod := IsElementaryAbelian.card_inf_ker_mul_card_map A f
  have hm : Nat.card C*Nat.card (V.map f)≤Nat.card (V⊔C:Subgroup G) := by
    apply Nat.le_of_mul_le_mul_left (c:=Nat.card (V⊓f.ker:Subgroup G)) _ Nat.card_pos
    calc
      _ = Nat.card V*Nat.card C := by rw [←hVprod]; ac_rfl
      _ = Nat.card (V⊓C:Subgroup G)*Nat.card (V⊔C:Subgroup G) := hprod
      _ ≤ _ := Nat.mul_le_mul_right _ hcard
  apply Nat.le_of_mul_le_mul_left (c:=Nat.card C) _ Nat.card_pos
  exact hm.trans (hmax.trans_eq hAprod.symm)
theorem elementary_le_maxJ_of_image_bound (S A V:Subgroup G) (f:G→*H)
    (hA:A∈elementaryAbelianMaxSubgroups S) (hV:V≤S)
    [IsElementaryAbelian 2 V]
    (hc:V≤centralizer (A⊓f.ker:Set G)) (hd:Disjoint V f.ker)
    (hb:Nat.card (A.map f)≤Nat.card V) : V≤elementaryAbelianMaxJ S := by
  let C:=A⊓f.ker
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have he : IsElementaryAbelian 2 (V⊔C:Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc)
  have hint : V⊓C=⊥ := bot_unique ((inf_le_inf_left V inf_le_right).trans hd.le_bot)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes V C
    ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
  rw [hint,card_bot,one_mul] at hprod
  have hlow : Nat.card A≤Nat.card (V⊔C:Subgroup G) := by
    rw [←hprod,←IsElementaryAbelian.card_inf_ker_mul_card_map A f]
    change Nat.card C * Nat.card (A.map f) ≤ Nat.card V * Nat.card C
    simpa [mul_comm] using Nat.mul_le_mul_left (Nat.card C) hb
  exact le_sup_left.trans (le_sSup ⟨sup_le hV (inf_le_left.trans hA.1),he,
    fun B hBS hB => (hA.2.2 B hBS hB).trans hlow⟩)

end Stellmacher
