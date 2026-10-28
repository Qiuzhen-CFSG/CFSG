module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Counts
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Local counting in full extensions before proving native generation

The marked endpoint and whole-middle maps preserve their orders. Cancelling
the common middle order transfers both local indices to every faithful
completion. Cancelling the endpoint order transfers the full extension
order bound to each native coset orbit. These local counting arguments do
not require the native parabolic generation theorem or odd outer degree.

Source: the counting part of Aschbacher–Smith F.4.6,13,24,
printed pp.276–280 and287. The actual PSU₅(4) application is in FiveCensus.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry.RankTwo
variable {B : Type*} [Group B] [Finite B] {P₀ P₁ : Subgroup B}
variable (E : SourceExtension P₀ P₁)
variable {M : Type*} [Group M]
variable (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))

omit [Finite B] in
private theorem completion_endpoint_card (i : Bool) :
    Nat.card (c.cosetFamily i) = Nat.card (E.family i) := by
  cases i
  · exact c.left_card.trans (Nat.card_congr
      (subgroupOfEquivOfLe E.left_le).toEquiv).symm
  · exact c.right_card.trans (Nat.card_congr
      (subgroupOfEquivOfLe E.right_le).toEquiv).symm

omit [Finite B] in
private theorem completion_intersection_card
    (ho : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) :
    Nat.card (c.cosetFamily (!i) ⊓ c.cosetFamily i : Subgroup M) =
      Nat.card (E.family (!i) ⊓ E.family i : Subgroup E.carrier) := by
  have hc : Nat.card (c.cosetFamily (!i) ⊓ c.cosetFamily i : Subgroup M) = Nat.card E.middle := by
    cases i
    · change Nat.card (c.right.range ⊓ c.left.range : Subgroup M) = _
      rw [inf_comm,ho,c.middle_card]
    · change Nat.card (c.left.range ⊓ c.right.range : Subgroup M) = _
      rw [ho,c.middle_card]
  have he : (E.family (!i) ⊓ E.family i : Subgroup E.carrier) = E.middle.subgroupOf E.carrier := by
    cases i
    · exact (inf_comm _ _).trans (comap_inf E.left E.right E.carrier.subtype).symm
    · exact (comap_inf E.left E.right E.carrier.subtype).symm
  rw [he]
  exact hc.trans (Nat.card_congr (subgroupOfEquivOfLe
    (show E.middle ≤ E.carrier from inf_le_left.trans E.left_le)).toEquiv).symm

theorem completion_card_neighbors_eq_native_of_finite
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (ho : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) :
    Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily i)) =
      Nat.card ((graph (nativeFamily (P₀ := P₀) (P₁ := P₁))).neighborSet
        (base (nativeFamily (P₀ := P₀) (P₁ := P₁)) i)) := by
  apply Eq.trans _ (E.card_neighbors_eq_native hi i)
  rw [card_neighbor_base,card_neighbor_base]
  have hc := ((c.cosetFamily (!i)).subgroupOf (c.cosetFamily i)).card_mul_index
  have he := ((E.family (!i)).subgroupOf (E.family i)).card_mul_index
  rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,
    completion_intersection_card E c ho i, completion_endpoint_card E c i] at hc
  rw [← inf_subgroupOf_right, Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv] at he
  rw [inf_subgroupOf_right] at hc he
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (E.family (!i) ⊓ E.family i : Subgroup E.carrier)))
    (hc.trans he.symm)

theorem completion_card_coset_le_native_of_finite
    (hi : Function.Injective (MulAut.conj : B →* MulAut B))
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    Nat.card (M ⧸ c.cosetFamily i) ≤
      Nat.card (B ⧸ nativeFamily (P₀ := P₀) (P₁ := P₁) i) := by
  rw [← E.card_coset_eq_native hi i, ← index_eq_card, ← index_eq_card]
  apply Nat.le_of_mul_le_mul_right _ (Nat.card_pos (α := E.family i))
  calc
    (c.cosetFamily i).index * Nat.card (E.family i) = Nat.card M := by
      rw [← completion_endpoint_card E c i,index_mul_card]
    _ ≤ Nat.card E.carrier := horder
    _ = (E.family i).index * Nat.card (E.family i) := (E.family i).index_mul_card.symm

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.SourceExtension
