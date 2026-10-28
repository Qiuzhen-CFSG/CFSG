module

public import Theory.GroupTheory.SubgroupPartitionCounting
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Transferring the actual HS local-core span through its full kernel

An intersection of index at most two has no proper intermediate subgroup.
This puts the intersection with a local core inside the original singular
hyperplane once the latter intersection lies in the core and the whole
moved subgroup does not. The cardinal version only needs a subgroup of
half the ambient order.

Generation of the actual image lifts to containment upstairs whenever the
entire homomorphism kernel belongs to the seed. The seed, acting subgroup,
target subgroup and map are retained; no choice of a smaller kernel or a
surjectivity assumption is needed.

Source: the full-kernel local-core comparison for the original returned HS
pair in Aschbacher--Smith Section12.6.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsCoreSpanTransfer
variable {G : Type*} [Group G]

/-- A proper intermediate intersection above an index-at-most-two subgroup
equals that subgroup and therefore lies in the given hyperplane. -/
theorem inf_le_of_relIndex_le_two [Finite G]
    (W U N : Subgroup G) (hi : (W ⊓ U).relIndex W ≤ 2)
    (hWU : W ⊓ U ≤ N) (hnot : ¬ W ≤ N) : W ⊓ N ≤ U := by
  let I := W ⊓ U
  let B := W ⊓ N
  have hIB : I ≤ B := le_inf inf_le_left hWU
  have hB1 : B.relIndex W ≠ 1 := by
    intro he
    exact hnot ((relIndex_eq_one.mp he).trans inf_le_right)
  have hB0 : B.relIndex W ≠ 0 := index_ne_zero_of_finite
  have hI0 : I.relIndex B ≠ 0 := index_ne_zero_of_finite
  have hmul := relIndex_mul_relIndex I B W hIB inf_le_left
  have hI1 : I.relIndex B = 1 := by
    have hB2 : 2 ≤ B.relIndex W := by omega
    have hIpos : 1 ≤ I.relIndex B := by omega
    change I.relIndex W ≤ 2 at hi
    nlinarith
  exact (relIndex_eq_one.mp hI1).trans inf_le_right

/-- The half-order hypothesis bounds every contained subgroup's intersection
index by two; no order or commutativity assumption on W is required. -/
theorem inf_le_of_half_card_and_not_le [Finite G]
    (V W U N : Subgroup G) (hWV : W ≤ V) (hUV : U ≤ V)
    (hc : Nat.card V = 2 * Nat.card U)
    (hWU : W ⊓ U ≤ N) (hnot : ¬ W ≤ N) : W ⊓ N ≤ U := by
  have hidx : U.relIndex V = 2 := by
    have hm := relIndex_mul_card_of_le hUV
    rw [hc] at hm
    have hp : 0 < Nat.card U := Nat.card_pos
    nlinarith
  apply inf_le_of_relIndex_le_two W U N _ hWU hnot
  rw [inf_relIndex_left]
  exact (relIndex_le_of_le_right hWV (by omega : U.relIndex V ≠ 0)).trans_eq hidx

/-- Image generation lifts through the full original kernel contained in
the seed. Surjectivity and equality of the target image are unnecessary. -/
theorem le_conjugateSpanBy_of_image_le
    {B : Type*} [Group B] (q : G →* B) (seed R N : Subgroup G)
    (hk : q.ker ≤ seed)
    (hm : N.map q ≤ conjugateSpanBy (seed.map q) (R.map q)) :
    N ≤ conjugateSpanBy seed R := by
  rw [←map_conjugateSpanBy] at hm
  have hle := map_le_iff_le_comap.mp hm
  rwa [comap_map_eq_self (hk.trans (le_conjugateSpanBy seed R))] at hle

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsCoreSpanTransfer
