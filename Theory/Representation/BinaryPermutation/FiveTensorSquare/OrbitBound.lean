module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.SylowAction

/-!
# Orbit bounds for elementary actors on the deleted tensor square

Burnside’s formula reduces the strict ratio bound to three small counts in
D₈ wr C₂. Every nonidentity involution fixes at most eight points; all
involutions together contribute only 28 fixed points beyond the uniform
bound four. These estimates cover all possible elementary ranks at once.

Source: Aschbacher--Smith D.3.7, printed pp.197–199, deleted A₅ branch.
-/

@[expose] public section
namespace BinaryPermutation.FiveTensorSquare.Small
open Representation.BinaryOffender
open scoped BigOperators
private theorem fixed_one : pointFixed 1=16 := by decide +kernel

attribute [local instance] Classical.propDecidable

private theorem square_one (A : Subgroup P) (hA : IsElementaryTwo A) (g : A) :
    (g : P)*(g : P)=1 := by
  let _ : IsElementaryAbelian 2 A := hA.2
  simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (g : P) g.property

private theorem card_le (A : Subgroup P) (hA : IsElementaryTwo A) : Nat.card A≤44 := by
  classical
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card A ≤ Fintype.card {g:P // g*g=1} :=
      Fintype.card_le_of_injective (fun g => ⟨g.val,square_one A hA g⟩)
        (fun _ _ h => Subtype.ext (congrArg (fun x:{g:P // g*g=1} => x.val) h))
    _ = 44 := by rw [Fintype.card_subtype];exact square_one_card

private theorem sum_fixed_le_eight (A : Subgroup P) (hA : IsElementaryTwo A) :
    ∑g:A,pointFixed g ≤ 8*Nat.card A+8 := by
  classical
  calc
    ∑g:A,pointFixed g ≤ ∑g:A,(8+if g=1 then 8 else 0) := by
      apply Finset.sum_le_sum
      intro g _
      by_cases hg:g=1
      · simpa only [hg,Subgroup.coe_one,ite_true,fixed_one] using (le_rfl : 16≤16)
      · simpa only [if_neg hg,Nat.add_zero] using fixed_bound g (square_one A hA g)
          (fun h => hg (Subtype.ext h))
    _ = 8*Nat.card A+8 := by simp [Finset.sum_add_distrib,Nat.card_eq_fintype_card,mul_comm]

set_option maxRecDepth 1024 in
private theorem sum_fixed_le_four (A : Subgroup P) (hA : IsElementaryTwo A) :
    ∑g:A,pointFixed g ≤ 4*Nat.card A+28 := by
  classical
  have he : ∑g:A,(pointFixed g-4)≤28 := by
    rw [←Finset.sum_subtype (s:=(A:Set P).toFinset) (by simp) (fun g=>pointFixed g-4),
      ←total_excess]
    apply Finset.sum_le_sum_of_subset
    intro g hg
    simp only [Set.mem_toFinset] at hg
    simp [square_one A hA ⟨g,hg⟩]
  calc
    ∑g:A,pointFixed g ≤ ∑g:A,(4+(pointFixed g-4)) := by
      apply Finset.sum_le_sum
      intro g _
      omega
    _ = 4*Nat.card A+∑g:A,(pointFixed g-4) := by
      simp [Finset.sum_add_distrib,Nat.card_eq_fintype_card,mul_comm]
    _ ≤ 4*Nat.card A+28 := Nat.add_le_add_left he _

private theorem burnside (A : Subgroup P) :
    ∑g:A,pointFixed g = Nat.card (MulAction.orbitRel.Quotient A Point)*Nat.card A := by
  classical
  let _ : Fintype (MulAction.orbitRel.Quotient A Point) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group A Point
  simp only [Nat.card_eq_fintype_card]
  convert h using 1
  apply Finset.sum_congr rfl
  intro g _
  rw [pointFixed,Fintype.card_subtype]
  rfl

/-- Every nontrivial elementary actor loses more than twice its rank in the sixteen-point action. -/
theorem orbit_strict (A : Subgroup P) (hA : IsElementaryTwo A) :
    2*rank A + Nat.card (MulAction.orbitRel.Quotient A Point)<16 := by
  have hc := card_le A hA
  have hr : rank A≤5 := (Nat.log_mono_right (b:=2) hc).trans (by decide)
  have hp := hA.rank_pos
  have h8 := sum_fixed_le_eight A hA
  have h4 := sum_fixed_le_four A hA
  rw [burnside,hA.card_eq_two_pow_rank] at h8 h4
  interval_cases h : rank A <;> norm_num [h] at h8 h4 ⊢ <;> omega

end BinaryPermutation.FiveTensorSquare.Small
