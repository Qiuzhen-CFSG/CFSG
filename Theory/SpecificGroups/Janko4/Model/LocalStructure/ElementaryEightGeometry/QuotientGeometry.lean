module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairKernel

/-!
# Orders of the two whole quotient rows

The four displayed permutations, including the Figure 1 pair, are independent
commuting involutions. Their sixteen products certify the exact row order.
Source: Kleidman--Wilson (1988), Figures 1/2 and Propositions 2.3.4--2.3.5.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Cardinality KernelCount Subgroup

private theorem whole_square (r : Fin 2) (j : Fin 4) :
    pairRowGenerator (r.castLE (by decide)) j * pairRowGenerator (r.castLE (by decide)) j = 1 := by
  apply Subtype.ext
  revert r j
  decide +kernel

private theorem whole_commute (r : Fin 2) (i j : Fin 4) :
    Commute (pairRowGenerator (r.castLE (by decide)) i)
      (pairRowGenerator (r.castLE (by decide)) j) := by
  apply Subtype.ext
  revert r i j
  decide +kernel

theorem pairRow_binaryProduct_injective (r : Fin 2) :
    Function.Injective (binaryProduct (pairRowGenerator (r.castLE (by decide)))) := by
  have h : ∀ r : Fin 2, Function.Injective (fun v : Fin 4 → Bool =>
      (binaryProduct (pairRowGenerator (r.castLE (by decide))) v).val) := by decide +kernel
  intro v w hvw
  exact h r (congrArg Subtype.val hvw)

theorem unprimed_pairRow_card (r : Fin 2) :
    Nat.card (pairRowImage (r.castLE (by decide))) = 16 :=
  card_closure_binaryProduct _ (whole_square r) (whole_commute r) (pairRow_binaryProduct_injective r)

end Janko4.LocalStructure.ElementaryEightGeometry
