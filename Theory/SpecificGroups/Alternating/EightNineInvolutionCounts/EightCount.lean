module

public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.EightTable
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.CountFormula
public import Theory.SpecificGroups.Alternating.EightNineInvolutionCounts.ComputablePredicates

/-!
# The 8-point mixed-pair count

The complete centralizer table leaves 25 four-transposition and 18
double-transposition involutions. The kernel checks each product order by
checking its defining power and every smaller positive power, then checks the
half-order equation. Summing the 25 disjoint rows gives 156 ordered pairs.
The order data use four bits per entry; all entries are at most twelve.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3, p.38.
-/

namespace alternatingGroup.EightNineInvolutionCounts.Eight
open Equiv Equiv.Perm
open Theory.GroupTheory.TwoInvolutionClassOrder

private def productOrderData (i : Fin 25) : ℕ :=
  #[1259288123423068537890, 1259288123423068537890, 1298487456916165781026, 1259288123423068537890, 1259288123423068537890, 1298487456916165781026, 1259153611240163779140, 1259153611240163779140, 1298353540531124314726, 1259153611240163779140, 1259153611240163779140, 1298353540531124314726, 629802587249864492100, 629802587249864492100, 629803187720652220006, 629802587249864492100, 629802587249864492100, 629803187720652220006, 1298353540531124314726, 1298353540531124314726, 1298487456916165781026, 1298487456916165781026, 629803187720652220006, 629803187720652220006, 629648864382619361826][i.val]!

private def productOrder (i : Fin 25) (j : Fin 18) : ℕ :=
  (productOrderData i >>> (4 * j.val)) % 16

private theorem productOrder_check : ∀ (i : Fin 25) (j : Fin 18),
    0 < productOrder i j ∧
    (perm (zIndex i) * perm (tIndex j)) ^ productOrder i j = 1 ∧
    ∀ m : Fin (productOrder i j), 0 < m.val →
      (perm (zIndex i) * perm (tIndex j)) ^ m.val ≠ 1 := by
  decide +kernel

private theorem productOrder_eq (i : Fin 25) (j : Fin 18) :
    orderOf (perm (zIndex i) * perm (tIndex j)) = productOrder i j :=
  orderOf_eq_of_finite_check _ _ (productOrder_check i j).1
    (productOrder_check i j).2.1 (productOrder_check i j).2.2

private def rowCount (i : Fin 25) : ℕ :=
  #[4, 4, 9, 4, 4, 9, 4, 4, 9, 4, 4, 9, 4, 4, 9, 4, 4, 9, 9, 9, 9, 9, 9, 9, 0][i.val]!

private theorem rowCount_correct : ∀ i : Fin 25,
    (Finset.univ.filter (fun j : Fin 18 =>
      (perm (zIndex i) * perm (tIndex j)) ^ (productOrder i j / 2) =
        (z8 : Perm (Fin 8)))).card = rowCount i := by
  decide +kernel

/-- The actual ambient alternating-group mixed-pair count. -/
public theorem kappa_eq : kappa z8 t8 z8 = 156 := by
  rw [kappa_eq_sum z8 t8 z8 z8_order t8_order z8_not_conjugate_t8
    zClassEquiv tClassEquiv
    (fun i j => (perm (zIndex i) * perm (tIndex j)) ^ (productOrder i j / 2) =
      (z8 : Perm (Fin 8)))
    (fun i j => halfOrder_eq_iff_of_order _ _ _ _ (productOrder_eq i j))]
  simp only [rowCount_correct]
  decide +kernel

end alternatingGroup.EightNineInvolutionCounts.Eight
