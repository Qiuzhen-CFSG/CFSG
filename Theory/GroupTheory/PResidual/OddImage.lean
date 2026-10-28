module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.Index

/-!
# Two-residual images in odd quotients

A homomorphism to a finite group of odd order has the same image on C and
O²(C). Thus adjoining the kernel gives equal indices. This is the residual
step in the Borel calculation of Aschbacher–Smith 13.6.6, printed pp.927–928.
-/

public section
namespace Subgroup
variable {B A : Type*} [Group B] [Finite B] [Group A]

/-- Passing to the two-residual does not change an odd image. -/
theorem embedded_twoResidual_map_eq_of_odd (q : B →* A) (hA : Odd (Nat.card A))
    (C : Subgroup B) : ((pResidual 2 C).map C.subtype).map q = C.map q := by
  rw [map_embedded_pResidual]
  have hr : pResidual 2 (C.map q) = ⊤ := by
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    exact hA.coprime_two_left.of_dvd_right
      ((_root_.orderOf_dvd_natCard x).trans (card_subgroup_dvd_card _))
  rw [hr, ← MonoidHom.range_eq_map, range_subtype]

/-- The actual residual has the same index after adjoining an odd quotient's kernel. -/
theorem embedded_twoResidual_sup_ker_index (q : B →* A) (hq : Function.Surjective q)
    (hA : Odd (Nat.card A)) (C : Subgroup B) :
    ((pResidual 2 C).map C.subtype ⊔ q.ker).index = (C ⊔ q.ker).index := by
  have h := congrArg Subgroup.index (embedded_twoResidual_map_eq_of_odd q hA C)
  simpa only [index_map, q.range_eq_top_of_surjective hq, index_top, mul_one] using h

end Subgroup
