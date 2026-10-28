module

public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Centralizers of elements of order seven in degree nine

An element of order seven on nine points is a single seven-cycle. Its
centralizer has order fourteen, so it cannot commute with an element of
order four. This supplies the small coset-action obstruction needed in
Fong's centralizer calculation (J. Algebra 6 (1967), p.75).
-/

namespace Equiv.Perm

public theorem card_centralizer_order_seven_on_nine
    {α : Type*} [Fintype α] (hα : Fintype.card α = 9)
    (g : Perm α) (hg : orderOf g = 7) :
    Nat.card (Subgroup.centralizer ({g} : Set (Perm α))) = 14 := by
  classical
  have hc : g.IsCycle := isCycle_of_prime_order' (hg ▸ by decide) (by omega)
  rw [nat_card_centralizer, hc.cycleType, ← hc.orderOf, hg, hα]
  norm_num

public theorem not_commute_order_four_seven_on_nine
    {α : Type*} [Fintype α] (hα : Fintype.card α = 9)
    (f g : Perm α) (hf : orderOf f = 4) (hg : orderOf g = 7) : ¬ Commute f g := by
  intro hcomm
  have hd := (Subgroup.centralizer ({g} : Set (Perm α))).orderOf_dvd_natCard
    (Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq)
  rw [hf, card_centralizer_order_seven_on_nine hα g hg] at hd
  norm_num at hd

end Equiv.Perm
