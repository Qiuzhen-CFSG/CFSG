module

public import Theory.GroupAction.TernaryFusedFour.MatrixClassification.Counts
public import Theory.GroupAction.TernaryFusedFour.MatrixClassification.Obstructions
/-!
# The eligible node in the certified SL₃(3) enumeration

The exact small orders, order-four words and line-action obstructions eliminate
all nodes except node 16. The whole-group node is explicitly eliminated using
an order-four element of node 5. This sieve is applied to arbitrary subgroups
by the already proved exhaustive extension certificate in `MatrixClassification`.

Source application: Bender (1974), (4.1), p.225, citing Janko (1966), Lemma 3.1.
-/

namespace TernaryFusedFour.MatrixClassification
open Matrix Matrix.PSL3Three Matrix.PSL3Three.CertifiedEnumeration

public theorem eligible_node_eq_sixteen (i : Fin 51)
    (hfour : 4 ∣ Nat.card (node i))
    (hno : ∀ x : node i, orderOf x ≠ 4)
    (hfuse : ∀ t u : node i, orderOf t = 2 → orderOf u = 2 → IsConj t u) : i = 16 := by
  have hno' : ∀ x ∈ node i, orderOf x ≠ 4 := by
    intro x hx ho
    exact hno ⟨x, hx⟩ ((Subgroup.orderOf_mk (H := node i) x hx).trans ho)
  fin_cases i
  · exact False.elim (not_four_dvd_small_nodes 0 hfour)
  · exact False.elim (not_four_dvd_small_nodes 1 hfour)
  · exact False.elim (not_four_dvd_small_nodes 2 hfour)
  · exact False.elim (not_four_dvd_small_nodes 3 hfour)
  · exact False.elim (unfused_nodes 0 hfuse)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 0
    exact False.elim (hno' x hx ho)
  · exact False.elim (not_four_dvd_small_nodes 4 hfour)
  · exact False.elim (not_four_dvd_small_nodes 5 hfour)
  · exact False.elim (not_four_dvd_small_nodes 6 hfour)
  · exact False.elim (not_four_dvd_small_nodes 7 hfour)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 1
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 2
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 3
    exact False.elim (hno' x hx ho)
  · exact False.elim (not_four_dvd_small_nodes 8 hfour)
  · exact False.elim (not_four_dvd_small_nodes 9 hfour)
  · exact False.elim (not_four_dvd_small_nodes 10 hfour)
  · rfl
  · exact False.elim (unfused_nodes 1 hfuse)
  · exact False.elim (not_four_dvd_small_nodes 11 hfour)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 4
    exact False.elim (hno' x hx ho)
  · exact False.elim (not_four_dvd_small_nodes 12 hfour)
  · exact False.elim (not_four_dvd_small_nodes 13 hfour)
  · exact False.elim (not_four_dvd_small_nodes 14 hfour)
  · exact False.elim (not_four_dvd_small_nodes 15 hfour)
  · exact False.elim (not_four_dvd_small_nodes 16 hfour)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 5
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 6
    exact False.elim (hno' x hx ho)
  · exact False.elim (not_four_dvd_small_nodes 17 hfour)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 7
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 8
    exact False.elim (hno' x hx ho)
  · exact False.elim (unfused_nodes 2 hfuse)
  · exact False.elim (unfused_nodes 3 hfuse)
  · exact False.elim (not_four_dvd_small_nodes 18 hfour)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 9
    exact False.elim (hno' x hx ho)
  · exact False.elim (not_four_dvd_small_nodes 19 hfour)
  · exact False.elim (not_four_dvd_small_nodes 20 hfour)
  · exact False.elim (not_four_dvd_small_nodes 21 hfour)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 10
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 11
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 12
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 13
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 14
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 15
    exact False.elim (hno' x hx ho)
  · exact False.elim (unfused_nodes 4 hfuse)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 16
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 17
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 18
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 19
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 20
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, hx, ho⟩ := order_four_nodes 21
    exact False.elim (hno' x hx ho)
  · obtain ⟨x, _, ho⟩ := order_four_nodes 0
    exact False.elim (hno' x (show x ∈ (⊤ : Subgroup SL) from Subgroup.mem_top x) ho)
end TernaryFusedFour.MatrixClassification
