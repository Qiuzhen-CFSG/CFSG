module

public import Theory.SpecificGroups.HaradaNorton.Order.LocalSubgroup
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic.NormNum

/-!
# Order assembly for the fixed Harada–Norton matrix group

The concrete subgroup defined by the ATLAS word program has been identified
with `A₁₂` in `Order.LocalCard`, using checked matrix relations and Suzuki's
presentation. Its proved cardinality is 239500800. Lagrange's equality now
reduces the exact order of HN to the single remaining index obligation 1140000.

The index is not inferred from the ATLAS label or from an external orbit
enumeration. The unconditional theorem `card_HN` still requires a certificate
of this index for the fixed matrix carrier. The equivalence below records
that this is precisely the remaining mathematical obligation.

Source of the proposed subgroup and factors:
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/HNG1-max1W1 .
-/

namespace HaradaNorton.OrderCertificate

/-- Lagrange's equality for the actual word subgroup of the fixed matrix group. -/
public theorem card_HN_eq :
    Nat.card HN = Nat.card localSubgroup * localSubgroup.index :=
  localSubgroup.card_mul_index.symm

/-- Assembly from the two concrete counts; both hypotheses require proofs. -/
public theorem card_HN_of_local_counts
    (hCard : Nat.card localSubgroup = 239500800)
    (hIndex : localSubgroup.index = 1140000) :
    Nat.card HN = 273030912000000 := by
  rw [card_HN_eq, hCard, hIndex]

/-- The independent abstract alternating group has the required local order. -/
public theorem card_alternating_twelve :
    Nat.card (alternatingGroup (Fin 12)) = 239500800 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num [Nat.factorial]

/-- A concrete equivalence with `A₁₂` suffices for the local cardinality input. -/
public theorem localSubgroup_card_of_equiv
    (e : localSubgroup ≃* alternatingGroup (Fin 12)) :
    Nat.card localSubgroup = 239500800 :=
  (Nat.card_congr e.toEquiv).trans card_alternating_twelve

/-- Lagrange's equality with the now-certified local subgroup order. -/
public theorem card_HN_eq_local_index :
    Nat.card HN = 239500800 * localSubgroup.index := by
  rw [card_HN_eq, localSubgroup_card]

/-- The concrete local index is the only remaining input for order assembly. -/
public theorem card_HN_of_local_index (hIndex : localSubgroup.index = 1140000) :
    Nat.card HN = 273030912000000 :=
  card_HN_of_local_counts localSubgroup_card hIndex

/-- The requested order and the remaining local-index certificate are equivalent. -/
public theorem card_HN_iff_local_index :
    Nat.card HN = 273030912000000 ↔ localSubgroup.index = 1140000 := by
  rw [card_HN_eq_local_index]
  change 239500800 * localSubgroup.index = 239500800 * 1140000 ↔ _
  exact Nat.mul_left_cancel_iff (by decide)

end HaradaNorton.OrderCertificate
