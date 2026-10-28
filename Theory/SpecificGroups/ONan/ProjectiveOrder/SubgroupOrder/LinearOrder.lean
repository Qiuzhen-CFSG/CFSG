module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.SubgroupOrder.LinearOrder.Bounds

/-!
# Assembly of the linear local subgroup order

An upper bound from actual matrix word reductions and a lower bound from
independent finite subgroup certificates determine the order of the subgroup
in GL(45,7). No assumption on the projective O'Nan order or scalar kernel is
used. The concrete certificates are separate obligations; the assembly below
keeps their mathematical contracts explicit.

See `ProjectiveOrder/source/` and `refs/original/onan/` for the source words
and matrices.
-/

namespace ONan.OrderCertificate

/-- Assemble the linear order from independent upper and lower bounds. -/
public theorem linearLocalSubgroup_card_of_bounds
    (hupper : Nat.card linearLocalSubgroup ≤ 3753792)
    (hlower : 3753792 ≤ Nat.card linearLocalSubgroup) :
    Nat.card linearLocalSubgroup = 3753792 :=
  Nat.le_antisymm hupper hlower

/-- Prime-power subgroup certificates suffice for the lower bound. -/
public theorem linearLocalSubgroup_card_of_prime_power_certificates
    (hupper : Nat.card linearLocalSubgroup ≤ 3753792)
    (h2 : 64 ∣ Nat.card linearLocalSubgroup)
    (h3 : 9 ∣ Nat.card linearLocalSubgroup)
    (h7 : 343 ∣ Nat.card linearLocalSubgroup)
    (h19 : 19 ∣ Nat.card linearLocalSubgroup) :
    Nat.card linearLocalSubgroup = 3753792 :=
  linearLocalSubgroup_card_of_bounds hupper
    (linearLocalSubgroup_card_ge_of_dvd
      (linearLocalSubgroup_order_dvd_of_prime_powers h2 h3 h7 h19))

end ONan.OrderCertificate
