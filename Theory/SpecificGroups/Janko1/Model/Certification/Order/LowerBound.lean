module

public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Generators
public import Theory.SpecificGroups.Janko1.Model.Certification.InvolutionFusion

/-!
# The divisibility half of the J₁ order certificate

The checked subgroup of order eight and the checked elements of orders
3, 5, 7, 11 and 19 force their least common multiple, 175560, to divide the
order of the explicit matrix group. All witnesses come from the ATLAS
matrices documented in `Model.Basic`.
-/

namespace Janko1

public theorem order_target_dvd_card : 175560 ∣ Nat.card Model := by
  have h3 : 3 ∣ Nat.card Model := orderOf_b ▸ orderOf_dvd_natCard b
  have h5 : 5 ∣ Nat.card Model :=
    OrderCertificate.orderOf_five ▸ orderOf_dvd_natCard (OrderCertificate.x * OrderCertificate.y)
  have h7 : 7 ∣ Nat.card Model := orderOf_ab ▸ orderOf_dvd_natCard (a * b)
  have h11 : 11 ∣ Nat.card Model := OrderCertificate.orderOf_eleven ▸
    orderOf_dvd_natCard (OrderCertificate.x * OrderCertificate.y ^ 2)
  have h19 : 19 ∣ Nat.card Model := orderOf_abab_sq ▸ orderOf_dvd_natCard (a * b * a * b ^ 2)
  exact (show Nat.lcm 8 (Nat.lcm 3 (Nat.lcm 5 (Nat.lcm 7 (Nat.lcm 11 19)))) = 175560
    from by decide) ▸
      Nat.lcm_dvd eight_dvd_card (Nat.lcm_dvd h3 (Nat.lcm_dvd h5
        (Nat.lcm_dvd h7 (Nat.lcm_dvd h11 h19))))

end Janko1
