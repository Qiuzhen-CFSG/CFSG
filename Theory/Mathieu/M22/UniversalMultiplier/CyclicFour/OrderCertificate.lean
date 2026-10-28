module

public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.OrderCertificate.Reduction
public import Theory.Mathieu.M22.UniversalMultiplier.CyclicFour.OrderCertificate.RawChecks

/-!
# Order-certificate assembly for the paired M₂₂ candidate

The checked reduction turns the literal degree-4928 transition identities into
an order bound and then exhausts the native projection kernel by the powers of
the specified central word. The finite transition certificates are still
explicit premises, so this is not yet the finished cyclic-four-cover proof.

Source application: Aschbacher–Smith I.1.1 and I.1.3(4), printed p.407.
-/

namespace Sporadic.Mathieu.M22CyclicFour
open OrderCertificate

/-- The raw first-coordinate obligations imply the bound for the actual paired group. -/
public theorem order_le_of_raw_steps
    (hz : centralWord ^ 4 = 1) (hc : centralWord ∈ Subgroup.center Model)
    (h0 : RawStep0) (h1 : RawStep1) (h2 : RawStep2) (h3 : RawStep3)
    (ht : RawTerminal) : Nat.card Model ≤ 1774080 :=
  order_le_of_lifted_steps hz hc (step0_of_raw h0) (step1_of_raw h1)
    (step2_of_raw h2) (step3_of_raw h3) (terminal_of_raw ht)

/-- Consumer on the literal native projection: the exact kernel is exhausted. -/
public theorem kernel_eq_zpowers_of_raw_steps
    (hz : orderOf centralWord = 4) (hc : centralWord ∈ Subgroup.center Model)
    (h0 : RawStep0) (h1 : RawStep1) (h2 : RawStep2) (h3 : RawStep3)
    (ht : RawTerminal) : projection.ker = Subgroup.zpowers centralWord :=
  kernel_eq_zpowers_of_order_bound hz (order_le_of_raw_steps
    (by rw [← hz]; exact pow_orderOf_eq_one _) hc h0 h1 h2 h3 ht)

/-- The same projection has cyclic-four kernel once its finite certificates hold. -/
public theorem kernel_equiv_four_of_raw_steps
    (hz : orderOf centralWord = 4) (hc : centralWord ∈ Subgroup.center Model)
    (h0 : RawStep0) (h1 : RawStep1) (h2 : RawStep2) (h3 : RawStep3)
    (ht : RawTerminal) : Nonempty (projection.ker ≃* Multiplicative (ZMod 4)) :=
  kernel_equiv_four_of_order_bound hz (order_le_of_raw_steps
    (by rw [← hz]; exact pow_orderOf_eq_one _) hc h0 h1 h2 h3 ht)

end Sporadic.Mathieu.M22CyclicFour
