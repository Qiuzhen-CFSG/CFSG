module
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.Janko1.Model.Certification.Order.Generators

/-!
# A binary degree obstruction for the actual J₁ carrier

The checked matrix word of order eleven forces eleven to divide the
actor order. The binary general-linear order formula then bounds the
degree below by the multiplicative order of two modulo eleven, namely ten.
Only this precise obstruction is needed for the rank-eight source span.

Source: Aschbacher–Smith C.5.12, printed p.163; the ATLAS matrix word is
verified in `Model.Certification.Order.Generators`.
-/
public section
namespace Janko1
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
theorem ten_le_binary_finrank (ρ : Representation (ZMod 2) Model W)
    (hi : Function.Injective ρ) : 10 ≤ Module.finrank (ZMod 2) W := by
  have hd : 11 ∣ Nat.card Model := OrderCertificate.orderOf_eleven ▸
    orderOf_dvd_natCard (OrderCertificate.x * OrderCertificate.y ^ 2)
  have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hi
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) hd
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] using hh
end Janko1
