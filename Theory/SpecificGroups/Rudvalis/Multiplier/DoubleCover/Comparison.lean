module

public import Theory.SpecificGroups.Rudvalis.Multiplier.DoubleCover
public import Theory.SpecificGroups.Rudvalis.Multiplier

/-!
# Applying the concrete Rudvalis double cover to the multiplier comparison

The constructed cover discharges the lower-bound input of
`kernel_equiv_two_of_primary_bound_and_double_cover` for the literal Rudvalis
model. Only the independent two-primary upper bound remains explicit. Thus
any chosen universal covering has cyclic kernel of order two once that bound
is supplied. The construction of the double cover uses no such bound.

Source: Aschbacher–Smith I.1.3(1), printed p.407. Final discharge of the upper
bound and the exact multiplier theorem remain with `Multiplier.lean`.
-/

namespace Rudvalis.Multiplier.DoubleCover
open PerfectCentralCovering Theory.GroupTheory

/-- The concrete cover supplies the entire lower-bound input of I.1.3(1). -/
public theorem kernel_equiv_two_of_primary_bound
    [IsQuasisimple Rudvalis.Model]
    {U : Type} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Rudvalis.Model) (hf : Covering.IsUniversal.{0,0,0} f)
    (hfour : ¬ 4 ∣ Nat.card (universalProjection Rudvalis.Model).ker) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 2)) :=
  kernel_equiv_two_of_primary_bound_and_double_cover f hf hfour covering kernel_card_two

end Rudvalis.Multiplier.DoubleCover
