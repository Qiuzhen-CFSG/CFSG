module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The compatible quotient used to locate the source eight in `L`

In the p.688 branch of Aschbacher–Smith, Proposition 6.2.13, the actual
`V = O₂(M) = O₂(L)` is normal in `M`, and `M/V ≃ S₅` carries `L/V` onto
`A₅`. This interface retains the same quotient map for both assertions.
It asserts no splitting. In the source application the group parameter
below is the subgroup `M = LT` of the ambient group.

Only these quotient facts, Sylow maximality of `T`, and the order of
`U ∩ V` are needed for the containment argument. The natural `SL₂(4)`
module on `V`, needed elsewhere, is not replaced by this smaller interface.
-/

namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension

open Subgroup

/-- The genuine quotient and the image of the actual subgroup `L`, with a
common multiplicative equivalence to the symmetric-five model. -/
public structure CompatibleSymmetricFiveQuotient
    {M : Type*} [Group M] (V L : Subgroup M) [V.Normal] : Prop where
  kernel_le_layer : V ≤ L
  quotient : ∃ e : (M ⧸ V) ≃* Equiv.Perm (Fin 5),
    L.map (e.toMonoidHom.comp (QuotientGroup.mk' V)) = alternatingGroup (Fin 5)

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
