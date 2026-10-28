module

public import Theory.SpecificGroups.Janko3.Model
public import Theory.GroupTheory.PerfectCentralCoverKernelLowerBound
public import Theory.GroupTheory.UniversalCoverKernelTransport

/-!
# Assembling the exact J₃ multiplier from independent upper and lower bounds

The carrier is the actual degree-6156 permutation model, whose perfectness is
proved in `Model.Perfect`. A perfect central triple cover forces three to divide
the canonical universal kernel order. An independent upper bound of three
then gives a cyclic kernel of order three. Kernel comparison transports this
to any chosen universal covering and to any genuinely isomorphic source group.

These are conditional assembly theorems, not a completed multiplier
calculation. Task `qt-j3-three-primary-upper-bound` owns the full kernel bound
(including exclusion of the two-primary part), and
`qt-j3-triple-cover-lower-bound` owns the actual perfect central triple cover.
Task `qt-i01-multiplier-j3` retains their discharge and final assembly for
Aschbacher--Smith I.1.4(2), printed p.408; the table owner is
`qt-i-01-multipliers-altspor`.
-/

namespace Sporadic.Janko3.Multiplier

open PerfectCentralCovering Theory.GroupTheory

universe u v

/-- The full upper bound and an actual perfect central triple cover identify
the canonical multiplier. Both model-specific inputs remain explicit. -/
public theorem universal_kernel_equiv_three_of_bound_and_triple_cover
    (hbound : Nat.card (universalProjection Model).ker ≤ 3)
    {E : Type v} [Group E] [Finite E] (c : Cover E Model)
    (hc : Nat.card c.toMonoidHom.ker = 3) :
    Nonempty (PerfectCentralCovering.schurMultiplier Model ≃*
      Multiplicative (ZMod 3)) :=
  c.universal_kernel_equiv_of_prime_bound hc hbound

/-- Source-domain assembly for every chosen universal covering of the actual
model. The quasisimplicity hypothesis is inherited from the source group. -/
public theorem source_kernel_equiv_three_of_bound_and_triple_cover
    [IsQuasisimple Model]
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Model) (hf : Covering.IsUniversal.{0, u, 0} f)
    (hbound : Nat.card (universalProjection Model).ker ≤ 3)
    {E : Type v} [Group E] [Finite E] (c : Cover E Model)
    (hc : Nat.card c.toMonoidHom.ker = 3) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨k⟩ := universal_kernel_equiv_three_of_bound_and_triple_cover hbound c hc
  exact ⟨(schurMultiplierEquivOfUniversal (MulEquiv.refl Model) f hf).symm.trans k⟩

/-- The literal source-group application of the conditional J₃ row. The model
equivalence supplies quasisimplicity; both multiplier inputs still need proof. -/
public theorem source_schurMultiplier_equiv_three_of_model_of_bound_and_triple_cover
    {S : Type u} [Group S] [Finite S] [IsQuasisimple S]
    (e : S ≃* Model)
    (hbound : Nat.card (universalProjection Model).ker ≤ 3)
    {E : Type v} [Group E] [Finite E] (c : Cover E Model)
    (hc : Nat.card c.toMonoidHom.ker = 3) :
    Nonempty (PerfectCentralCovering.schurMultiplier S ≃*
      Multiplicative (ZMod 3)) := by
  let : IsQuasisimple Model := IsQuasisimple.of_mulEquiv e
  obtain ⟨k⟩ := universal_kernel_equiv_three_of_bound_and_triple_cover hbound c hc
  exact ⟨(schurMultiplierCongr e).trans k⟩

end Sporadic.Janko3.Multiplier
