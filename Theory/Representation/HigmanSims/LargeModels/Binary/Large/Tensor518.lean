module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Assembly
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorA
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.GeneratorB
public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank

/-!
# Tensor construction for the marked degree-518 HS model

The actual tensor of the marked degree-20 and degree-56 actions has dimension
1120, with the degree-56 coordinate varying fastest. The checked generator
identities preserve the annihilator of the 21 kernel rows and intertwine its
action with the literal degree-518 matrices through the 518 lift rows. The
checked pivot inverse makes that map surjective, so annihilator-quotient descent
constructs the marked degree-518 action on the literal HS carrier.

All numerical premises are discharged here. Only the marked degree-20
comparison and degree-56 action remain inputs; absolute irreducibility is a
separate matrix-algebra calculation.

Source and certificate status: `Tensor518/source/README.md`.
-/

public section

namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518

/-- The marked degree-518 HS action obtained from the actual tensor of the
marked degree-20 and degree-56 actions, with every section certificate proved. -/
theorem markedAction
    (h20 : Nonempty Sporadic.LeechRelated.HS.Twenty.MarkedComparison)
    (C56 : MarkedAction 0) : Nonempty (MarkedAction 2) :=
  markedAction_of_certificates h20 C56 kernel_a kernel_b lift_a lift_b pivot_inverse

end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518
