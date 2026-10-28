module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.ProjectionKernel
public import Theory.SpecificGroups.PSL3.BinaryComparison

/-!
# Degree-three inputs to I.1.3–I.1.4

The ordinary linear projection kernels and the binary exceptional isomorphism
are exported here. The binary adapter sends `IsPSL G 3 2` to `IsPSL G 2 7`,
so that the degree-two universal-cover calculation applies at this endpoint.
The ordinary projection kernel is trivial there, and must not be substituted
for the universal-cover kernel.

The degree-three universality proofs, the unitary kernel calculation, and the
exceptional `PSL₃(4)` cover are separate prerequisites still to be integrated.
No multiplier table is asserted by the ordinary projection results alone.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
I.1.3(2),(6) and I.1.4(2), printed pp.407–408. The source's odd-field
parameters are restricted by A.2.3 to odd primes in the strongly quasithin
list, and by A.2.2 to powers `p^e`, `p` odd prime and `1 ≤ e ≤ 2`, in the
quasithin list. For the unitary family the parameter is the fixed-field
order, with matrices over a field of its square order.
-/

namespace CFSG.Quasithin.ChapterI.LieMultipliers.A2

/-- The binary linear endpoint belongs to the degree-two multiplier branch,
through the concrete matrix-group isomorphism, independently of field choice. -/
public theorem isPSL_two_seven_of_isPSL_three_two
    {G : Type*} [Group G] (hG : ClassicalGroup.IsPSL G 3 2) :
    ClassicalGroup.IsPSL G 2 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  rcases hG with ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  exact ⟨ZMod 7, inferInstance, inferInstance, Nat.card_zmod 7,
    ⟨e.trans (Matrix.PSL3.binaryEquivPsl2Seven F hcard)⟩⟩

end CFSG.Quasithin.ChapterI.LieMultipliers.A2
