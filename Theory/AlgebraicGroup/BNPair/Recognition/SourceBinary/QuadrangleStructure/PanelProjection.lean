module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootLocalCover
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions

/-!
# Agreement of the two literal root-to-panel projections

The root quotient equivalence and the root-local-cover projection both
restrict the same endpoint permutation action. This equation connects the
existing full-actor profile to the original source covering transport.

This is an intentional internal proof extension of HexagonStructure.LocalActions:
its private definition bodies are imported only to prove the public equation.
The owning module and its public boundary stay unchanged; no private name
occurs in the exported statement. The ordinary dependencies remain public.

Source: Fong--Seitz I (5C), pp.25--26, the canonical R_i to L_i projection.
-/

public section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
/-- Both existing quotient conventions give the same actual panel permutation. -/
theorem rankOneLocalEquiv_eq_projection (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) (r : rankOne Q split i) :
    rankOneLocalEquiv Q split i hV (QuotientGroup.mk r) = RootLocalCover.projection Q split i r := by
  apply Subtype.ext
  rw [rankOneLocalEquiv_apply,RootLocalCover.projection_apply]
  rfl
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
