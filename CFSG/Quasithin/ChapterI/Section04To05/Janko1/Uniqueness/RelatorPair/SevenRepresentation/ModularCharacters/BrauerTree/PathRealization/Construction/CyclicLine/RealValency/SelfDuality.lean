module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SelfDuality

/-!
# Actual self-duality of the principal eleven-block edge modules

The supplied ordinary family is complete, and all fifteen rows are real.
Separation of conjugacy classes therefore makes every element conjugate to
its inverse. Each supplied irreducible edge representation and its
contragredient have the same trace, so irreducible trace separation in
characteristic eleven gives an actual intertwining equivalence.

This discharges the simple-edge self-duality input to Feit VII.2.24 (proof
p.303) and VII.9.2 (p.307). It applies to the literal modules of any supplied
tree, including the lift `principalBlock_rootLift b r`. The tree itself is
an explicit input, and no additional character-separation premise is needed.
The serial-module ordering, reversal and final valency bound remain with
the parent assembly.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- The complete real ordinary table forces conjugacy to inverses in the
actual ambient group. -/
public theorem ordinaryData_isConj_inv (d : OrdinaryData G) (g : G) : IsConj g g⁻¹ :=
  RealValency.isConj_inv_of_real_completeFamily d.complete (ordinaryCharacters_real d) g

/-- Each supplied principal eleven-block edge module is equivalent to its
actual contragredient. This also covers the precise compatible-root lift,
without needing the group-order or any further duality premise. -/
public theorem principalBlock_edge_selfDual (b : PrincipalBlockIdentification d)
    {L : Representation.CyclicRootLift ElevenClosure 15960}
    (t : Tree b.data.chi b.data.block 11 10 L) (e : Fin 10) :
    Nonempty ((t.rep e).Equiv (t.rep e).dual) := by
  let : Representation.IsIrreducible (t.rep e) := t.irreducible e
  exact RealValency.equiv_dual_of_isConj_inv (t.rep e) (ordinaryData_isConj_inv d)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
