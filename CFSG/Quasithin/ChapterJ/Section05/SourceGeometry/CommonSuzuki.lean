module
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.OrbitSource
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Twenty

/-!
# The literal common-neighbor stabilizer is Sz(2)

The original pair stabilizer is marked to the native mixed PSL₂(25) group.
Its actual common-neighbor stabilizer has the proved order20, so the native
trivial-two-core calculation and Suzuki recognition apply to its exact image.
The equivalence transports back along this same subgroup embedding.

Source: Aschbacher–Smith J.5.5(4), printed p.446.
-/

public noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
variable {G:Type*} [Group G] [Finite G] (F:Subgroup G) (q:G) (hq:q∉F)
    (hs:q•(q•basePoint F)=basePoint F) {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))

include h

/-- J.5.5(4): the actual common-neighbor stabilizer is the literal Suzuki group Sz(2). -/
theorem common_neighbor_stabilizer_equiv_suzuki
    (x:(sourceGraph F q hq hs).commonNeighbors (basePoint F) (g•basePoint F)) :
    Nonempty (stabilizer (stabilizer F (g•basePoint F)) x.val≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  obtain ⟨e⟩:=h.second_plus
  let K:=stabilizer (stabilizer F (g•basePoint F)) x.val
  have hc:Nat.card (K.map e.toMonoidHom)=20:=by
    rw [card_map_of_injective e.injective]
    exact h.common_neighbor_stabilizer_card F q hq hs x
  obtain ⟨f⟩:=Tits.Max4Outer.Mixed.twenty_equiv_suzuki (K.map e.toMonoidHom) hc
  exact ⟨(e.subgroupMap K).trans f⟩

end CFSG.Quasithin.ChapterJ.Section05.RudvalisAction
