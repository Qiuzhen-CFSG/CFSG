module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.EdgeRealness
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.DualityOrder

/-!
# Real edge characters of the principal eleven-block tree

All ordinary rows of the supplied block are real. Injectivity of the literal
tree incidence map therefore proves realness of every actual edge character,
with the same root lift as in its decomposition identities. This supplies
the realness input to Feit VII.2.24; realness alone does not bound valency.

The second theorem records the finite-cycle deduction once the genuine
serial-module cyclic ordering and duality action have been constructed.
Their existence is not asserted here. Final discharge of those earlier-source
obligations, and hence the valency bound without an ordering premise, remains
with this module's assembly. Sources: Feit VII.2.20, VII.2.23--24 (pp.280,
302--303) and VII.9.2 (p.307).
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- All ten supplied simple edge representations have real Brauer values on
actual eleven-regular elements, using the tree's literal root correspondence. -/
public theorem principalBlock_edge_characters_real (b : PrincipalBlockIdentification d)
    {L : Representation.CyclicRootLift ElevenClosure 15960}
    (t : Tree b.data.chi b.data.block 11 10 L) (e : Fin 10)
    (g : G) (hg : ¬11 ∣ orderOf g) :
    star (L.value (t.rep e) g) = L.value (t.rep e) g :=
  t.edge_value_real (fun v g => principalBlock_characters_real b v.val (ConjClasses.mk g)) e g hg

/-- The bound follows from a constructed local duality order. This theorem
retains that additional premise; it is not the completed source bound. -/
public theorem principalBlock_incident_card_le_two_of_dualityOrder
    (b : PrincipalBlockIdentification d)
    {L : Representation.CyclicRootLift ElevenClosure 15960}
    (t : Tree b.data.chi b.data.block 11 10 L) (v : {i // i ∈ b.data.block})
    (o : RealValency.LocalDualityOrder t v) : (t.incident v).card ≤ 2 :=
  o.incident_card_le_two (fun e g hg => principalBlock_edge_characters_real b t e.val g hg)

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
