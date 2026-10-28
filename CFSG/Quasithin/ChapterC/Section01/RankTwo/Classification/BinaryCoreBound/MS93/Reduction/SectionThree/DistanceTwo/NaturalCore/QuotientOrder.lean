module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.QuotientOrder.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.QuotientOrder.FiniteAction

/-!
# Order of the natural distance-two core

The actual quotient core/U is elementary abelian by involution generation
and the explicit commutator containment [core,Q] ≤ U. The critical-pair
commutator gives a nonidentity involution with displacement of order at
most two on this quotient. Its faithful, fully moving SL3(2)-action then
forces order eight. Since the actual natural U has order eight, the core
has order sixty-four.

This proves the binary |V| = q⁶ conclusion of Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), natural branch of (3.6),
printed p.870, conditional only on the independently owned local
commutator containment. It assumes neither core commutativity nor a
natural marking of core/U. Final quotient construction belongs to the
parent NaturalCore/QuotientConstruction module.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The natural non-Frattini core at distance two has order 64, given the
local commutator containment needed to descend its quotient action. -/
theorem core_card_eq_sixty_four (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    (hcomm : ⁅core R (alpha R), Q R (alpha R)⁆ ≤ U R (alpha R)) :
    Nat.card (core R (alpha R)) = 64 := by
  let := QuotientOrder.factor_elementary source geometry hb hcomm
  obtain ⟨a, hinj, hfull, hact⟩ :=
    QuotientOrder.exists_faithful_full_action source geometry hb natural hlarge hcomm
  obtain ⟨t, ht, htne, hsmall⟩ :=
    QuotientOrder.exists_small_displacement source geometry hb natural a hact
  rw [QuotientOrder.core_card_eq source geometry hb natural,
    QuotientOrder.card_eq_eight_of_small_displacement a hinj hfull t ht htne hsmall]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
