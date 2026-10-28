module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SpanAction.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SpanAction.Duality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SpanAction.FFBound

/-!
# Construction of the paired spans' central quotient actions

One of the paired spans has a faithful self-dual FF action on its literal
quotient W/Z(W). The local projection, its exact kernel Q, the conjugation
equation and faithfulness come from `Basic`. Each derived subgroup is the
specified central displacement of order two, so `Duality` supplies the
invariant nondegenerate commutator pairing without restricting the whole center.

The comparison in `FFBound` selects an orientation in which the actual
opposite-span projection image is an offender. Assembling these facts fills
every field of `SpanQuotientAction`. The source-hypothesis wrapper also
constructs the paired spans from the escaping neighbor. The independent
FF exclusion and the full radius-offender theorem belong to the consumer.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.4), printed p.902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- In a favorable orientation, the actual nonabelian span modulo its center
carries the faithful self-dual FF action of its local SL₃(2) quotient. -/
theorem pairedSpanQuotientActions_nonempty (common : CommonFacts R source geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (p : PairedSpans geometry a b d ha)
    (hnon : ¬ IsMulCommutative (neighborSpan a d)) :
    Nonempty (SpanQuotientAction a (neighborSpan a d)) ∨
      Nonempty (SpanQuotientAction p.e (neighborSpan p.e p.r)) := by
  obtain ⟨c1, c0⟩ := pairedSpanCentralActions_nonempty common a b d ha hab hdb p hnon
  obtain ⟨hd1, hd0⟩ := p.derived_eq_displacement common hab hdb hnon
  obtain ⟨h1, h0, _, _⟩ := p.span_kernel_containments common hab hdb
  let := c1.elementary
  let := c0.elementary
  rcases pairedSpanCentralActions_isFFModule common a b d ha hab hdb p c1 c0 with h | h
  · exact Or.inl ⟨{ c1 with
      selfDual := c1.selfDual (h1.trans (fun _ hx => hx.1))
        (by rw [hd1]; exact p.card_left) (by rw [hd1]; exact p.central_left)
      offending := h }⟩
  · exact Or.inr ⟨{ c0 with
      selfDual := c0.selfDual (h0.trans (fun _ hx => hx.1))
        (by rw [hd0]; exact p.card_right) (by rw [hd0]; exact p.central_right)
      offending := h }⟩

/-- Construct the paired spans and the favorable central-quotient action from
the escaping-neighbor hypotheses of the nonabelian branch of MS93 (4.6.4). -/
theorem escaping_neighbor_spanQuotientAction_nonempty
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (hnon : ¬ IsMulCommutative (neighborSpan a d)) :
    ∃ p : PairedSpans geometry a b d ha,
      Nonempty (SpanQuotientAction a (neighborSpan a d)) ∨
        Nonempty (SpanQuotientAction p.e (neighborSpan p.e p.r)) := by
  obtain ⟨p⟩ := pairedSpans_nonempty common initial hb a b d ha hab hdb hbad
  exact ⟨p, pairedSpanQuotientActions_nonempty common a b d ha hab hdb p hnon⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
