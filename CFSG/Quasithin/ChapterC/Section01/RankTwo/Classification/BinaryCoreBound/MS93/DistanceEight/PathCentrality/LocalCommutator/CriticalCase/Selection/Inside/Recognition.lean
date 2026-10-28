module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Action

/-!
# Assembly interface for the escaping-conjugate recognition

The local quotient, its action and the transfer of the small escaping
commutator are proved in Head and Action. Once the finite representation
argument transfers displacement from escaping conjugates to the full carrier,
small-involution recognition and quotient correspondence construct every
clause of the marked natural section.

The local marked configuration, faithfulness, and the full-displacement
transfer remain explicit here. Their proofs are needed before this can be
used as the hrecognition premise of Inside's selection theorem.

Source: Meierfrankenfeld--Stellmacher (1993), (1.6), pp.845–847,
and the inside-B branch of (4.4.1)(2), p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Application of the full-displacement transfer to the actual local span.
The remaining premise is the substantive finite representation implication
of (1.6), and is not inferred merely from the escaping-span bound. -/
theorem hasNaturalSection_of_escaping_transfer (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (hfaithful : Function.Injective (spanHeadAction source geometry a c hc))
    (d : EscapingConfiguration (spanHeadAction source geometry a c hc))
    (htransfer : actionDisplacement (spanHeadAction source geometry a c hc)
      (zpowers d.involution) ⊤ ≤
      actionDisplacement (spanHeadAction source geometry a c hc) (zpowers d.involution)
        (actionEscapingSpan (spanHeadAction source geometry a c hc)
          (markedPointStabilizer d.marking d.point) d.involution d.seed)) :
    HasNaturalSection R a c := by
  apply hasNaturalSection_of_spanHead_small_involution source geometry hb hc hd htriple hfaithful
  refine ⟨d.involution, d.involution_ne_one, d.involution_sq, ?_⟩
  have hh := (card_le_of_le htransfer).trans d.small
  rwa [actionDisplacement_top, MonoidHom.map_zpowers] at hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
