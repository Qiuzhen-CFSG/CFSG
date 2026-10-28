module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Detection.SourceAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Generation.Detection.Recognition

/-!
# Detecting the transported crossing commutator

Given the escaping transport and the source index bound, failure of crossing
produces a nonidentity involution of the marked SL₃(2) quotient whose fixed
preimage on V₀/Z_alpha has index at most two. The quotient is the literal
pullback section in M; its projection kernel acts trivially, and the critical
triple makes its whole-group action nontrivial.

The small-fixed-index recognition supplies the full fixed/moving splitting,
exact intersection and equivariant natural coordinates. It therefore gives
`SingleSection p`, contradicting the non-single-section branch. The escaping
transport and index bound remain explicit inputs for the generation assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (2), p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
open Detection
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- In the non-single-section branch, an escaping transported layer has a
commutator with V₀ ∩ Q_t not contained in Z_alpha. The source actor index is
explicit, so the earlier hypotheses used to establish that bound are unnecessary
for this detection step. -/
theorem transported_commutator_crosses [Finite M]
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (p : FlagCriticalData source geometry i)
    (hs : ¬ SingleSection p) (t : Vertex R) (ht : nu R geometry (alpha R) t)
    (g : FreeAmalgam R) (hg : act R g (alpha R) = t)
    (hescape : ¬ Z R (act R g p.middle) ≤ Q R (alpha R))
    (hindex : (Q R t).relIndex (midpointSpan p) ≤ 2) :
    ¬ ⁅Z R (act R g p.middle), midpointSpan p ⊓ Q R t⁆ ≤ Z R (alpha R) := by
  intro hvanish
  let := sourceSpan_normal p
  let := sourceDenominator_normal R
  obtain ⟨a, ha, ha2, hfixed⟩ :=
    exists_small_fixed_actor_of_non_crossing common hb p t ht g hg hescape hindex hvanish
  apply hs
  exact Recognition.singleNaturalSection_of_small_fixed_index
    source.projection source.projection_surjective (sourceSpan p) (sourceDenominator R)
    (sourceDenominator_le_sourceSpan p) (sourceSpan_quotient_elementary common early p)
    (sourceSpan_kernel_commutator_le early p) (sourceSpan_action_nontrivial common p)
    a ha ha2 hfixed

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation
