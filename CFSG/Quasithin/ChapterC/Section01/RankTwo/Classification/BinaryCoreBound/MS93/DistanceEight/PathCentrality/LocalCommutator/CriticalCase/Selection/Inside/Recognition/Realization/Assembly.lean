module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization.Point
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization.Faithfulness

/-!
# The faithful marked escaping configuration on the local head

The point xD_c has a nonzero lift in the earlier natural subgroup U_c.
Its marked stabilizer has precisely the literal relative normalizer K as
preimage. The image of the K-span therefore gives the invariant generating
seed. A nonidentity involution in the projected endpoint supplies the
escaping action, whose displacement bound follows from the source bound.
The escaping commutator and the triple bound independently prove faithfulness
on H/(Z_c[H,Q_c]), where H is the G_c-conjugate span of Z_a.

The first theorem retains the point, seed and endpoint identifications; the
second supplies exactly the two realization inputs of
`hasNaturalSection_of_escaping_transfer`. The independent finite representation
implication and final natural-section recognition remain with that consumer's
owner. Since placement of x in Z_c D_c is supplied, the earlier inside-B bound
is not needed again in this construction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.6), printed pp.845--847, applied in (4.4.1)(2), printed p.891.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Realize the actual quotient point and source seed in the faithful local
head, retaining the projected endpoint containing the chosen involution. -/
theorem exists_faithful_marked_escapingConfiguration (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c e : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (x : stabilizer R c)
    (hx : (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆)
    (hxD : (x : FreeAmalgam R) ∉ fixedCore R c)
    (hxZ : (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (hsmall : (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2) :
    Function.Injective (spanHeadAction source geometry a c hc) ∧
      ∃ point : LocalPointMarking source c hc x,
      ∃ d : EscapingConfiguration (spanHeadAction source geometry a c hc),
        d.marking = point.naturalU.marking ∧
        d.point = (point.naturalU.coordinates point.lift).toAdd ∧
        d.seed = spanHeadImage geometry a c (normalizerSpan a c x) ∧
        d.involution ∈ ((Z R e).subgroupOf (stabilizer R c)).map
          (localProjection source c hc) := by
  refine ⟨spanHeadAction_injective_of_escaping source geometry hb ha hc hd x hx hxD htriple, ?_⟩
  obtain ⟨point⟩ := localPointMarking_nonempty source geometry common hc x hxD hxZ
  exact ⟨point, escapingConfiguration_of_pointNormalizer source geometry common hb hc hd p x
    point.naturalU.marking (point.naturalU.coordinates point.lift).toAdd
    point.nonzero point.normalizer hsmall⟩

/-- Both local realization premises of the escaping-transfer consumer follow
from the source inputs, with no marking or faithfulness assumption remaining. -/
theorem faithful_escapingConfiguration_of_source (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c e : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (x : stabilizer R c)
    (hx : (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆)
    (hxD : (x : FreeAmalgam R) ∉ fixedCore R c)
    (hxZ : (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (hsmall : (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2) :
    Function.Injective (spanHeadAction source geometry a c hc) ∧
      Nonempty (EscapingConfiguration (spanHeadAction source geometry a c hc)) := by
  obtain ⟨hfaithful, point, d, _⟩ := exists_faithful_marked_escapingConfiguration
    source geometry common hb ha hc hd p x hx hxD hxZ htriple hsmall
  exact ⟨hfaithful, ⟨d⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
