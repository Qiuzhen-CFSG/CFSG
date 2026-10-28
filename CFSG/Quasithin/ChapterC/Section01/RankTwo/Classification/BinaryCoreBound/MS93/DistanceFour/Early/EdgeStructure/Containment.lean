module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.OrbitSpan
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Terminal

/-!
# MS93 edge containment at critical distance four

If every neighboring displacement lies in B_alpha, the characteristic
transfer (4.2)(i) proves [Z_alpha,Q_beta] <= Z_beta. Otherwise an escaping
neighbor yields actual paired conjugate spans. Their abelianness and the
radius-image bound give the literal intersection index
[Z_alpha : Z_alpha intersection Z_e] = 2. The terminal fixed-line argument
then gives a contradiction.

`edge_containment` assembles (4.6.4) from the local source, common geometry,
critical distance four and InitialFacts, discharging the paired-index premise
of the retained conditional helper. The complete EdgeFacts assembly remains
with the EdgeStructure module.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.2)(i) and (4.6.4), printed pp.882 and 902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Branch assembly with the paired-index argument explicit. A bad neighbor
supplies a paired path with intersection index two; otherwise the neighboring
displacement transfer applies. `edge_containment` discharges this premise. -/
theorem edge_containment_of_paired_indices
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4)
    (hindices : ∀ (a b d : Vertex R) (ha : color R a = false),
      Adjacent R a b → Adjacent R d b →
      ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a) →
      ∃ p : SpanOffender.PairedSpans geometry a b d ha,
        (Z R p.e).relIndex (Z R a) = 2)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a,Q R b⁆ ≤ Z R b := by
  classical
  by_cases hB : ∀ d, Adjacent R d b → ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)
  · exact Transfer.edge_transfer R common hb initial a b ha hab hB
  · push Not at hB
    obtain ⟨d,hdb,hbad⟩ := hB
    obtain ⟨p,hi⟩ := hindices a b d ha hab hdb hbad
    exact Terminal.edge_containment_of_paired_index common initial hb a b d ha hab p hi

/-- MS93 (4.6.4): at critical distance four, every edge displacement
[Z_alpha,Q_beta] lies in Z_beta. The paired critical path and its literal
Z-intersection index are constructed from the authorized initial facts;
no additional span, index or edge-containment premise remains. -/
theorem edge_containment
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    ⁅Z R a,Q R b⁆ ≤ Z R b :=
  edge_containment_of_paired_indices common initial hb
    (RadiusIntersection.paired_index_witness common initial hb) a b ha hab

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
