module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.OrbitClique
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Realization.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Dual

/-!
# The inside-B conjugate in MS93 (4.4.1)

Construct the faithful marked action on the literal local span head. The
binary escaping-seed theorem transfers its displacement bound to the full
head, yielding a natural section. In the nonnatural branch this excludes
containment of the escaping span, so one actual local conjugator has both
required critical and triple-commutator noncontainments.

No representation-recognition callback remains: the point, kernel, action,
faithfulness and displacement transfer are all instantiated on the original
free-amalgam subgroups and quotient maps.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.6), pp.845--847, applied in (4.4.1)(2), printed p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase.Inside LocalCommutator.CriticalCase.Inside.Recognition
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

 theorem hasNaturalSection_of_escaping_bound
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hd : (cosetGraph R).dist a c=2) (p : CriticalPath R geometry c e)
    (x : stabilizer R c)
    (hx : (x : FreeAmalgam R)∈⁅Z R a,Q R c⁆)
    (hxD : (x : FreeAmalgam R)∉fixedCore R c)
    (hxZ : (x : FreeAmalgam R)∈Z R c⊔fixedCore R c)
    (htriple : ⁅⁅localZSpan R a c,Q R c⁆,Ltilde R c⁆≤Z R c)
    (hsmall : (Z R c).relIndex ⁅escapingSpan a c e x,Z R e⁆≤2) :
    HasNaturalSection R a c := by
  let := spanHead_elementary geometry hb hc hd.le
  obtain ⟨hf,⟨d⟩⟩ := faithful_escapingConfiguration_of_source source geometry common hb
    ha hc hd p x hx hxD hxZ htriple hsmall
  exact hasNaturalSection_of_escaping_transfer source geometry hb hc hd htriple hf d
    (OrbitClique.displacement_transfer _ hf d)

 theorem inside_conjugate
    (common : CommonFacts R source geometry) (hb : 4 < geometry.b R)
    {a c e : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hd : (cosetGraph R).dist a c=2)
    (hB : ⁅Z R a,Q R c⁆≤B R c (geometry.Z_normal c))
    (hn : ¬⁅Z R a,Q R c⁆≤fixedCore R c)
    (hnone : ¬HasNaturalSection R a c)
    (htriple : ⁅⁅localZSpan R a c,Q R c⁆,Ltilde R c⁆≤Z R c)
    (p : CriticalPath R geometry c e) :
    ∃g∈stabilizer R c,
      ¬Z R (act R g a)≤Q R (p.walk.getVert (p.walk.length-2)) ∧
      ⁅⁅Z R (act R g a),Q R c⁆,Z R e⁆≠⊥ := by
  apply exists_conjugate_of_escaping_recognition common hb ha hc hd hB hn hnone htriple p
  intro x hx hxD hxZ ht hs
  exact hasNaturalSection_of_escaping_bound common hb ha hc hd p x hx hxD hxZ ht hs

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
