module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.DistanceFour

/-!
# MS93 (2.3): the critical-distance-four criterion

On the actual infinite free-amalgam graph, printed hypotheses (b)--(d)
and b > 2 imply b = 4 and relative normality of the given edge witness at
the second vertex of a critical path. The conclusion retains its containment
in that vertex group.

The generation premise is at the given edge, using only vertex-group
conjugates. Condition (c) keeps its far-endpoint witness and its literal
Frattini condition. Condition (d) supplies one subgroup; its transports are
constructed in the proof, without assuming an additional covariant family.
The intermediate escape theorem is proved within this argument from (b)--(c).

This is the conditional criterion. Verification of its module hypotheses,
source 3.8, and the unconditional natural-structure theorem remain with the
natural-structure development.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.3), printed pp.857--859.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
open NormalizerTransfer CriticalCriterion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Source (2.3), with the printed premises and the actual local normality. -/
theorem source_2_3 (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t c : Vertex R) (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hac : (cosetGraph R).dist a c = 2)
    (hpath : (cosetGraph R).dist c a' + 2 = (cosetGraph R).dist a a')
    (hgen : ∀ x ∈ Q R t, x ∉ Q R a →
      conjugatesIn (zpowers x) (stabilizer R a) ⊔ Q R t = stabilizer R a)
    (hcomm : CommutatorControl R geometry)
    (A : Subgroup (FreeAmalgam R)) (hA : EdgeWitness R geometry a t A) :
    geometry.b R = 4 ∧ A ≤ stabilizer R c ∧
      (A.subgroupOf (stabilizer R c)).Normal := by
  have hg := Generation.of_edge R a t ha hat hgen
  have hta' : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct))
    have h₁ := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected R).dist_triangle (u := t) (v := c) (w := a')
    omega
  exact ⟨distance_eq_four R source geometry hb hg hcomm a ha a' hc t hat hta' A hA,
    normal_at_second R source geometry hb hg hcomm a ha a' hc t c hat hct hac hpath A hA⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
