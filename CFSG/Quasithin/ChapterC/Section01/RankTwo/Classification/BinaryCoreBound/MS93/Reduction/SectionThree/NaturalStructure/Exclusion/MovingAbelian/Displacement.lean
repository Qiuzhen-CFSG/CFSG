module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Intersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Intersection.Outer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Index

/-!
# Geometric displacement for the bad moving radius

Choose a critical path, which has length four in each of the three bad
branches, and its midpoint c. The full endpoint actor X_a' displaces
V_a intersect Q_c into [X_a,X_a'], which lies in Z_a. The corresponding
intersection in P therefore maps into the actor's fixed space in the actual
moving central quotient P/Z(P), for P = Vcirc_a.
The radius-index comparison bounds that subspace's codimension by the rank
of the actor's image under the genuine marked projection G_a to SL₃(2).

The outer-extension intersection calculation retains X distinct from Z.
Every geometric premise of the quotient transfer is discharged here, and
the projection has exactly the local two-core as kernel. No triviality of
that kernel's action on P/Z(P) is assumed. Only local stabilizers are finite.

Source: Meierfrankenfeld--Stellmacher (1993), (3.8), printed p.878.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- All three bad branches give the radius-intersection bound for the full
critical endpoint actor X, including the index-two outer extension. -/
theorem radius_intersection_X (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hac : (cosetGraph R).dist a c = 2)
    (hca' : (cosetGraph R).dist c a' = 2) :
    ⁅V R a ⊓ Q R c, X R a'⁆ ≤ ⁅X R a, X R a'⁆ := by
  rcases hbad with h | h | h
  · exact splitDouble_radius_intersection_X source geometry hb h a ha a' hc c hac hca'
  · exact centralExtension_radius_intersection_X source geometry hb h a ha a' hc c hac hca'
  · exact outerExtension_radius_intersection_X source geometry hb h a ha a' hc c hac hca'

/-- The geometric displacement input to source (3.8), on the actual quotient
Vcirc_a/Z(Vcirc_a). The elementary actor has nontrivial image in SL₃(2), and
its fixed codimension is bounded by that image's rank. -/
theorem moving_projected_offender (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a) :
    letI := moving_central_quotient_elementary geometry (by omega) a ha hfixed
    ∃ (π : stabilizer R a →* SL) (A : Subgroup (stabilizer R a)),
      Function.Surjective π ∧ π.ker = (Q R a).subgroupOf (stabilizer R a) ∧
      IsElementaryAbelian 2 A ∧ A.map π ≠ ⊥ ∧
      fixedCodim (Offenders.linearize (movingQuotientAction a)) A ≤ rank (A.map π) := by
  obtain ⟨a', hc⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  have hd : (cosetGraph R).dist a a' = 4 :=
    (hc.1.trans (geometry.distance_constant a ha)).trans
      (distance_eq_four source geometry hb hbad)
  obtain ⟨t, hat, hta'⟩ := exists_adjacent_dist_sub_one R a a' (by omega)
  obtain ⟨c, htc, hca'⟩ := exists_adjacent_dist_sub_one R t a' (by omega)
  have hca' : (cosetGraph R).dist c a' = 2 := by omega
  have hac : (cosetGraph R).dist a c = 2 := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr htc)
    have h₁ := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := c)
    have h₂ := (cosetGraph_connected R).dist_triangle (u := a) (v := c) (w := a')
    omega
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hcColor : color R c = false := by
    have hn := adjacent_color_ne R htc
    cases h : color R c <;> simp_all
  have hintersection := radius_intersection_X source geometry hb hbad a ha a' hc c hac hca'
  have hindex := radius_index_le_critical_image source geometry hb hbad a ha hfixed
    a' hc c hcColor hac hca' hintersection
  exact moving_projected_offender_of_radius_bounds source geometry hb hbad a ha hfixed
    a' hc c hintersection hindex

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
