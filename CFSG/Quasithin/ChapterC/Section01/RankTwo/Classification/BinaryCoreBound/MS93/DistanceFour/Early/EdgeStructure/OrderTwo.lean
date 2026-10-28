module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Centrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Offender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.OffenderConstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion

/-!
# The order-two exclusion in MS93 (4.6.5)

The simple marked quotient supplies the generation hypothesis (b) of (2.3).
The order-two branch supplies its literal hypotheses (c) and (d).
Relative normality at critical midpoints implies centrality there, and
generation then places the radius-derived subgroup in the actual fixed core.
Two opposite radius groups give actual actors with the required escape
and intrinsic Frattini containment. Comparing their image indices supplies
a quotient offender, contradicting the initial factorization implication
and nonabelianness of the radius group.

The only intermediate source inputs in the final exclusion are InitialFacts
and the universal edge containment from (4.6.4). All hypotheses of (2.3),
derived fixedness, and the offender index estimate are discharged here.
EdgeFacts assembly belongs to the parent EdgeStructure module.

Source: Meierfrankenfeld--Stellmacher (1993), pp.857--859 and 903.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common

/-- Apply source (2.3) to the literal order-two edge commutator. The result
retains containment and normality in the midpoint stabilizer. -/
theorem critical_edge_normal_at_midpoint (hb : geometry.b R = 4)
    (a b a' c : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hcb : Adjacent R c b)
    (hcrit : CriticalPair R a a' (geometry.exists_critical a ha))
    (hac : (cosetGraph R).dist a c = 2) (hca' : (cosetGraph R).dist c a' = 2)
    (hcard : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2) :
    ⁅Z R a, Q R b⁆ ≤ stabilizer R c ∧
      ((⁅Z R a, Q R b⁆).subgroupOf (stabilizer R c)).Normal := by
  have hcomm : CriticalCriterion.CommutatorControl R geometry := by
    intro d hd d' hcrit'
    obtain ⟨hle, hnot, hbound⟩ :=
      critical_witness_bound common a b ha hab hcard d d' hd hcrit'
    exact ⟨Z R d', hle, hnot, fun t ht Y hY _ => hbound t ht.1 ht.2 Y hY⟩
  obtain ⟨hle, hn, hnot, hbound⟩ := edge_source_d common a b ha hab hcard
  have hA : CriticalCriterion.EdgeWitness R geometry a b ⁅Z R a, Q R b⁆ := by
    refine ⟨hle, hn, hnot, ?_⟩
    intro ha' d hd hpath
    apply hbound d hd
    rwa [hd.1, geometry.distance_constant a ha']
  have hpath : (cosetGraph R).dist c a' + 2 = (cosetGraph R).dist a a' := by
    have hdist : (cosetGraph R).dist a a' = 4 :=
      (hcrit.1.trans (geometry.distance_constant a ha)).trans hb
    rw [hca', hdist]
  exact (source_2_3 source geometry (by omega) a ha a' hcrit b c hab hcb hac hpath
    (edge_element_conjugate_generation source a b ha hab) hcomm
    ⁅Z R a, Q R b⁆ hA).2

/-- Midpoint centrality from (2.3) puts every radius-derived subgroup in
the actual component-fixed core D, assuming one order-two edge. -/
theorem derived_le_fixedCore_of_order_two (hb : geometry.b R = 4)
    (a₀ b₀ : Vertex R) (ha₀ : color R a₀ = false) (he₀ : Adjacent R a₀ b₀)
    (hcard : Nat.card (⁅Z R a₀, Q R b₀⁆ : Subgroup (FreeAmalgam R)) = 2)
    (a : Vertex R) (ha : color R a = false) :
    ⁅V R a, V R a⁆ ≤ fixedCore R a := by
  apply derived_le_fixedCore_of_critical_edge_normality common hb a₀ b₀ ha₀ he₀ hcard
    ?_ a ha
  intro c d hc hcrit b e hcb heb hce hed
  have hcard' : Nat.card (⁅Z R c, Q R b⁆ : Subgroup (FreeAmalgam R)) = 2 :=
    (edge_card_eq a₀ b₀ c b ha₀ hc he₀ hcb).symm.trans hcard
  exact (critical_edge_normal_at_midpoint common hb c b d e hc hcb heb hcrit
    hce hed hcard').2

/-- The order-two alternative in source (4.6.5) is impossible, using only
the initial facts and the independent containment from (4.6.4). -/
theorem edge_commutator_card_ne_two (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry)
    (hcontain : ∀ a b, color R a = false → Adjacent R a b → ⁅Z R a, Q R b⁆ ≤ Z R b)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) ≠ 2 := by
  intro hcard
  have hfixed := derived_le_fixedCore_of_order_two common hb a b ha hab hcard
  obtain ⟨c, d, A, hc, hcd, hA, hnot, hPhi, hi⟩ :=
    exists_quotient_offender common hb initial hcontain a b ha hab hcard hfixed
  exact not_offender_of_derived_fixed common hb initial c d hc hcd (hfixed c hc)
    A hA hnot hPhi hi

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.OrderTwo
