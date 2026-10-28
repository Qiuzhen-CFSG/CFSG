module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.ComponentGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.FromCentralizer

/-!
# Reduction of the G₂ exclusion to distance four

The actual component quotient supplies conjugate generation at every edge.
Applying the proved critical-pair criterion to the local module estimates
forces distance four and transports the auxiliary subgroup's normality to
the second vertex. All groups remain in the original free holomorph; R is
only assumed to be the two-group in the original small MS pair.

Source: MS93 (2.3) and the first two paragraphs of (3.8), pp.857--859,877--878.
The local estimates and the subsequent radius-two exclusion remain explicit.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC BinaryMS.MS93 BinaryMS.MS93.NormalizerTransfer
namespace G2Reconstruction.DistanceTwo
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)

variable (h : SmallMSPair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h e

/-- Source (2.3)(b), discharged on the original relative component. -/
theorem generation : CriticalCriterion.Generation T := by
  let := relative_normal h
  let := Atlas.G2.isSimple_commutator_binary
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.core_quasisimple_of_centralCore e
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ (show K ≃* L from subgroupOfEquivOfLe le_sup_left)
        (pCore_map_iso 2 (show K ≃* L from subgroupOfEquivOfLe le_sup_left))).symm
  apply MSCentralOrbit.component_generation K T h.component (edge_two_group h) _
    (core_le_edge h)
  rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]

/-- Once the two local module estimates hold, the only distance above two
that needs exclusion is four. -/
theorem distance_four_of_localControl (hb : 2 < (geometry h).b T)
    (hloc : LocalControl h) : (geometry h).b T = 4 := by
  obtain ⟨a', hc⟩ := criticalPair_exists T (alpha T) ((geometry h).exists_critical _ rfl)
  obtain ⟨t, hat, ht⟩ := exists_adjacent_dist_sub_one T (alpha T) a' (by
    rw [hc.1, (geometry h).distance_constant (alpha T) rfl]
    change 0 < (geometry h).b T
    omega)
  obtain ⟨A, hA⟩ := hloc.auxiliary (alpha T) rfl a' hc t hat ht
  exact CriticalCriterion.FromCentralizer.distance_eq_four T (edgeCentralizer h e)
    (geometry h) hb (generation h e) hloc.commutator (alpha T) rfl a' hc t hat ht A hA

/-- The same local input gives the literal normal auxiliary subgroup at the
second vertex of any critical path, for the radius-two calculation. -/
theorem auxiliary_normal_at_second (hb : 2 < (geometry h).b T)
    (hloc : LocalControl h)
    (a : Vertex T) (ha : color T a = false) (a' : Vertex T)
    (hc : CriticalPair T a a' ((geometry h).exists_critical a ha))
    (t c : Vertex T) (hat : Adjacent T a t) (hct : Adjacent T c t)
    (hac : (cosetGraph T).dist a c = 2)
    (hpath : (cosetGraph T).dist c a' + 2 = (cosetGraph T).dist a a') :
    ∃ A, CriticalCriterion.EdgeWitness T (geometry h) a t A ∧
      A ≤ stabilizer T c ∧ (A.subgroupOf (stabilizer T c)).Normal := by
  have ht : (cosetGraph T).dist t a' + 1 = (cosetGraph T).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj T _ _).mpr (adjacent_symm T hct))
    have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected T).dist_triangle (u := t) (v := c) (w := a')
    omega
  obtain ⟨A, hA⟩ := hloc.auxiliary a ha a' hc t hat ht
  exact ⟨A, hA, CriticalCriterion.FromCentralizer.normal_at_second T
    (edgeCentralizer h e) (geometry h) hb (generation h e) hloc.commutator
    a ha a' hc t c hat hct hac hpath A hA⟩

end G2Reconstruction.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
