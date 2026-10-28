module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Centralizer

/-!
# The actual A₆ application of the critical-distance criterion

The source-(3.8) module estimates are separated from their graph consequences.
The proved generation and centralizer equalities allow the group-independent
criterion to give distance four, path escape and relative midpoint normality
of the critical X commutator. These are the inputs to the radius-two argument
on pp.878--879, rather than an assumption that the full S₆ image exists.

Source: MS93 (2.3) and the first paragraph of (3.8), pp.857--859 and 877.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.CriticalCriterion
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- The two module estimates used in the first paragraph of MS93 (3.8).
The auxiliary subgroup is the literal critical X commutator. -/
structure CriticalEstimates (h : SmallMSPair κ L R) (d : Replacement L R) : Prop where
  commutator : CommutatorControl d.radical (replacementGeometry h d)
  edge : ∀ a (ha : color d.radical a = false) a',
    CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha) →
    ∀ t, Adjacent d.radical a t →
      (cosetGraph d.radical).dist t a' + 1 = (cosetGraph d.radical).dist a a' →
      EdgeWitness d.radical (replacementGeometry h d) a t
        ⁅X d.radical a, X d.radical a'⁆

/-- Actual path consequences of the module estimates, before the radius-two
commutator contradiction on pp.878--879. -/
structure FourGeometry (h : SmallMSPair κ L R) (d : Replacement L R) : Prop where
  distance : replacementDistance h d = 4
  escape : Factorization.CriticalEscape d.radical (replacementGeometry h d)
  midpoint : ∀ a (ha : color d.radical a = false) a',
    CriticalPair d.radical a a' ((replacementGeometry h d).exists_critical a ha) →
    ∀ c, (cosetGraph d.radical).dist a c = 2 →
      (cosetGraph d.radical).dist c a' = 2 →
      ⁅X d.radical a, X d.radical a'⁆ ≤ stabilizer d.radical c ∧
        ((⁅X d.radical a, X d.radical a'⁆).subgroupOf (stabilizer d.radical c)).Normal

variable (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

/-- The literal A₆ application of source (2.3), including relative midpoint
normality and escape. No SL₃(2) source record or natural subgroup is used. -/
theorem fourGeometry
    (himage : (projection h e hz hn d).range = alternatingGroup (Fin 6))
    (hb : 2 < replacementDistance h d) (he : CriticalEstimates h d) :
    FourGeometry h d := by
  have hC := edgeCentralizerCondition h e hz hn d himage
  have hgen := generation h e hz hn d himage
  have hfour : replacementDistance h d = 4 := by
    obtain ⟨a', hc⟩ := criticalPair_exists d.radical (alpha d.radical)
      ((replacementGeometry h d).exists_critical (alpha d.radical) rfl)
    obtain ⟨t, hat, ht⟩ := exists_adjacent_dist_sub_one d.radical (alpha d.radical) a' (by
      rw [hc.1, (replacementGeometry h d).distance_constant (alpha d.radical) rfl]
      change 0 < replacementDistance h d
      omega)
    exact FromCentralizer.distance_eq_four d.radical hC (replacementGeometry h d) hb hgen
      he.commutator (alpha d.radical) rfl a' hc t hat ht _
        (he.edge (alpha d.radical) rfl a' hc t hat ht)
  refine ⟨hfour, FromCentralizer.criticalEscape d.radical hC (replacementGeometry h d)
    hb hgen he.commutator, ?_⟩
  intro a ha a' hc c hac hca'
  have hd : (cosetGraph d.radical).dist a a' = 4 :=
    (hc.1.trans ((replacementGeometry h d).distance_constant a ha)).trans hfour
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two d.radical a c hac
  have ht : (cosetGraph d.radical).dist t a' + 1 =
      (cosetGraph d.radical).dist a a' := by
    have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hat)
    have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hct))
    have h₁ := (cosetGraph_connected d.radical).dist_triangle (u := a) (v := t) (w := a')
    have h₂ := (cosetGraph_connected d.radical).dist_triangle (u := t) (v := c) (w := a')
    omega
  exact FromCentralizer.normal_at_second d.radical hC (replacementGeometry h d) hb hgen
    he.commutator a ha a' hc t c hat hct hac (by omega) _ (he.edge a ha a' hc t hat ht)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
