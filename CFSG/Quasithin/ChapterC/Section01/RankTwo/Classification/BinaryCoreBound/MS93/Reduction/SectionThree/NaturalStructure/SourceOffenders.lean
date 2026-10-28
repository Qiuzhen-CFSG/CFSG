module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.CriticalPairs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Factorization.Offenders

/-!
# Actual source offenders without an extra centralizer premise

The binary local centralizer theorem discharges the additional hypothesis
of source 2.2. Both Z and X consequently admit actual elementary offenders,
without assuming an equality between these two layers or a module shape.

Source: Meierfrankenfeld--Stellmacher (1993), 2.2(vi), pp.856--857.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The genuine binary source supplies the centralizer hypothesis of 2.2. -/
theorem LocalSource.edgeCentralizerCondition (source : LocalSource L R)
    (geometry : Geometry R) : EdgeCentralizerCondition R :=
  source.adjacent_centralizer geometry.radical_ne_bot

/-- Both actual layer offenders, with the extra hypothesis of 2.2 discharged. -/
theorem LocalSource.factorization_offenders (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (ht : (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a') :
    Nonempty (Offenders.Witness (Q R a) (Q R t) (Z R a)) ∧
      Nonempty (Offenders.Witness (Q R a) (Q R t) (X R a)) := by
  apply MS93.factorization_offenders R geometry (source.edgeCentralizerCondition geometry)
    a ha _ a' hc t hat ht
  rw [geometry.distance_constant a ha]
  exact hb

/-- Every M-vertex has an edge supporting both literal layer offenders. -/
theorem LocalSource.exists_layer_offenders (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    ∃ t, Adjacent R a t ∧
      Nonempty (Offenders.Witness (Q R a) (Q R t) (Z R a)) ∧
      Nonempty (Offenders.Witness (Q R a) (Q R t) (X R a)) := by
  obtain ⟨a', hc⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  obtain ⟨t, hat, ht⟩ := exists_adjacent_dist_sub_one R a a' (by
    rw [hc.1, geometry.distance_constant a ha]
    exact hb)
  exact ⟨t, hat, source.factorization_offenders geometry hb a ha a' hc t hat ht⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
