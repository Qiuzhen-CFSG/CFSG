module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions

/-!
# Actual FF actions on the native symplectic central layers

The proved edge-centralizer condition and positive critical distance produce
literal elementary offender quotients on both Z and X. The offender on X
embeds into the actual stabilizer quotient and yields the binary FF-module
inequality on the same carrier. No irreducibility or module shape is assumed.

Source: MS93 (2.2)(vi), printed p.857, used in (3.2), p.863.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem exists_layer_offenders (a : Vertex R) (ha : color R a = false) :
    ∃ t, Adjacent R a t ∧
      Nonempty (Offenders.Witness (Q R a) (Q R t) (Z R a)) ∧
      Nonempty (Offenders.Witness (Q R a) (Q R t) (X R a)) := by
  have hb : 0 < criticalDistance R a (s.geometry.exists_critical a ha) := by
    rw [s.geometry.distance_constant a ha]
    exact s.criticalDistance_pos
  obtain ⟨a',hc⟩ := criticalPair_exists R a (s.geometry.exists_critical a ha)
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one R a a' (by rw [hc.1]; exact hb)
  exact ⟨t,hat,CFSG.Quasithin.ChapterC.BinaryMS.MS93.factorization_offenders R s.geometry
    s.edgeCentralizerCondition a ha hb a' hc t hat ht⟩

theorem X_quotient_isFFModule (a : Vertex R) (ha : color R a = false) :
    letI := Q_normal R a
    letI := X_elementary R a
    IsFFModule (Offenders.linearize (X_quotientConjugation R a)) := by
  let := Q_normal R a
  let := X_elementary R a
  let := finite_X R a
  obtain ⟨t,hat,_,⟨w⟩⟩ := s.exists_layer_offenders a ha
  let := w.finite
  have hAS : w.A ≤ stabilizer R a :=
    w.le_edge.trans (fun _ hx => hx.2 a (adjacent_symm R hat))
  exact ⟨_,w.linear_offender (stabilizer R a) hAS (Q_normal R a)
    (X_normalized R a) (Q_le_centralizer_X R a)⟩

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
