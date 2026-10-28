module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticStrictMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.SourcePaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.SourceCalculation

/-!
# Repeated critical paths on the original tensor geometry

The proved original strict index and backward existence construct an infinite
sequence of overlapping critical paths. Every literal second vertex retains
the strict B-index. The actual paired critical commutators then centralize
the radius at the twice-shifted endpoint, as required by the large-distance
calculation. No replacement kernel or additional distance premise is used.

This constructs the path geometry used in MS93 (5.10)--(5.11), pp.922--924,
for the original tensor case of Aschbacher--Smith 9.3.10, pp.734--735.
It does not assert the further selected-mover conditions or the large radius
index bound used in those source arguments. Both distance exclusions and
SymplecticPlaneRecognition remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- Apply the original strict-movement proof throughout the same overlapping
path sequence, and feed its paired commutators to the literal radius consumer. -/
theorem original_overlapping_critical_sequence
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ p : CriticalSegment geometry,
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry (fun _ _ _ => True) (s n) (s (n+1))) ∧
        (∀ n k i, i+2*k ≤ geometry.b R →
          (s (n+k)).path.walk.getVert (i+2*k) = (s n).path.walk.getVert i) ∧
        (∀ n, 4 < nextMovingIndex (s n)) ∧
        ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
          ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ := by
  intro R geometry hb p
  have hstep (q : CriticalSegment geometry) :
      ∃ d t, True ∧ Adjacent R q.first t ∧ Adjacent R d t ∧
        ¬ Z R d ≤ Q R (q.path.walk.getVert (geometry.b R-2)) := by
    obtain ⟨d,t,hat,hdt,⟨back,_,_⟩,_⟩ := c.original_backward_path eK geometry hb q.path
    exact ⟨d,t,True.intro,hat,hdt,by simpa only [q.path.length_eq_b] using back.critical.2⟩
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega) (fun _ _ _ => True) hstep p
  exact ⟨s,hs0,hs,hover,
    fun n => c.original_critical_strict_movement eK geometry hb (s n).path,
    paired_critical_commutators_centralize_radius hb (fun _ _ _ => True) s hs⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
