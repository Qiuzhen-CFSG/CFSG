module

public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorExchange

/-!
# Core placement for the literal smaller actor

The two half-path radicals of a centered path both fix the midpoint, so their
join is a subgroup of the midpoint stabilizer. If the source actor-normalizer
calculation proves that this stabilizer normalizes the join, relative
`pCoreIn` monotonicity places the join's own two-core in the midpoint two-core.
This is the exact containment needed by the failure-conditioned exchange
consumer; it does not replace the source normalizer calculation by global
endpoint normalization.

Source: DGS (14.3)(a,d), printed p.212, and (14.9)(c), pp.215--216.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.WeakBNPair.RegularTree
open SimpleGraph
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

variable {X V : Type*} [Group X] [MulAction X V]
variable {Γ : SimpleGraph V} {a b : V}

private theorem pathRoot_fixes_vertex {p : Γ.Walk a b} (m : ℕ)
    (hm : m ≤ p.length) :
    pathRoot (X := X) p ≤ MulAction.stabilizer X (p.getVert m) := by
  intro x hx
  exact (pCoreIn_le 2 (pathFixer (X := X) p) hx) m hm

include Γ in
/-- The literal join of the two half-path radicals fixes the midpoint. -/
theorem halfPathActor_le_midpoint_stabilizer
    {p : Γ.Walk a b} {n : ℕ} (hlen : p.length = 2*n) :
    halfPathActor (X := X) p n ≤
      MulAction.stabilizer X (p.getVert n) := by
  apply sup_le
  · intro x hx
    have hm := pathRoot_fixes_vertex (X := X) (p := p.drop n) 0
      (Nat.zero_le _) hx
    simpa only [SimpleGraph.Walk.drop_getVert, Nat.add_zero] using hm
  · intro x hx
    have hnp : n ≤ p.length := by
      rw [hlen]
      omega
    have hm := pathRoot_fixes_vertex (X := X) (p := p.take n) n
      (by
        rw [SimpleGraph.Walk.take_length]
        exact (Nat.le_min).2 ⟨le_refl n, hnp⟩) hx
    simpa only [SimpleGraph.Walk.take_getVert, Nat.min_self] using hm

/-- Relative core monotonicity gives the exact smaller-core containment once
the source actor-normalizer statement is available. -/
theorem halfPathActor_core_le_midpoint_core
    {p : Γ.Walk a b} {n : ℕ} (hlen : p.length = 2*n)
    (hnorm : MulAction.stabilizer X (p.getVert n) ≤
      normalizer (halfPathActor (X := X) p n : Set X)) :
    (halfPathActor (X := X) p n).pCoreIn 2 ≤
      (MulAction.stabilizer X (p.getVert n)).pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (halfPathActor_le_midpoint_stabilizer hlen) hnorm

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
open RankTwoAmalgam Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension

universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source-facing form of the six-path consumer.  The source calculation
supplies normalization by the midpoint stabilizer of the literal smaller
actor; the actor's own-core containment is then discharged by
`halfPathActor_core_le_midpoint_core`.  The natural-coordinate profile remains
the source obligation at the selected failing path. -/
theorem source_six_small_actor_exchange_of_normalizer
    (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
    (d : SixPathSmallActorGeometry c)
    (hlocal : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) →
      ∀ g : (reducedAmalgam L S).Universal,
      (∀ k, 6≤k → k≤12 → g • p.getVert k=p.getVert k) → g • a≠a →
      (¬∃ z : (reducedAmalgam L S).Universal,
        (∀ k≤6, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b) →
      MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert 6) ≤
        normalizer (halfPathActor (X := (reducedAmalgam L S).Universal) p 6 : Set _) ∧
      Nonempty (SmallActorPathCoordinates.{uF} p 6 (cartan c))) :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S))
      (cartanApartment (reducedAmalgam L S) (reflectionGroup c d.reflection)) 6 := by
  apply source_six_small_actor_exchange h c d
  intro a b p hp hl hT g hg hmove hfail
  obtain ⟨hnorm, hcoords⟩ := hlocal p hp hl hT g hg hmove hfail
  exact ⟨halfPathActor_core_le_midpoint_core (p := p) (n := 6) (by omega) hnorm,
    hcoords⟩

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

