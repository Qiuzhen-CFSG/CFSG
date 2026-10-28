module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictSmallActorSource

/-!
# Original strict-source exchange with core placement discharged

Apply the midpoint-core theorem to the exact Cartan, reflections, paths and
universal action supplied by the original strict b=2 branch. The remaining
local premise is the smaller actor's marked natural quotient at a failed
exchange instance. The resulting `StrictSourceExchange` is the unchanged
input to the whole-Borel sign theorem and marked finite quotient consumers.

Source: DGS, *Groups and Graphs* (1985), (14.9)(c), (14.12), (14.17),
pp.215--218,221. This is conditional on the still-missing natural profiles.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The literal strict apartment exchanges once the failed local instances
have the marked (14.9)(c) natural actor; own-core placement is proved. -/
theorem strict_source_exchange_of_small_actor_coordinates
    (hlocal : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear) →
      ∀ g : (reducedAmalgam L S).Universal,
      (∀ k, 6≤k → k≤12 → g • p.getVert k=p.getVert k) → g • a≠a →
      (¬∃ z : (reducedAmalgam L S).Universal,
        (∀ k≤6, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b) →
      Nonempty (SmallActorPathCoordinates.{uF} p 6 (cartan (chosenCartans h)))) :
    StrictSourceExchange h hc hne hb hβu hns hlinear :=
  source_six_small_actor_exchange_of_coordinates h (chosenCartans h)
    (strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear) hlocal

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
