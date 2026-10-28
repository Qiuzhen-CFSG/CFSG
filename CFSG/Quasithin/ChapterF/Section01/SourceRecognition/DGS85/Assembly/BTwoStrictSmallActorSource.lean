module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictSourceQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorSupplement

/-!
# The smaller-actor route into the strict source quotient

The original strict distance-two hypotheses supply the compatible Cartan,
both reflections, seven-path transitivity, thickness and odd seven-path
fixers. The remaining local input is (14.3)(a) supplementation and (14.9)(c)
natural coordinates for the actual join of the two half-path radicals,
at a putative failed exchange instance. The local quotient restriction
then supplies its own-core containment and the cubic argument gives the
exact `StrictSourceExchange` consumed by the marked quotient.

This is a conditional source consumer. Constructing that smaller natural
actor from the strict local profile remains necessary. In particular the
exceptional opposite-binary complement argument of (14.17) is not assumed.

Source: DGS, *Groups and Graphs* (1985), (14.3), (14.9), (14.12), (14.17),
printed pp.212,215--218,221--222.
-/

@[expose] public noncomputable section
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

/-- All geometric premises of the smaller-actor exchange are supplied by
the original strict branch, for the same source-selected reflections. -/
def strictSourceSmallActorGeometry : SixPathSmallActorGeometry (chosenCartans h) :=
  let d := strictSourceReflections h hc hne hb hβu hns hlinear
  { reflection := d.t
    fixes := d.fixes
    moves := d.moves
    squares := d.square
    normalizes := d.normalizes
    transitive := strict_tree_path_transitive_source h hc hne hb hβu hns hlinear
    thick := strict_path_thickness_source h d.t d.fixes d.moves
    odd := strict_tree_path_fixers_odd_source h hc hne hb hβu hns hlinear }

/-- The literal strict apartment exchanges once the failed local instances
have their (14.3)(a) supplement and marked (14.9)(c) natural actor. -/
theorem strict_source_exchange_of_small_actor_supplement
    (hlocal : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear) →
      ∀ g : (reducedAmalgam L S).Universal,
      (∀ k, 6≤k → k≤12 → g • p.getVert k=p.getVert k) → g • a≠a →
      (¬∃ z : (reducedAmalgam L S).Universal,
        (∀ k≤6, z • p.getVert k=p.getVert k) ∧ z • (g • a)=b) →
      ∃ J : Subgroup (reducedAmalgam L S).Universal, Finite J ∧
        halfPathActor (X := (reducedAmalgam L S).Universal) p 6 ≤ J ∧
        halfPathActor (X := (reducedAmalgam L S).Universal) p 6 ⊔ J.pCoreIn 2 = J ∧
        J.pCoreIn 2 ≤
          (MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert 6)).pCoreIn 2 ∧
        Nonempty (SmallActorPathCoordinates.{uF} p 6 (cartan (chosenCartans h)))) :
    StrictSourceExchange h hc hne hb hβu hns hlinear :=
  source_six_small_actor_exchange_of_supplement h (chosenCartans h)
    (strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear) hlocal

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
