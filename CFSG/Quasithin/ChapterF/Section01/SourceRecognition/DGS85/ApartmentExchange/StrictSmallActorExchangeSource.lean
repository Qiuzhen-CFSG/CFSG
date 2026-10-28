module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorNaturalCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorFaithfulExchange

/-!
# Strict apartment exchange from the literal Cartan-kernel condition

A failed exchange cannot have a core-free actor, and the beta source proves
its actor core-free. At alpha the nonzero whole core has the genuine natural
coordinates. The existing cubic calculation then contradicts failure.
Only the actual Cartan/full local-kernel nontriviality remains a local
condition; no naturality, root marking, reflection or catalogue is supplied.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
universe uG
variable {G : Type uG} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S

/-- All failed-exchange coordinate duties are discharged by the strict
source itself once its actual Cartan/full-kernel part is nontrivial. -/
theorem strict_source_exchange_of_cartan_kernels
    (hCU : ∀ {a b : SourceVertex (reducedAmalgam L S)}
      (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length=12 →
      (∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear) →
      (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
        U F ((bOne_tree_cover h).vertex (p.getVert 6))≠⊥) :
    StrictSourceExchange h hc hne hb hβu hns hlinear := by
  apply strict_source_exchange_of_small_actor_coordinates.{uG} h hc hne hb hβu hns hlinear
  intro a b p hp hl hT g hg hm hfail
  have hkernel := hCU p hp hl hT
  have hcore : pCore 2 (halfPathActor (X := (A).Universal) p 6)≠⊥ := by
    intro hz
    exact hfail (strict_source_faithful_path_exchange h hc hne hb hβu hns hlinear
      p hp hl hT hz g hg hm)
  cases ht : ((bOne_tree_cover h).vertex (p.getVert 6)).type
  · exact strict_source_small_actor_alpha_coordinates h hc hne hb hβu hns hlinear
      p hp hl hT hkernel ht hcore
  · exact (hcore (strict_source_small_actor_beta_core_eq_bot h hc hne hb hβu hns hlinear
      p hp hl hT hkernel ht)).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
