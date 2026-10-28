module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictCartanKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorExchangeSource

/-!
# Strict apartment exchange from the original source

The two actual local Cartans force a nontrivial intersection of the whole
Cartan with the midpoint permutation kernel. The proved smaller-actor
analysis supplies natural coordinates and reflections and excludes every
failed exchange. No Cartan-kernel, natural-module, reflection or apartment
exchange input remains.
Source: DGS, Groups and Graphs (1985), (14.9)--(15.3).
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
universe uG
variable {G : Type uG} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual strict distance-two source proves its apartment exchange.
The Cartan and whole local kernels retain their original definitions. -/
theorem strict_source_exchange
    (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    StrictSourceExchange h hc hne hb hβu hns hlinear := by
  apply strict_source_exchange_of_cartan_kernels h hc hne hb hβu hns hlinear
  intro a b p hp hl hT
  exact strict_source_cartan_kernel_ne_bot h hc hne hb hβu hns hlinear p hp hl hT

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
