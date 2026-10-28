module
public import CFSG.Quasithin.Chapter14.Section09.StrictActorKernel.Kernel

/-!
# Original strict-source actor and kernel control

The original noncommuting distance-two hypotheses construct the actual
Cartan, reflections, path profile and both local quotient markings. Applying
the Cartan and kernel results to that same apartment proves the intrinsic
Cartan containment, full neighborhood-kernel centralization, and exact
endpoint-core intersection formula for every supported twelve-path and
both midpoint types. No new local-action or kernel hypothesis is imposed.

The natural action on this very intersection, its identification with Z_i,
and the reversing reflection needed for (14.17) remain source obligations.
Source: DGS, *Groups and Graphs* (1985), (14.3)(b), (14.5)(b), (14.9)(c),
printed pp.212--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment Assembly.BTwoSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The original strict source controls the same half-path actor and its
own kernel, preserving the chosen apartment, full Cartan and covering. -/
theorem strict_source_actor_kernel_control
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear) :
    let D := halfPathActor (X := (reducedAmalgam L S).Universal) p 6
    let φ := bOne_tree_map h
    let v := (bOne_tree_cover h).vertex (p.getVert 6)
    let C := cartan (chosenCartans h)
    let J := graphLocalGroup (reducedFamily L S) v
    C ≤ normalizer (D : Set (reducedAmalgam L S).Universal) ∧
      (C.map φ ⊓ J ≤ D.map φ) ∧ (C ⊓ J.comap φ ≤ D) ∧
      C ⊓ centralizer (D : Set (reducedAmalgam L S).Universal) =
        C ⊓ (U (reducedFamily L S) v).comap φ ∧
      (D.pCoreIn 2).map φ = D.map φ ⊓ Q (reducedFamily L S) v ∧
      (D.pCoreIn 2).map φ ≤ Q (reducedFamily L S) v ⊓
        centralizer ((C.map φ ⊓ U (reducedFamily L S) v : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
  intro D φ v C J
  obtain ⟨K,fK,finK,chK,_hK,e,hactors⟩ :=
    strict_source_small_actor_linear_quotients h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,hker,hcover,_⟩ := hactors p hp hl hT
  let d := strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear
  have hC := six_local_cartan_le_actor h (chosenCartans h) d p hl hT hcover
  have hkernel : (D.pCoreIn 2).map φ = D.map φ ⊓ Q (reducedFamily L S) v := by
    rw [Subgroup.pCoreIn,←hker]
    exact halfPath_kernel_image h p 6 hl (e v)
  exact ⟨six_cartan_normalizes_actor (chosenCartans h) d p hT,
    hC.1,hC.2,six_cartan_actor_centralizer h (chosenCartans h) d p hp hl hT,
    hkernel,le_inf (hkernel.le.trans inf_le_right)
      (six_actor_core_image_le_centralizer h p (chosenCartans h) d hp hl hT)⟩

end CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
