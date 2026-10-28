module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCore

/-!
# The original strict branch supplies the smaller actor quotient

Use the actual strict b=2 profiles to construct both nonbinary fields and
all local quotient markings. Their original Borel indices give the exact
valences; the universal covering preserves those valences. Apply the
opposite half-path theorem to every twelve-path in the source-selected
apartment. The output retains the same local marking and covering map,
proves supplementation, and identifies the smaller actor's own two-core
quotient with SL₂ on every original representative.

This discharges the quotient part of the remaining local coordinate input.
The natural action on the kernel and compatible reflection exchange are
not yet constructed. Both G₂ and triality field patterns remain possible.
Source: DGS, *Groups and Graphs* (1985), (10.10), p.164; (14.3)(a),
(14.9)(c), pp.212,215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The original strict branch constructs the literal smaller actor quotient,
for both midpoint types and every supported twelve-path. -/
theorem strict_source_small_actor_linear_quotients :
    ∃ (K : Bool → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Finite (K i))
      (_ : ∀ i, CharP (K i) 2), (∀ i, 4 ≤ Nat.card (K i)) ∧
    ∃ e : ∀ v : Vertex (reducedFamily L S),
      (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)) ≃*
        SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
      (_hp : p.IsPath) (hl : p.length=12),
      (∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear) →
      Function.Surjective (halfPathLinearMap h p 6 hl
        (e ((bOne_tree_cover h).vertex (p.getVert 6)))) ∧
      (halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6)))).ker =
        pCore 2 (halfPathActor (X := (reducedAmalgam L S).Universal) p 6) ∧
      (halfPathActor (X := (reducedAmalgam L S).Universal) p 6).map (bOne_tree_map h) ⊔
        Q (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) =
          graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6)) ∧
      ∃ E : (halfPathActor (X := (reducedAmalgam L S).Universal) p 6 ⧸
          pCore 2 (halfPathActor (X := (reducedAmalgam L S).Universal) p 6)) ≃*
            SL(2,K ((bOne_tree_cover h).vertex (p.getVert 6)).type),
        ∀ x : halfPathActor (X := (reducedAmalgam L S).Universal) p 6,
          E (QuotientGroup.mk' _ x) = e _ (QuotientGroup.mk' _ (halfPathLocalMap h p 6 hl x)) := by
  obtain ⟨K,fK,finK,chK,hK,e'⟩ :=
    original_bTwo_strict_nonbinary_markings h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  let e (v) := Classical.choice (e' v)
  refine ⟨K,fK,finK,chK,hK,e,?_⟩
  have hi (i : Bool) : ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index =
      Nat.card (K i)+1 := by
    have hadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i)
        (base (reducedFamily L S) (!i)) :=
      ⟨by change i≠!i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    have he := source_linear_edge_index_of_quotient (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj (e (base (reducedFamily L S) i))
    change (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i))).relIndex
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)) = _ at he
    rw [show stabilizer (reducedFamily L S) (base (reducedFamily L S) i) = reducedFamily L S i from
      Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) = reducedFamily L S (!i) from
      Subgroup.CosetGeometry.stabilizer_base _ _] at he
    exact he
  have hval (v : SourceVertex (reducedAmalgam L S)) :
      Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet v) =
        Nat.card (K ((bOne_tree_cover h).vertex v).type)+1 := by
    rw [Nat.card_congr (Equiv.ofBijective ((bOne_tree_cover h).hom.mapNeighborSet v)
      ((bOne_tree_cover h).neighbor_bijective v))]
    exact card_neighbors_of_indices (reducedFamily L S) (fun i => Nat.card (K i)+1) hi _
  intro a b p hp hl hT
  let d := strictSourceSmallActorGeometry h hc hne hb hβu hns hlinear
  exact ⟨source_six_halfPathLinearMap_surjective h (chosenCartans h) d p hp hl hT
      (e _) (hval _),
    source_six_halfPathLinearMap_kernel h (chosenCartans h) d p hp hl hT (e _) (hval _),
    source_six_halfPathActor_supplement h (chosenCartans h) d p hp hl hT (e _) (hval _),
    sourceSixHalfPathQuotientEquiv h (chosenCartans h) d p hp hl hT (e _) (hval _),
    sourceSixHalfPathQuotientEquiv_apply h (chosenCartans h) d p hp hl hT (e _) (hval _)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
