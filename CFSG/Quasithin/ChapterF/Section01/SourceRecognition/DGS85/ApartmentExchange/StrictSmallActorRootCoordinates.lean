module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SmallActorRootCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorCore

/-!
# The original strict source marks both six-path roots

The source constructs both actual local field markings and the midpoint
valence. Regular exits on the chosen apartment then identify the two full
half-path radicals with opposite unipotent groups under one inner change
of that same quotient map. Its kernel remains the actor's own two-core.

No root coordinates, natural kernel action, or apartment exchange are
assumed. Naturality and the compatible reflection are separate source duties.
Source: DGS, Groups and Graphs (1985), (14.1)--(14.3), pp.210--212.
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

/-- Both actual strict-source roots have full opposite coordinates in the
same original midpoint map, whose kernel is the smaller actor's own core. -/
theorem strict_source_small_actor_root_coordinates :
    ∃ (K : Bool → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, Finite (K i))
      (_ : ∀ i, CharP (K i) 2), (∀ i, 4 ≤ Nat.card (K i)) ∧
    ∃ e : ∀ v : Vertex (reducedFamily L S),
      (graphLocalGroup (reducedFamily L S) v ⧸ pCore 2 (graphLocalGroup (reducedFamily L S) v)) ≃*
        SL(2,K v.type),
    ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
      (_hp : p.IsPath) (hl : p.length=12),
      (∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear) →
      let D := halfPathActor (X := (reducedAmalgam L S).Universal) p 6
      let R := (pathRoot (X := (reducedAmalgam L S).Universal) (p.drop 6)).subgroupOf D
      let U := (pathRoot (X := (reducedAmalgam L S).Universal) (p.take 6)).subgroupOf D
      let k := K ((bOne_tree_cover h).vertex (p.getVert 6)).type
      let f := halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6)))
      Function.Surjective f ∧ f.ker=pCore 2 D ∧
        R ⊓ f.ker=⊥ ∧ U ⊓ f.ker=⊥ ∧
        ∃ z : SL(2,k),
          R.map ((MulAut.conj z).toMonoidHom.comp f)=Matrix.SpecialLinearGroup.upperUnipotent k ∧
          ∀ y : SL(2,k), y∈U.map ((MulAut.conj z).toMonoidHom.comp f) ↔
            ∃ a : k, Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y := by
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
    source_six_root_coordinates h (chosenCartans h) d p hp hl hT (e _) (hval _)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
