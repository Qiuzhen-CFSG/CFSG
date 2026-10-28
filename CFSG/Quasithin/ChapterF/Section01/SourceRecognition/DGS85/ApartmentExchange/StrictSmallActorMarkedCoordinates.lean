module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorTorus

/-!
# Root and Cartan markings from the original strict source

Package the actual strict-source field and quotient with both full opposite
six-path root images and all diagonal lifts from the original Cartan. The
same quotient map and its own-core kernel are used throughout. All these
markings are constructed internally from the strict critical source; no
root-coordinate or diagonal-lift premise is supplied.

The kernel's natural action and a compatible actor reflection remain the
separate source duties for apartment exchange.
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

/-- The actual strict source constructs its root and full Cartan markings
simultaneously on the same own-core quotient. -/
theorem strict_source_small_actor_marked_coordinates :
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
          (∀ y : SL(2,k), y∈U.map ((MulAut.conj z).toMonoidHom.comp f) ↔
            ∃ a : k, Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero a=y) ∧
          ∀ a : k, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
            ((cartan (chosenCartans h)).subgroupOf D).map
              ((MulAut.conj z).toMonoidHom.comp f) := by
  obtain ⟨K, fK, finK, chK, hK, e, hroots⟩ :=
    strict_source_small_actor_root_coordinates h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  refine ⟨K, fK, finK, chK, hK, e, ?_⟩
  intro a b p hp hl hT
  obtain ⟨hs, hk, hR, hU, z, hzR, hzU⟩ := hroots p hp hl hT
  exact ⟨hs, hk, hR, hU, z, hzR, hzU,
    strict_source_small_actor_full_diagonal h hc hne hb hβu hns hlinear
      p hp hl hT (e _) z hzR hzU⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
