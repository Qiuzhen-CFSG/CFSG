module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoStrictPaths

/-!
# The strict binary and nonbinary profiles on the original universal tree

The unrestricted strict path parameters give seven-path transitivity and
odd seven-path fixers on the original reduced coset graph. Short-path
regularity makes its nonbacktracking seven-paths simple. The original
faithful-completion cover transfers the rooted action and the full pointwise
fixer through the same endpoint and Borel inclusions used by Chapter 14.

This supplies the actual universal-tree consumer in every strict field,
including binary alpha. The literal field markings and strict D inequality
are retained; no nonsolvability hypothesis or marked-amalgam recognition is
assumed. The beta irreducibility clause remains a separate source obligation.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10)(a)--(c), printed p.164, and the tree reduction p.227.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open DGS85.Reduction Noncommuting OriginalExtension
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

private theorem based_transitive_of_root {X : Type*} [Group X]
    (E : Bool → Subgroup X) {n : ℕ}
    (ht : ∀ a : Vertex E, RootPathTransitive (graph E) X a n) :
    BasedPathTransitive (X := X) (graph E) n := by
  intro a b c p q hp hq hpl hql
  let p' : BasedWalk (graph E) n a := hpl ▸ ofWalk p
  let q' : BasedWalk (graph E) n a := hql ▸ ofWalk q
  have hp' : p'.Nonbacktracking := by
    simpa only [p',nonbacktracking_cast] using nonbacktracking_ofWalk_of_isPath p hp
  have hq' : q'.Nonbacktracking := by
    simpa only [q',nonbacktracking_cast] using nonbacktracking_ofWalk_of_isPath q hq
  obtain ⟨g,_,hg⟩ := ht a p' q' hp' hq'
  simp only [p',q',vertices_cast,vertices_ofWalk] at hg
  refine ⟨g,?_⟩
  intro k hk
  have he := congrArg (fun l : List (Vertex E) => l[k]?) hg
  rw [List.getElem?_map,←p.getVert_eq_support_getElem? (by omega),
    ←q.getVert_eq_support_getElem? (by omega)] at he
  simpa only [Option.map_some,Option.some.injEq] using he

private theorem root_transitive_on_cover {X Y : Type*} [Group X] [Group Y]
    {F₁ : Bool → Subgroup X} {F₂ : Bool → Subgroup Y} {f : X →* Y}
    (c : CoverData F₁ F₂ f) {n : ℕ} {a : Vertex F₁}
    (ht : RootPathTransitive (graph F₂) Y (c.vertex a) n) :
    RootPathTransitive (graph F₁) X a n := by
  apply (rootPathTransitive_iff F₁ n a).mpr
  have hpre := (rootPathTransitive_iff F₂ n (c.vertex a)).mp ht
  constructor
  intro p q
  obtain ⟨g,hg⟩ := hpre.exists_smul_eq (c.nbPathEquiv n a p) (c.nbPathEquiv n a q)
  obtain ⟨x,rfl⟩ := (c.stabilizerEquiv a).surjective g
  exact ⟨x,(c.nbPathEquiv n a).injective ((c.nbPathEquiv_smul x p).trans hg)⟩

/-- The same original universal cover carries the unrestricted strict
seven-path profile, including binary alpha and both orientations. -/
theorem original_bTwo_strict_tree_source_profile
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι ≠ (Z F α).map ι) :
    HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
    BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7 ∧
    ∀ {a d} (p : (sourceGraph (reducedAmalgam L S)).Walk a d),
      p.IsPath → p.length = 7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
  obtain ⟨hpar,hodd⟩ := original_bTwo_strict_source_path_parameters
    h hc hne hb hβu ht htne K e hD
  have hs : sourceS (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) = 7 :=
    (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2.unique hpar.2
  have htrans (a : Vertex F) : RootPathTransitive (graph F) (G₀ L S) a 7 :=
    sourceS_transitive (reduced_triple h) (reduced_vertex_sylow h) a hs.ge
  have hval (v : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) v.type
  have ho {a : Vertex F} (p : BasedWalk (graph F) 7 a) (hp : p.Nonbacktracking) :
      Odd (Nat.card (pathStabilizer F p)) := by
    have hsimple : p.toWalk.IsPath := Theory.GroupAction.CubicTree.isPath_of_short_rightRegular
      hval 7 (fun m hm v q hq =>
        (sourceS_short_regular (reduced_triple h) (reduced_vertex_sylow h) q
          (by omega) hq).2) p le_rfl hp
    have he : pathFixer (X := G₀ L S) p.toWalk = pathStabilizer F p := by
      ext x
      rw [mem_pathFixer_support]
      rw [support_toWalk]
      rfl
    rw [←he]
    exact hodd p.toWalk (Or.inl hsimple) (length_toWalk p).ge
  let cov := bOne_tree_cover h
  refine ⟨hpar,based_transitive_of_root _
    (fun a => root_transitive_on_cover cov (htrans (cov.vertex a))),?_⟩
  intro a d p hp hl
  have hfixer : pathFixer (X := (reducedAmalgam L S).Universal) p =
      pathStabilizer (Universal.cosetFamily (reducedAmalgam L S)) (ofWalk p) := by
    ext x
    rw [mem_pathFixer_support]
    change _ ↔ ∀ z ∈ (ofWalk p).vertices, x • z = z
    rw [vertices_ofWalk]
  rw [hfixer,Nat.card_congr (cov.pathStabilizerEquiv (ofWalk p)).toEquiv]
  have hnb : (cov.pathEquiv p.length a (ofWalk p)).Nonbacktracking := by
    rw [cov.pathEquiv_apply]
    exact (nonbacktracking_map_iff cov.hom (fun v => (cov.neighbor_bijective v).1) (ofWalk p)).mpr
      (nonbacktracking_ofWalk_of_isPath p hp)
  generalize he : cov.pathEquiv p.length a (ofWalk p) = q at hnb ⊢
  clear he
  revert q
  rw [hl]
  exact fun q hq => ho q hq

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
