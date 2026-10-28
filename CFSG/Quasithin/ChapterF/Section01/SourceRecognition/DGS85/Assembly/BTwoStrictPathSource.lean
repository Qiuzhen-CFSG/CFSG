module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.MarkedQuotient
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# The strict distance-two path profile on the original tree

The original left PSL₂ quotient and the constructed right quotient supply
both characteristic-two field markings. Source valence constructs the two
continuations of the critical path. The strict Cartan residual and edge-core
order theorem therefore give the literal source extrema `r = 6`, `s = 7`
and odd fixers for all source paths of length at least seven.

Regularity below the first nonregular length makes every nonbacktracking
seven-path simple. The original reduced-completion covering then transports
rooted transitivity and the full pointwise fixers to the actual universal
tree used in Chapter 14. The maps are the original endpoint inclusions.
The companion consumer discharges the left marking and nonsolvability from
the original Chapter 12 preparation. Marked amalgam recognition is separate.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.10)(a)--(c), printed p.164, and (14.1), pp.210--211.
-/

public noncomputable section
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Subgroup Theory.GroupTheory RankTwoAmalgam
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile OriginalExtension
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The strict path extrema and odd long-path fixers from the original
left linear quotient. The opposite field and both continuations are constructed. -/
theorem original_bTwo_strict_path_parameters_of_linear_left
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
      ∀ {a d : Vertex F} (p : (graph F).Walk a d),
        IsSourcePath p → 7 ≤ p.length →
          Odd (Nat.card (pathFixer (X := G₀ L S) p)) := by
  have hval (v : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) v.type
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq]; have := hval α; omega) β
  obtain ⟨y,hy,hyne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet u)
    (by rw [←Nat.card_coe_set_eq]; have := hval u; omega) β
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,m,hm,hright,_⟩ :=
    original_core_layers h hc hne hb hβu ht htne hns
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := hlinear
  obtain ⟨k₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := hright
  let _ := f₀
  let _ := fin₀
  let _ := f₁
  let _ := fin₁
  let _ := Fintype.ofFinite k₀
  let _ := Fintype.ofFinite k₁
  let _ : CharP k₀ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₀)
  let _ : CharP k₁ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₁)
  let K : Bool → Type := fun i => if i then k₁ else k₀
  let _ : ∀ i, Field (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, Finite (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, CharP (K i) 2 := fun i => by cases i <;> assumption
  let e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i) := by
    intro i
    cases i
    · exact e₀
    · exact e₁
  exact original_bTwo_strict_path_parameters h hc hne hb hβu ht htne hy hyne hns K e

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile OriginalExtension
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

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

/-- The source parameters and odd fixers give exactly the seven-path
hypotheses on the original universal tree. -/
theorem original_bTwo_strict_tree_path_profile_of_linear_left
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 7 ∧
    BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7 ∧
    ∀ {a d} (p : (sourceGraph (reducedAmalgam L S)).Walk a d),
      p.IsPath → p.length = 7 →
        Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
  obtain ⟨hpar,hodd⟩ := original_bTwo_strict_path_parameters_of_linear_left
    h hc hne hb hβu hns hlinear
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
    exact hodd p.toWalk (Or.inl hsimple) (by rw [length_toWalk])
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

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
