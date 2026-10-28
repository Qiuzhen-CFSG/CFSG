module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneClosedPaths
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
public import Theory.GroupAction.RankTwoCosetCover.PathTransport
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# The b=1 path conclusions on a covering graph

Three-path regularity excludes a four-cycle; the two vertex types exclude
odd cycles. Thus every nonbacktracking walk of length at most five is a
simple path in the source graph. A coset covering therefore sends each
relevant covering path to a source path. Unique local lifting transfers
based path transitivity, while the covering homomorphism identifies the
literal pointwise path stabilizers and preserves their orders.

The final theorem applies these facts to both alternatives of (10.5),
retaining the exact source extrema and actor centers. `BOneTreeSource`
constructs the covering from the actual reduced amalgam.

Source: DGS, *Groups and Graphs* (1985), path conventions pp.60,73--74,
(10.5), pp.156--157, and the tree reduction p.227; AS F.3.3, p.270.
-/

@[expose] public noncomputable section
open Subgroup SimpleGraph SimpleGraph.Walk
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
local instance coverAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include h c₀ c₁ hn₀ hn₁

/-- The source graph has no cycles short enough to obstruct four- or five-path lifting. -/
theorem bOne_cycle_length_gt_five
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (v : Vertex (family P)) (p : (graph (family P)).Walk v v) (hp : p.IsCycle) :
    5 < p.length := by
  let color : (graph (family P)).Coloring Bool := ⟨fun v => v.type, fun {_ _} hvw => hvw.1⟩
  have he : Even p.length := (color.even_length_iff_congr p).mpr Iff.rfl
  have h3 := hp.three_le_length
  by_contra hnot
  have h4 : p.length = 4 := by
    rcases he with ⟨m,hm⟩
    omega
  apply no_closed_source_path_of_regular_prefix h c₀ c₁ hn₀ hn₁ E₀ p hp.isPath_dropLast h3
  exact short_path_regular h c₀ c₁ hn₀ hn₁ E₀ E₁ p.dropLast hp.isPath_dropLast
    (by right; left; rw [length_dropLast,h4])

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {X G : Type*} [Group X] [Group G]
variable {F : Bool → Subgroup X} {E : Bool → Subgroup G} {f : X →* G}
variable (c : CoverData F E f)

private theorem short_path_image {N : ℕ}
    (hg : ∀ v (p : (graph E).Walk v v), p.IsCycle → N < p.length)
    {a b : Vertex F} (p : (graph F).Walk a b) (hp : p.IsPath) (hlen : p.length ≤ N) :
    (p.map c.hom).IsPath := by
  have hnb := (BasedWalk.nonbacktracking_map_iff c.hom
    (fun v => (c.neighbor_bijective v).1) (BasedWalk.ofWalk p)).mpr
      (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
  have ht := PathTransitivePolygon.isPath_of_nonbacktracking_of_cycle_bound hg
    ((BasedWalk.ofWalk p).map c.hom) hnb hlen
  rw [Walk.isPath_def, BasedWalk.support_toWalk,BasedWalk.vertices_map,
    BasedWalk.vertices_ofWalk] at ht
  simpa only [Walk.isPath_def,Walk.support_map] using ht

include c in
private theorem basedPathTransitive_lift {N n : ℕ}
    (hg : ∀ v (p : (graph E).Walk v v), p.IsCycle → N < p.length)
    (hn : n ≤ N) (ht : BasedPathTransitive (X := G) (graph E) n) :
    BasedPathTransitive (X := X) (graph F) n := by
  intro a b d p q hp hq hpl hql
  obtain ⟨g,hg⟩ := ht (p.map c.hom) (q.map c.hom)
    (short_path_image c hg p hp (by omega)) (short_path_image c hg q hq (by omega))
    (by simpa only [length_map] using hpl) (by simpa only [length_map] using hql)
  have hga : g ∈ stabilizer E (c.vertex a) := by
    change g • c.hom a = c.hom a
    simpa only [getVert_map,getVert_zero] using hg 0 (Nat.zero_le n)
  obtain ⟨x,hx⟩ := (c.stabilizerEquiv a).surjective ⟨g,hga⟩
  have hfx : f (x : X) = g := congrArg Subtype.val hx
  refine ⟨x,?_⟩
  intro j hj
  induction j with
  | zero =>
    simpa only [getVert_zero] using (show (x : X) • a = a from x.property)
  | succ j ih =>
    have hi := ih (by omega)
    have hpadj := (Subgroup.CosetGeometry.translationGraphIso F (x : X)).map_adj_iff.mpr
      (p.adj_getVert_succ (by omega : j < p.length))
    change (graph F).Adj ((x : X) • p.getVert j) ((x : X) • p.getVert (j+1)) at hpadj
    rw [hi] at hpadj
    have hqadj := q.adj_getVert_succ (by omega : j < q.length)
    apply congrArg Subtype.val ((c.neighbor_bijective (q.getVert j)).1
      (a₁ := ⟨_,hpadj⟩) (a₂ := ⟨_,hqadj⟩) ?_)
    apply Subtype.ext
    change c.vertex ((x : X) • p.getVert (j+1)) = c.vertex (q.getVert (j+1))
    rw [c.vertex_smul,hfx]
    have hh := hg (j+1) hj
    simp only [getVert_map] at hh
    exact hh

private theorem pathFixer_eq_pathStabilizer {a b : Vertex F} (p : (graph F).Walk a b) :
    pathFixer (X := X) p = pathStabilizer F (BasedWalk.ofWalk p) := by
  ext x
  change (∀ j ≤ p.length, x • p.getVert j = p.getVert j) ↔
    ∀ z ∈ (BasedWalk.ofWalk p).vertices, x • z = z
  rw [BasedWalk.vertices_ofWalk]
  constructor
  · intro hx z hz
    obtain ⟨j,rfl,hj⟩ := mem_support_iff_exists_getVert.mp hz
    exact hx j hj
  · intro hx j hj
    exact hx _ (mem_support_iff_exists_getVert.mpr ⟨j,rfl,hj⟩)

private theorem pathFixer_card_map {a b : Vertex F} (p : (graph F).Walk a b) :
    Nat.card (pathFixer (X := X) p) = Nat.card (pathFixer (X := G) (p.map c.hom)) := by
  rw [pathFixer_eq_pathStabilizer,pathFixer_eq_pathStabilizer]
  have he : pathStabilizer E (c.pathEquiv p.length a (BasedWalk.ofWalk p)) =
      pathStabilizer E (BasedWalk.ofWalk (p.map c.hom)) := by
    ext x
    change (∀ z ∈ (c.pathEquiv p.length a (BasedWalk.ofWalk p)).vertices, x • z = z) ↔ _
    rw [c.pathEquiv_vertices,BasedWalk.vertices_ofWalk]
    change _ ↔ ∀ z ∈ (BasedWalk.ofWalk (p.map c.hom)).vertices, x • z = z
    rw [BasedWalk.vertices_ofWalk,Walk.support_map]
    rfl
  rw [←he]
  exact Nat.card_congr (c.pathStabilizerEquiv (BasedWalk.ofWalk p)).toEquiv

include c in
private theorem odd_pathFixer_lift {N n : ℕ}
    (hg : ∀ v (p : (graph E).Walk v v), p.IsCycle → N < p.length)
    (hn : n ≤ N)
    (ho : ∀ {a b} (p : (graph E).Walk a b), p.IsPath → p.length = n →
      Odd (Nat.card (pathFixer (X := G) p))) :
    ∀ {a b} (p : (graph F).Walk a b), p.IsPath → p.length = n →
      Odd (Nat.card (pathFixer (X := X) p)) := by
  intro a b p hp hl
  rw [pathFixer_card_map c p]
  exact ho (p.map c.hom) (short_path_image c hg p hp (by omega))
    (by simpa only [length_map] using hl)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
variable {X G : Type*} [Group X] [Group G]
variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Bool → Subgroup X} {f : X →* G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance bOneCoverAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- Both regular alternatives supply the exact path premises on every marked coset cover. -/
theorem bOne_cover_path_alternatives (h : LocallyRankOneTriple P B)
    (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
    (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
    (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (c : CoverData F (family P) f) :
    (centerIn c₀.actor = ⊥ ∧ centerIn c₁.actor = ⊥ ∧
      HasSourcePathParameters (P := P) 3 4 ∧
      BasedPathTransitive (X := X) (graph F) 4 ∧
      ∀ {a b} (p : (graph F).Walk a b), p.IsPath → p.length = 4 →
        Odd (Nat.card (pathFixer (X := X) p))) ∨
    (Nat.card (centerIn c₀.actor) = Nat.card k₀ ∧ Nat.card (centerIn c₁.actor) = Nat.card k₁ ∧
      HasSourcePathParameters (P := P) 4 5 ∧
      BasedPathTransitive (X := X) (graph F) 5 ∧
      ∀ {a b} (p : (graph F).Walk a b), p.IsPath → p.length = 5 →
        Odd (Nat.card (pathFixer (X := X) p))) := by
  have hg := bOne_cycle_length_gt_five h c₀ c₁ hn₀ hn₁ E₀ E₁
  rcases bOne_source_path_parameters h c₀ c₁ hn₀ hn₁ E₀ E₁ with
    ⟨hc₀,hc₁,hpar,ht,ho⟩ | ⟨hc₀,hc₁,hpar,ht,ho⟩
  · exact Or.inl ⟨hc₀,hc₁,hpar,basedPathTransitive_lift c hg (by decide) ht,
      odd_pathFixer_lift c hg (by decide) (fun p hp hl => ho p (Or.inl hp) hl.ge)⟩
  · exact Or.inr ⟨hc₀,hc₁,hpar,basedPathTransitive_lift c hg (by decide) ht,
      odd_pathFixer_lift c hg (by decide) (fun p hp hl => ho p (Or.inl hp) hl.ge)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
