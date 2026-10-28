module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.MixedPathTransitivity
public import Theory.GroupAction.CubicTree.TotalSingularity
/-!
# Exact nonbacktracking regular lengths in the mixed graph

Five-walk transitivity makes every shorter walk regular at both endpoints.
For a walk of length at least five, the odd pointwise fixer cannot be
transitive on its even set of two or four forward choices. Consequently
the regular nonbacktracking lengths are exactly zero through four, and
both extrema are realized by actual walks in the source graph.

The simple-path transitivity interface for the apartment construction is
also supplied and transferred through every marked coset cover using the
actual path-fixer isomorphism. The source's exceptional closed two-edge return convention
is addressed separately from these nonbacktracking extrema.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.7)(f), pp.174--175, and the regularity definitions, pp.73--74.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Theory.GroupAction.CubicTree

private theorem two_neighbors {G : Type*} [Group G] (F : Bool → Subgroup G)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5) :
    HasTwoNeighbors (graph F) := by
  intro a b
  exact Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet a) (by
    rw [←Nat.card_coe_set_eq,hval]; cases a.type <;> decide) b

private theorem right_regular_of_root_transitive {G : Type*} [Group G]
    (F : Bool → Subgroup G) {n : ℕ} {a : Vertex F}
    (ht : RootPathTransitive (graph F) G a (n+1))
    (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking) : RightRegular (A := G) p := by
  intro z w hz hw
  have haz := forward_adj p hz
  have haw := forward_adj p hw
  obtain ⟨g,_,hg⟩ := ht (p.snoc haz) (p.snoc haw)
    ((forward_iff_snoc_nonbacktracking p hp haz).mp hz)
    ((forward_iff_snoc_nonbacktracking p hp haw).mp hw)
  rw [vertices_snoc,vertices_snoc,List.map_append,List.map_singleton] at hg
  have hs := List.append_inj hg (by simp : (p.vertices.map (g • ·)).length = p.vertices.length)
  refine ⟨g,?_,?_⟩
  · simpa only [List.map_id, id_eq] using (List.map_inj_left (l := p.vertices)
      (f := (g • ·)) (g := id)).mp (hs.1.trans (List.map_id p.vertices).symm)
  · simpa only [List.singleton_inj] using hs.2

private theorem exits_card {G : Type*} [Group G] (F : Bool → Subgroup G)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a) :
    Nat.card {z : Vertex F // Theory.GroupAction.CubicTree.Forward p z} =
      if p.endpoint.type then 2 else 4 := by
  classical
  let : Finite ((graph F).neighborSet p.endpoint) :=
    Nat.finite_of_card_ne_zero (by rw [hval]; cases p.endpoint.type <;> decide)
  let := Fintype.ofFinite ((graph F).neighborSet p.endpoint)
  let e : {z : Vertex F // Theory.GroupAction.CubicTree.Forward p z} ≃
      {z : (graph F).neighborSet p.endpoint // z ≠ ⟨p.penultimate,p.adj_penultimate_endpoint.symm⟩} := {
    toFun z := ⟨⟨z,z.property.1⟩,fun he => z.property.2 (congrArg Subtype.val he)⟩
    invFun z := ⟨z.val,z.val.property,fun he => z.property (Subtype.ext he)⟩
    left_inv z := rfl
    right_inv z := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ←Nat.card_eq_fintype_card,hval]
  cases p.endpoint.type <;> simp

private theorem not_right_regular_of_odd {G : Type*} [Group G] [Finite G]
    (F : Bool → Subgroup G)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) (n+1) a)
    (hodd : Odd (Nat.card (pathStabilizer F p))) : ¬ RightRegular (A := G) p := by
  intro hr
  let D : Set (Vertex F) := {z | Theory.GroupAction.CubicTree.Forward p z}
  have hD := exits_card F hval p
  obtain ⟨z,hz⟩ : D.Nonempty := Set.nonempty_of_ncard_ne_zero (by
    rw [←Nat.card_coe_set_eq]
    change Nat.card {z // Theory.GroupAction.CubicTree.Forward p z} ≠ 0
    rw [hD]; cases p.endpoint.type <;> decide)
  have hact : GraphAction (graph F) G :=
    ⟨fun g _ _ hadj => (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj hadj⟩
  have he : MulAction.orbit (pathStabilizer F p) z = D := by
    apply Set.Subset.antisymm
    · rintro _ ⟨g,rfl⟩
      exact forward_smul_of_fixes hact p g g.property hz
    · intro w hw
      obtain ⟨g,hg,hgw⟩ := hr z w hz hw
      exact ⟨⟨g,hg⟩,hgw⟩
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (pathStabilizer F p) z)
  rw [Nat.card_prod,he] at hc
  have hDeven : Even (Nat.card D) := by
    change Even (Nat.card {z // Theory.GroupAction.CubicTree.Forward p z})
    rw [hD]; cases p.endpoint.type <;> decide
  exact (Nat.not_even_iff_odd.mpr hodd) (hc ▸ hDeven.mul_right _)

private theorem based_transitive_of_root {G : Type*} [Group G]
    (F : Bool → Subgroup G) {n : ℕ}
    (ht : ∀ a : Vertex F, RootPathTransitive (graph F) G a n) :
    BasedPathTransitive (X := G) (graph F) n := by
  intro a b c p q hp hq hpl hql
  let p' : BasedWalk (graph F) n a := hpl ▸ ofWalk p
  let q' : BasedWalk (graph F) n a := hql ▸ ofWalk q
  have hp' : p'.Nonbacktracking := by
    simpa only [p',nonbacktracking_cast] using nonbacktracking_ofWalk_of_isPath p hp
  have hq' : q'.Nonbacktracking := by
    simpa only [q',nonbacktracking_cast] using nonbacktracking_ofWalk_of_isPath q hq
  obtain ⟨g,_,hg⟩ := ht a p' q' hp' hq'
  simp only [p',q',vertices_cast,vertices_ofWalk] at hg
  refine ⟨g,?_⟩
  intro k hk
  have he := congrArg (fun l : List (Vertex F) => l[k]?) hg
  rw [List.getElem?_map,←p.getVert_eq_support_getElem? (by omega),
    ←q.getVert_eq_support_getElem? (by omega)] at he
  simpa only [Option.map_some,Option.some.injEq] using he


private theorem root_transitive_on_cover {X H : Type*} [Group X] [Group H]
    {F₁ : Bool → Subgroup X} {F₂ : Bool → Subgroup H} {f : X →* H}
    (c : CoverData F₁ F₂ f) {n : ℕ} {a : Vertex F₁}
    (ht : RootPathTransitive (graph F₂) H (c.vertex a) n) :
    RootPathTransitive (graph F₁) X a n := by
  apply (rootPathTransitive_iff F₁ n a).mpr
  have hpre := (rootPathTransitive_iff F₂ n (c.vertex a)).mp ht
  constructor
  intro p q
  obtain ⟨g,hg⟩ := hpre.exists_smul_eq (c.nbPathEquiv n a p) (c.nbPathEquiv n a q)
  obtain ⟨x,rfl⟩ := (c.stabilizerEquiv a).surjective g
  exact ⟨x,(c.nbPathEquiv n a).injective ((c.nbPathEquiv_smul x p).trans hg)⟩

private theorem walk_fixer_eq_based {X : Type*} [Group X] (F₁ : Bool → Subgroup X)
    {a b : Vertex F₁} (p : (graph F₁).Walk a b) :
    pathFixer (X := X) p = pathStabilizer F₁ (ofWalk p) := by
  ext x
  rw [mem_pathFixer_support]
  change (∀ y ∈ p.support, x • y = y) ↔ ∀ y ∈ (ofWalk p).vertices, x • y = y
  rw [vertices_ofWalk]
/-- Five-walk transitivity and odd longer fixers determine regularity
for any graph with the two mixed valences. -/
theorem binary_graph_regular_iff_of_five_transitive
    {G : Type*} [Group G] [Finite G] (F : Bool → Subgroup G)
    (hval : ∀ v : Vertex F, Nat.card ((graph F).neighborSet v) = if v.type then 3 else 5)
    (hfive : ∀ a : Vertex F, RootPathTransitive (graph F) G a 5)
    (hodd : ∀ {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a),
      p.Nonbacktracking → 5 ≤ n → Odd (Nat.card (pathStabilizer F p)))
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking) :
    Regular (A := G) p ↔ n ≤ 4 := by
  constructor
  · intro hr
    by_contra hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact not_right_regular_of_odd F hval p (hodd p hp (by omega)) hr.2
  · intro hn
    apply regular_of_all_rightRegular (fun v q hq => ?_) p hp
    exact right_regular_of_root_transitive F
      ((hfive v).mono (two_neighbors F hval) (by omega : n+1 ≤ 5)) q hq

/-- The same five-path transitivity and odd-fixer profile on any marked
coset cover, using its actual stabilizer equivalence. -/
theorem binary_graph_cover_path_profile
    {G : Type*} [Group G] (F : Bool → Subgroup G)
    (hfive : ∀ a : Vertex F, RootPathTransitive (graph F) G a 5)
    (hodd : ∀ {a : Vertex F} (p : BasedWalk (graph F) 5 a),
      p.Nonbacktracking → Odd (Nat.card (pathStabilizer F p)))
    {X : Type*} [Group X] (F₁ : Bool → Subgroup X) (f : X →* G)
    (c : CoverData F₁ F f) :
    BasedPathTransitive (X := X) (graph F₁) 5 ∧
      ∀ {a b} (p : (graph F₁).Walk a b), p.IsPath → p.length = 5 →
        Odd (Nat.card (pathFixer (X := X) p)) := by
  refine ⟨based_transitive_of_root F₁ (fun a => root_transitive_on_cover c (hfive (c.vertex a))),?_⟩
  intro a b p hp hl
  rw [walk_fixer_eq_based,Nat.card_congr (c.pathStabilizerEquiv (ofWalk p)).toEquiv]
  have hnb : (c.pathEquiv p.length a (ofWalk p)).Nonbacktracking := by
    rw [c.pathEquiv_apply]
    exact (nonbacktracking_map_iff c.hom (fun v => (c.neighbor_bijective v).1) (ofWalk p)).mpr
      (nonbacktracking_ofWalk_of_isPath p hp)
  generalize he : c.pathEquiv p.length a (ofWalk p) = q at hnb ⊢
  clear he
  revert q
  rw [hl]
  exact fun q hq => hodd q hq

variable {G : Type*} [Group G] [Finite G] (K U₀ S : Subgroup G)
local notation "F" => Reduction.reducedFamily ![K,U₀] S
local notation "M" => Reduction.G₀ ![K,U₀] S
local notation "α" => base F false
local notation "β" => base F true

/-- All nonbacktracking walks of length at most five are transitive from
both vertex orbits in the actual mixed graph. -/
theorem mixed_binary_graph_short_walk_transitive (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    (a : Vertex F) (n : ℕ) (hn : n ≤ 5) : RootPathTransitive (graph F) M a n :=
  (mixed_binary_graph_five_walk_transitive K U₀ S h eK eU hc hb hcomm a).mono
    (two_neighbors F (mixed_reduced_neighbor_cards K U₀ S h eK eU)) hn

/-- The exact regular lengths in the mixed source graph, over both orbits.
This holds for every nonbacktracking walk, even with repeated vertices. -/
theorem mixed_binary_graph_regular_iff (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking) :
    Regular (A := M) p ↔ n ≤ 4 := by
  constructor
  · intro hr
    by_contra hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact not_right_regular_of_odd F (mixed_reduced_neighbor_cards K U₀ S h eK eU) p
      (mixed_binary_graph_based_fixer_odd K U₀ S h eK eU hc hb hcomm p hp (by omega)) hr.2
  · intro hn
    apply regular_of_all_rightRegular (fun v q hq => ?_) p hp
    exact right_regular_of_root_transitive F
      (mixed_binary_graph_short_walk_transitive K U₀ S h eK eU hc hb hcomm v (n+1) (by omega)) q hq


/-- The precise simple-path transitivity premise for the apartment construction,
with the original reduced graph and both vertex orbits. -/
theorem mixed_binary_graph_five_path_transitive (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    BasedPathTransitive (X := M) (graph F) 5 :=
  based_transitive_of_root F (mixed_binary_graph_five_walk_transitive K U₀ S h eK eU hc hb hcomm)

/-- The extrema over all nonbacktracking walks are exactly r=4 and s=5.
The witnesses are constructed from the actual graph valences. -/
theorem mixed_binary_graph_nonbacktracking_extrema (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥) :
    IsGreatest {n | ∃ a : Vertex F, ∃ p : BasedWalk (graph F) n a,
      p.Nonbacktracking ∧ Regular (A := M) p} 4 ∧
    IsLeast {n | ∃ a : Vertex F, ∃ p : BasedWalk (graph F) n a,
      p.Nonbacktracking ∧ ¬Regular (A := M) p} 5 := by
  have htwo := two_neighbors F (mixed_reduced_neighbor_cards K U₀ S h eK eU)
  obtain ⟨p,hp,_⟩ := exists_extension htwo (show 0 ≤ 4 by decide)
    (show BasedWalk (graph F) 0 α from PUnit.unit) trivial
  obtain ⟨q,hq,_⟩ := exists_extension htwo (show 0 ≤ 5 by decide)
    (show BasedWalk (graph F) 0 α from PUnit.unit) trivial
  have hr {n : ℕ} {a : Vertex F} (p : BasedWalk (graph F) n a) (hp : p.Nonbacktracking) :=
    mixed_binary_graph_regular_iff K U₀ S h eK eU hc hb hcomm p hp
  refine ⟨⟨⟨α,p,hp,(hr p hp).mpr le_rfl⟩,?_⟩,
    ⟨⟨α,q,hq,fun hh => by have := (hr q hq).mp hh; omega⟩,?_⟩⟩
  · rintro n ⟨a,t,ht,hreg⟩
    exact (hr t ht).mp hreg
  · rintro n ⟨a,t,ht,hnot⟩
    have hn : ¬n ≤ 4 := fun hn => hnot ((hr t ht).mpr hn)
    omega


/-- The exact path hypotheses used by the apartment construction hold on every
marked coset cover. Unique nonbacktracking lifting preserves the path fixer,
so no girth or tree premise is needed for this transfer. -/
theorem mixed_cover_path_profile (h : HypothesisF11 ![K,U₀] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U₀ ⧸ pCore 2 U₀) ≃* Equiv.Perm (Fin 3))
    (hc : IsCriticalPair F α β) (hb : DGS85.b F = 1) (hcomm : ⁅Z F α,Z F β⁆ = ⊥)
    {X : Type*} [Group X] (F₁ : Bool → Subgroup X) (f : X →* M)
    (c : CoverData F₁ F f) :
    BasedPathTransitive (X := X) (graph F₁) 5 ∧
      ∀ {a b} (p : (graph F₁).Walk a b), p.IsPath → p.length = 5 →
        Odd (Nat.card (pathFixer (X := X) p)) := by
  refine ⟨based_transitive_of_root F₁ (fun a => root_transitive_on_cover c
    (mixed_binary_graph_five_walk_transitive K U₀ S h eK eU hc hb hcomm (c.vertex a))),?_⟩
  intro a b p hp hl
  rw [walk_fixer_eq_based,Nat.card_congr (c.pathStabilizerEquiv (ofWalk p)).toEquiv]
  apply mixed_binary_graph_based_fixer_odd K U₀ S h eK eU hc hb hcomm
  · rw [c.pathEquiv_apply]
    exact (nonbacktracking_map_iff c.hom (fun v => (c.neighbor_bijective v).1) (ofWalk p)).mpr
      (nonbacktracking_ofWalk_of_isPath p hp)
  · omega

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
