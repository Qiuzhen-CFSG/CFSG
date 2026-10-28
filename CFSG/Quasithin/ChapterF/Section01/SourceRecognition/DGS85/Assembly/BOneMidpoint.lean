module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOnePathCores
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathRoot

/-!
# Four-edge roots and their actual midpoint centers

In the b=1 natural branch, the cores at two distinct neighbors intersect in
exactly the full midpoint actor center. The two-core of a four-edge path
fixer is therefore that center, transported by the literal vertex conjugator.
It fixes the entire radius-two ball and depends only on the midpoint.
The proof retains the full center, including its nontrivial r=4 case, and
does not identify the action on Q/Z with an action on the whole core.

BOneMidpointCover applies these facts to the actual universal completion,
its chosen apartment roots and the original Chapter 12 selected pair.
Source: DGS, Groups and Graphs (1985), (10.5)(b,c), printed p.156,
and the path roots in (14.1)--(14.2), pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open NoncommutingProfile
open Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneMidpoint
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : LocallyRankOneTriple P B)
  (c₀ : BOneActionData (family P) (base (family P) false) (base (family P) true) k₀ W₀)
  (c₁ : BOneActionData (family P) (base (family P) true) (base (family P) false) k₁ W₁)
  (hn₀ : B ≤ normalizer (c₀.actor : Set G)) (hn₁ : B ≤ normalizer (c₁.actor : Set G))

/-- The supplied actor at either marked endpoint; no new model is chosen. -/
def actor (i : Bool) : Subgroup G := if i then c₁.actor else c₀.actor

include h hn₀ hn₁ in
/-- Two distinct neighbor cores meet in the full midpoint actor center. -/
theorem turn_center (i : Bool) {u z : Vertex (family P)}
    (hu : (graph (family P)).Adj (base (family P) i) u)
    (hz : (graph (family P)).Adj (base (family P) i) z) (hne : u ≠ z) :
    Q (family P) u ⊓ Q (family P) z = centerIn (actor c₀ c₁ i) := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  cases i
  · exact base_two_neighbor_core_intersection h false c₀ hn₀ hc₀ hc₁ hu hz hne
  · exact base_two_neighbor_core_intersection h true c₁ hn₁ hc₁ hc₀ hu hz hne

include h in
/-- The full actor center lies in the actual two-core. -/
theorem center_le_core (i : Bool) :
    centerIn (actor c₀ c₁ i) ≤ Q (family P) (base (family P) i) := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  cases i
  · exact (actor_center_le_cores c₀ h hc₀).trans inf_le_left
  · exact (actor_center_le_cores c₁ h hc₁).trans inf_le_left

include h hn₀ hn₁ in
/-- A four-edge path centered at a marked vertex has precisely its actor center as root. -/
theorem four_path_root (i : Bool) {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath) (hlen : p.length=4)
    (hm : p.getVert 2=base (family P) i) :
    pathRoot (X := G) p = centerIn (actor c₀ c₁ i) := by
  have hu := (p.adj_getVert_succ (by omega : 1<p.length)).symm
  have hz := p.adj_getVert_succ (by omega : 2<p.length)
  rw [hm] at hu hz
  have he := turn_center h c₀ c₁ hn₀ hn₁ i hu hz (by
    intro he
    have := hp.getVert_injOn (by omega : 1≤p.length) (by omega : 3≤p.length) he
    omega)
  change (pathFixer (X := G) p).pCoreIn 2 = _
  rw [pathFixer_core_eq_interior h c₀ c₁ hn₀ hn₁ p hp (by omega),
    pathInteriorCore_four p hlen,he,hm,inf_eq_left.mpr (center_le_core h c₀ c₁ i)]

include h hn₀ hn₁ in
/-- The full center lies in every neighboring two-core. -/
theorem center_le_neighbor_core (i : Bool) {u : Vertex (family P)}
    (hu : (graph (family P)).Adj (base (family P) i) u) :
    centerIn (actor c₀ c₁ i) ≤ Q (family P) u := by
  obtain ⟨hc₀,hc₁⟩ := paired_cores_eq_centers_of_actions h c₀ c₁
  cases i
  · obtain ⟨g,rfl⟩ := base_actor_neighbor_transitive h false c₀ hn₀ u hu
    rw [Q_translate]
    intro x hx
    refine ⟨x,(actor_center_le_cores c₀ h hc₀ hx).2,?_⟩
    change (g:G)*x*(g:G)⁻¹=x
    rw [hx.2 g g.property,mul_inv_cancel_right]
  · obtain ⟨g,rfl⟩ := base_actor_neighbor_transitive h true c₁ hn₁ u hu
    rw [Q_translate]
    intro x hx
    refine ⟨x,(actor_center_le_cores c₁ h hc₁ hx).2,?_⟩
    change (g:G)*x*(g:G)⁻¹=x
    rw [hx.2 g g.property,mul_inv_cancel_right]

include h hn₀ hn₁ in
/-- The actor center fixes every vertex within two steps of its marked vertex. -/
theorem center_fixes_ball_two (i : Bool) :
    centerIn (actor c₀ c₁ i) ≤ ballKernel (family P) (base (family P) i) 2 := by
  intro x hx z hz
  change (graph (family P)).edist (base (family P) i) z ≤ (2:ℕ∞) at hz
  obtain ⟨p,hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
    (show (graph (family P)).edist (base (family P) i) z ≠ ⊤ from
      ne_top_of_le_ne_top (by simp) hz)
  have hlen : p.length≤2 := by
    exact_mod_cast hp.symm ▸ hz
  cases p with
  | nil => exact Q_le_stabilizer _ _ (center_le_core h c₀ c₁ i hx)
  | @cons _ y z hxy p =>
    have hxQ := center_le_neighbor_core h c₀ c₁ hn₀ hn₁ i hxy hx
    apply (source_Z_Q_U h y).2 hxQ z
    change (graph (family P)).edist y z ≤ (1:ℕ∞)
    exact p.edist_le.trans (by exact_mod_cast (show p.length≤1 by simpa using hlen))

include h hn₀ hn₁ in
/-- The same turn formula with the literal midpoint conjugator. -/
theorem turn_center_translate (i : Bool) (g : G) {u v z : Vertex (family P)}
    (hv : g • base (family P) i=v)
    (hu : (graph (family P)).Adj v u) (hz : (graph (family P)).Adj v z) (hne : u≠z) :
    Q (family P) u ⊓ Q (family P) z =
      (centerIn (actor c₀ c₁ i)).map (MulAut.conj g).toMonoidHom := by
  have hb : g⁻¹ • v=base (family P) i := inv_smul_eq_iff.mpr hv.symm
  have hu' := (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hu
  have hz' := (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hz
  change (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • u) at hu'
  change (graph (family P)).Adj (g⁻¹ • v) (g⁻¹ • z) at hz'
  rw [hb] at hu' hz'
  have he := turn_center h c₀ c₁ hn₀ hn₁ i hu' hz'
    (fun he => hne ((MulAction.toPerm g⁻¹).injective he))
  have hm := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ←Q_translate,←Q_translate,smul_inv_smul,smul_inv_smul] at hm
  exact hm

include h hn₀ hn₁ in
/-- The root is the transported full actor center, with its actual conjugation map. -/
theorem four_path_root_translate (i : Bool) (g : G) {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath) (hlen : p.length=4)
    (hm : g • base (family P) i=p.getVert 2) :
    pathRoot (X := G) p = (centerIn (actor c₀ c₁ i)).map (MulAut.conj g).toMonoidHom := by
  have he := turn_center_translate h c₀ c₁ hn₀ hn₁ i g hm
    (p.adj_getVert_succ (by omega : 1<p.length)).symm
    (p.adj_getVert_succ (by omega : 2<p.length)) (by
      intro he
      have := hp.getVert_injOn (by omega : 1≤p.length) (by omega : 3≤p.length) he
      omega)
  have hle := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (center_le_core h c₀ c₁ i)
  rw [←Q_translate,hm] at hle
  change (pathFixer (X := G) p).pCoreIn 2 = _
  rw [pathFixer_core_eq_interior h c₀ c₁ hn₀ hn₁ p hp (by omega),
    pathInteriorCore_four p hlen,he,inf_eq_left.mpr hle]

include h hn₀ hn₁ in
/-- Every four-edge root fixes the whole radius-two ball about its midpoint. -/
theorem four_path_root_fixes_ball_two {a b : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (hp : p.IsPath) (hlen : p.length=4) :
    pathRoot (X := G) p ≤ ballKernel (family P) (p.getVert 2) 2 := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) (p.getVert 2)
  rw [four_path_root_translate h c₀ c₁ hn₀ hn₁ _ g p hp hlen hg,←hg,ballKernel_translate]
  exact Subgroup.map_mono (center_fixes_ball_two h c₀ c₁ hn₀ hn₁ _)

include h hn₀ hn₁ in
/-- Changing the four-edge path while keeping its midpoint preserves the root. -/
theorem four_path_roots_eq_of_midpoint {a b a' b' : Vertex (family P)}
    (p : (graph (family P)).Walk a b) (p' : (graph (family P)).Walk a' b')
    (hp : p.IsPath) (hp' : p'.IsPath) (hlen : p.length=4) (hlen' : p'.length=4)
    (hm : p.getVert 2=p'.getVert 2) : pathRoot (X := G) p=pathRoot (X := G) p' := by
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base (family P) (p.getVert 2)
  rw [four_path_root_translate h c₀ c₁ hn₀ hn₁ _ g p hp hlen hg,
    four_path_root_translate h c₀ c₁ hn₀ hn₁ _ g p' hp' hlen' (hg.trans hm)]

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneMidpoint
