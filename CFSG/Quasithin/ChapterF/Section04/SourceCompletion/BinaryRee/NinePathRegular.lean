module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.CommonCover
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
/-!
# Regular nine-path actions and faithful apartment actions

The two actual local groups have orders 20480 and 12288. The local valences
five and three give exactly those numbers of nonbacktracking nine-edge paths
at their roots. Thus transitivity on these paths makes the root action regular,
and their pointwise stabilizers are trivial. In particular the pointwise fixer
of any sixteen-cycle is trivial, by restricting to its first nine edges.

This is the binary simplification of the apartment-kernel calculation in
F.4.16. The path-transitivity hypothesis is supplied by the concrete octagonal
BN-pair and the common-cover source transport; no recognition, group-order, or
reflection relation is assumed here.

Source: Aschbacher--Smith, F.4.6 and F.4.15--16, printed pp.276--277 and 281--282.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
open Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (c : Completion G)

/-- The actual vertex stabilizer has the corresponding marked local order. -/
theorem stabilizer_card (v : c.Vertex) :
    Nat.card (stabilizer c.family v) = (if v.type then 12288 else 20480) := by
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base c.family v
  have hc := Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv
  change Nat.card (stabilizer c.family (base c.family v.type)) =
    Nat.card (stabilizer c.family v) at hc
  rw [← hc, stabilizer, Subgroup.CosetGeometry.stabilizer_base]
  cases v.type
  · exact left_card c
  · exact right_card c

/-- Nine nonbacktracking steps give exactly as many paths as elements of the
root stabilizer: the first branching factor is five or three and thereafter
alternates between two and four. -/
theorem nine_path_card (v : c.Vertex) :
    Nat.card {p : BasedWalk c.graph 9 v // p.Nonbacktracking} =
      Nat.card (stabilizer c.family v) := by
  have (x : c.Vertex) : Finite (c.graph.neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [card_neighbors c x]; cases x.type <;> decide)
  have hf : ∀ {x y : c.Vertex}, c.graph.Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hc := BasedWalk.card_nonbacktracking_succ c.graph
    (fun x : c.Vertex => x.type) (fun b : Bool => if b then 3 else 5)
    hf (card_neighbors c) 8 v
  rw [stabilizer_card]
  change Nat.card {p : BasedWalk c.graph (8 + 1) v // p.Nonbacktracking} = _
  rw [hc]
  cases v.type <;> norm_num [BasedWalk.forwardCount]

/-- Transitivity at length nine is regularity: no nonidentity group element
fixes all vertices of such a nonbacktracking path. -/
theorem nine_pathStabilizer_eq_bot (v : c.Vertex)
    (ht : RootPathTransitive c.graph G v 9)
    (p : BasedWalk c.graph 9 v) (hp : p.Nonbacktracking) :
    pathStabilizer c.family p = ⊥ := by
  let P := {q : BasedWalk c.graph 9 v // q.Nonbacktracking}
  let : MulAction (stabilizer c.family v) P := nonbacktrackingAction c.family 9 v
  let p' : P := ⟨p, hp⟩
  have : Finite (stabilizer c.family v) :=
    Nat.finite_of_card_ne_zero (by rw [stabilizer_card]; cases v.type <;> decide)
  have htrans := (rootPathTransitive_iff c.family 9 v).mp ht
  let f : stabilizer c.family v → P := fun a => a • p'
  have hsur : Function.Surjective f := fun q => htrans.exists_smul_eq p' q
  have hinj := ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hsur, (nine_path_card c v).symm⟩).1
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  let a : stabilizer c.family v := ⟨g, pathStabilizer_le c.family p hg⟩
  have ha : a • p' = p' := Subtype.ext ((mem_pathStabilizer_iff c.family p a).mp hg)
  have he : a = 1 := hinj (ha.trans (one_smul _ p').symm)
  exact congrArg Subtype.val he
/-- A sixteen-cycle has trivial pointwise fixer. The proof uses its first
nine edges and retains the actual ambient action. -/
theorem cycle_fixer_eq_bot (v : c.Vertex)
    (ht : RootPathTransitive c.graph G v 9)
    (p : c.graph.Walk v v) (hp : p.IsCycle) (hlen : p.length = 16) :
    fixingSubgroup G {w | w ∈ p.support} = ⊥ := by
  have hl : (p.take 9).length = 9 := by rw [Walk.take_length, hlen]; rfl
  let q : BasedWalk c.graph 9 v := hl ▸ BasedWalk.ofWalk (p.take 9)
  have hq : q.Nonbacktracking :=
    (BasedWalk.nonbacktracking_cast hl _).mpr
      (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hp.isPath_take (by omega)))
  have hv : q.vertices = (p.take 9).support :=
    (BasedWalk.vertices_cast hl _).trans (BasedWalk.vertices_ofWalk _)
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hgq : g ∈ pathStabilizer c.family q := by
    intro w hw
    apply (mem_fixingSubgroup_iff G).mp hg w
    rw [hv, Walk.support_take] at hw
    exact List.mem_of_mem_take hw
  rw [nine_pathStabilizer_eq_bot c v ht q hq] at hgq
  exact hgq

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
