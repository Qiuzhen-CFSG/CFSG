module

public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.Kernels
public import Theory.GroupAction.RankTwoCosetCover.RootPathTransitivity
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Local order bounds from transitive nonbacktracking paths

Orbit--stabilizer counts paths from a root together with their pointwise
fixer. In valences three and five, eight edges from the quintic root give
5120 paths. A nontrivial radius-four kernel at the midpoint doubles this
bound, making the common edge stabilizer have order at least 2048.
Only the quintic stabilizer must be finite; the graph may be infinite.

Source: the path conventions of Aschbacher--Smith F.3.3--5, pp.270--272;
the numerical application is F.1.12 and 14.2.20--21, pp.263 and 988--989.
-/

public noncomputable section
namespace Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The actual local indices determine the valence at every vertex. -/
theorem card_neighbors_of_indices (degree : Bool → ℕ)
    (hi : ∀ i, ((F (!i)).subgroupOf (F i)).index = degree i)
    (v : Vertex F) :
    Nat.card ((graph F).neighborSet v) = degree v.type := by
  obtain ⟨g, hg⟩ := exists_smul_base F v
  have hc := Nat.card_congr
    ((translationGraphIso F g).mapNeighborSet (base F v.type))
  change Nat.card ((graph F).neighborSet (base F v.type)) =
    Nat.card ((graph F).neighborSet (g • base F v.type)) at hc
  rw [hg] at hc
  exact hc.symm.trans ((card_neighbor_base F v.type).trans (hi v.type))

/-- Eight nonbacktracking edges from either vertex of a (3,5) pair.
No transitivity or finiteness of the whole vertex set is used in this count. -/
theorem card_eight_paths_of_indices_three_five
    (hthree : ((F true).subgroupOf (F false)).index = 3)
    (hfive : ((F false).subgroupOf (F true)).index = 5) (i : Bool) :
    Nat.card {p : BasedWalk (graph F) 8 (base F i) // p.Nonbacktracking} =
      (if i then 5120 else 6144) := by
  have hi (i : Bool) : ((F (!i)).subgroupOf (F i)).index = (if i then 5 else 3) := by
    cases i
    · exact hthree
    · exact hfive
  have hc := card_neighbors_of_indices F (fun i => if i then 5 else 3) hi
  have (v : Vertex F) : Finite ((graph F).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> decide)
  have hf : ∀ {v w : Vertex F}, (graph F).Adj v w → w.type = !v.type := by
    intro v w h
    have hne := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have h := BasedWalk.card_nonbacktracking_succ (graph F)
    (fun v : Vertex F => v.type) (fun i => if i then 5 else 3) hf hc 7 (base F i)
  change Nat.card {p : BasedWalk (graph F) (7 + 1) (base F i) // p.Nonbacktracking} = _
  rw [h]
  change (if i then 5 else 3) *
    BasedWalk.forwardCount (fun j => if j then 5 else 3) 7 (!i) = _
  cases i <;> decide

/-- Orbit--stabilizer for the literal nonbacktracking-path action. -/
theorem card_paths_mul_card_fixer {n : ℕ} {v : Vertex F}
    (ht : RootPathTransitive (graph F) G v n)
    (p : BasedWalk (graph F) n v) (hp : p.Nonbacktracking) :
    Nat.card {q : BasedWalk (graph F) n v // q.Nonbacktracking} *
      Nat.card (pathStabilizer F p) = Nat.card (stabilizer F v) := by
  let P := {q : BasedWalk (graph F) n v // q.Nonbacktracking}
  let p' : P := ⟨p, hp⟩
  have htrans := (rootPathTransitive_iff F n v).mp ht
  have he : Function.Bijective
      (Subtype.val : MulAction.orbit (stabilizer F v) p' → P) := by
    refine ⟨Subtype.val_injective, fun q => ?_⟩
    obtain ⟨g, rfl⟩ := htrans.exists_smul_eq p' q
    exact ⟨⟨g • p', MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩, rfl⟩
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (stabilizer F v) p')
  rw [Nat.card_prod, Nat.card_congr (Equiv.ofBijective _ he)] at hc
  have hs : MulAction.stabilizer (stabilizer F v) p' =
      (pathStabilizer F p).subgroupOf (stabilizer F v) := by
    ext a
    change a • p' = p' ↔ a.val ∈ pathStabilizer F p
    exact Subtype.ext_iff.trans (mem_pathStabilizer_iff F p a).symm
  rw [hs, Nat.card_congr (subgroupOfEquivOfLe (pathStabilizer_le F p)).toEquiv] at hc
  exact hc

private theorem support_mem_ball {v w : Vertex F} (p : (graph F).Walk v w)
    (n : ℕ) (hn : p.length ≤ n) {x : Vertex F} (hx : x ∈ p.support) :
    x ∈ ball F v n := by
  obtain ⟨k, rfl, _⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  change (graph F).edist v (p.getVert k) ≤ (n : ℕ∞)
  exact (p.take k).edist_le.trans (ENat.natCast_le_natCast.mpr (by
    rw [SimpleGraph.Walk.take_length]
    exact (min_le_right _ _).trans hn))

/-- The radius-four kernel at the middle vertex fixes an eight-edge path,
whether or not that path is geodesic. -/
theorem midpoint_kernel_le_fixer {v : Vertex F}
    (p : BasedWalk (graph F) 8 v) :
    ballKernel F (p.toWalk.getVert 4) 4 ≤ pathStabilizer F p := by
  intro g hg x hx
  apply hg x
  rw [← BasedWalk.support_toWalk, ← p.toWalk.append_take_drop_eq 4,
    SimpleGraph.Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · apply support_mem_ball F (p.toWalk.take 4).reverse 4
    · rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length]
      exact min_le_left _ _
    · simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hx
  · apply support_mem_ball F (p.toWalk.drop 4) 4
    · rw [SimpleGraph.Walk.drop_length, BasedWalk.length_toWalk]
    · exact hx

/-- A nontrivial kernel at the quintic midpoint supplies the missing factor
 two. Only the quintic vertex stabilizer needs to be finite. -/
theorem common_card_ge_2048_of_quintic_paths [Finite (F true)]
    (hthree : ((F true).subgroupOf (F false)).index = 3)
    (hfive : ((F false).subgroupOf (F true)).index = 5)
    (ht : RootPathTransitive (graph F) G (base F true) 8)
    (hk : ballKernel F (base F true) 4 ≠ ⊥) :
    2048 ≤ Nat.card (F false ⊓ F true : Subgroup G) := by
  have : Finite (stabilizer F (base F true)) := by
    rw [stabilizer, stabilizer_base]
    infer_instance
  have hc := card_eight_paths_of_indices_three_five F hthree hfive true
  change Nat.card {p : BasedWalk (graph F) 8 (base F true) // p.Nonbacktracking} = 5120 at hc
  have hp : Nonempty {p : BasedWalk (graph F) 8 (base F true) // p.Nonbacktracking} :=
    (Nat.card_pos_iff.mp (hc ▸ (by decide : 0 < 5120))).1
  obtain ⟨p, hp⟩ := hp
  have htau : (p.toWalk.getVert 4).type = true := by
    have he := (even_walk_iff F (p.toWalk.take 4)).mp (by
      rw [SimpleGraph.Walk.take_length, BasedWalk.length_toWalk]
      decide)
    exact he.symm
  obtain ⟨g, hg⟩ := exists_smul_base F (p.toWalk.getVert 4)
  rw [htau] at hg
  have hk' : ballKernel F (p.toWalk.getVert 4) 4 ≠ ⊥ := by
    rw [← hg, ballKernel_translate]
    exact fun hh => hk ((map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hh)
  have hfix : pathStabilizer F p ≠ ⊥ := fun hh =>
    hk' (bot_unique ((midpoint_kernel_le_fixer F p).trans hh.le))
  have : Finite (pathStabilizer F p) :=
    Finite.of_injective (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  have hfixcard := (one_lt_card_iff_ne_bot (H := pathStabilizer F p)).mpr hfix
  have horder := card_paths_mul_card_fixer F ht p hp
  rw [hc, stabilizer, stabilizer_base] at horder
  have hcount := ((F false).subgroupOf (F true)).index_mul_card
  rw [hfive, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe (show F false ⊓ F true ≤ F true from
      inf_le_right)).toEquiv] at hcount
  omega

end Subgroup.CosetGeometry.RankTwo
