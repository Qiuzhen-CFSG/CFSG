module

public import Theory.SpecificGroups.ReeF4.Octagon.Binary.Automorphisms.Model
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount

/-!
# Faithfulness of the binary Ree building action

The two native vertex stabilizers have orders 20480 and 12288, exactly the
numbers of nonbacktracking nine-edge paths at their roots. The proved rooted
transitivity thus makes those path actions regular. An element fixing the
whole building fixes one such path and is the identity. Combined with the
full automorphism theorem, the inducing Model0 element is unique.

Source: Aschbacher--Smith F.4.16 and the action in J.5.6.
-/

public section
namespace ReeF4.Octagon.Binary.Automorphisms
open Subgroup Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.AlgebraicGroup.TitsSystem

private theorem stabilizer_card (v : CosetGeometry.Vertex family) :
    Nat.card (stabilizer family v) = (if v.type then 12288 else 20480) := by
  obtain ⟨g,hg⟩ := CosetGeometry.exists_smul_base family v
  have hc := Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv
  change Nat.card (stabilizer family (base family v.type)) = Nat.card (stabilizer family v) at hc
  rw [←hc,stabilizer,CosetGeometry.stabilizer_base]
  cases v.type
  · exact Tits.ExceptionalParabolics.FullRee.first_card
  · exact Tits.ExceptionalParabolics.FullRee.second_card

private theorem nine_path_card (v : CosetGeometry.Vertex family) :
    Nat.card {p : BasedWalk (DihedralGeometry.graph family) 9 v // p.Nonbacktracking} =
      Nat.card (stabilizer family v) := by
  have (x : CosetGeometry.Vertex family) : Finite ((graph family).neighborSet x) :=
    Nat.finite_of_card_ne_zero (by
      change Nat.card ((DihedralGeometry.graph family).neighborSet x) ≠ 0
      rw [card_neighbors]
      cases x.type <;> decide)
  have hf : ∀ {x y : CosetGeometry.Vertex family}, (graph family).Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hc := BasedWalk.card_nonbacktracking_succ (graph family)
    (fun x : CosetGeometry.Vertex family => x.type) (fun b : Bool => if b then 3 else 5)
    hf card_neighbors 8 v
  rw [stabilizer_card]
  change Nat.card {p : BasedWalk (graph family) (8+1) v // p.Nonbacktracking} = _
  rw [hc]
  cases v.type <;> norm_num [BasedWalk.forwardCount]

/-- The actual Model0 left action on the incidence graph is faithful. -/
theorem left_action_faithful (g : Model 0)
    (hg : ∀v : CosetGeometry.Vertex family,g • v=v) : g=1 := by
  let v := base family false
  let P := {q : BasedWalk (graph family) 9 v // q.Nonbacktracking}
  let : MulAction (stabilizer family v) (BasedWalk (graph family) 9 v) := pathAction family 9 v
  let : MulAction (stabilizer family v) P := nonbacktrackingAction family 9 v
  have hc : Nat.card P=20480 := (nine_path_card v).trans (stabilizer_card v)
  have : Nonempty P := (Nat.card_pos_iff.mp (by omega : 0<Nat.card P)).1
  let p : P := Classical.choice ‹Nonempty P›
  have : Finite (stabilizer family v) := Nat.finite_of_card_ne_zero
    (by rw [stabilizer_card]; change 20480 ≠ 0; decide)
  have ht := (rootPathTransitive_iff family 9 v).mp (rootPathTransitive_nine v)
  let f : stabilizer family v → P := fun a=>a • p
  have hs : Function.Surjective f := fun q=>ht.exists_smul_eq p q
  have hi := ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hs,(nine_path_card v).symm⟩).1
  let a : stabilizer family v := ⟨g,hg v⟩
  have ha : a • p=p := by
    apply Subtype.ext
    apply BasedWalk.vertices_injective 9 v
    change (a • p.val).vertices=p.val.vertices
    rw [vertices_smul_path]
    change p.val.vertices.map (fun w=>g • w)=p.val.vertices
    rw [show (fun w : CosetGeometry.Vertex family=>g • w)=id from funext hg]
    exact List.map_id _
  have he : a=1 := hi (ha.trans (one_smul _ p).symm)
  exact congrArg Subtype.val he

/-- The inducing group element is unique. -/
theorem automorphism_eq_unique_left_action (a : DihedralGeometry.graph family ≃g
    DihedralGeometry.graph family) : ∃!g : Model 0,∀v,a v=g • v := by
  obtain ⟨g,hg⟩ := automorphism_eq_left_action a
  refine ⟨g,hg,?_⟩
  intro h hh
  have he : g⁻¹*h=1 := left_action_faithful _ (fun v=>by
    rw [mul_smul,←hh v,hg v,inv_smul_smul])
  exact (inv_mul_eq_one.mp he).symm
end ReeF4.Octagon.Binary.Automorphisms
