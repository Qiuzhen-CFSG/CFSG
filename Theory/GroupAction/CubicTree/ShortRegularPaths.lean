module
public import Theory.GroupAction.CubicTree.ArcTransport
public import Mathlib.Data.Fintype.Card

/-!
# Simple paths below the first failure of regularity

At valence at least three, a right-regular walk cannot have a forward
neighbor among its fixed vertices. Induction on prefixes therefore makes
all nonbacktracking walks through the first nonregular length simple.
No acyclicity or finiteness of the whole graph is needed.

Source: DGS, *Groups and Graphs* (1985), path convention p.60 and
regularity definitions pp.73--74.
-/

public noncomputable section
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
namespace Theory.GroupAction.CubicTree
variable {V A : Type*} {Γ : SimpleGraph V} [Group A] [MulAction A V]

/-- The number of forward choices at a nonempty walk. -/
theorem card_forward_succ {n : ℕ} {x : V} (p : BasedWalk Γ (n+1) x)
    [Finite (Γ.neighborSet p.endpoint)] :
    Nat.card {z : V // Forward p z} = Nat.card (Γ.neighborSet p.endpoint) - 1 := by
  classical
  let : Fintype (Γ.neighborSet p.endpoint) := Fintype.ofFinite _
  let e : {z : V // Forward p z} ≃
      {z : Γ.neighborSet p.endpoint // z ≠ ⟨p.penultimate, p.adj_penultimate_endpoint.symm⟩} := {
    toFun z := ⟨⟨z, z.property.1⟩, fun he => z.property.2 (congrArg Subtype.val he)⟩
    invFun z := ⟨z.val, z.val.property, fun he => z.property (Subtype.ext he)⟩
    left_inv z := rfl
    right_inv z := rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card]
  simp

/-- Valence at least three leaves at least two forward choices. -/
theorem forward_card_gt_one (hval : ∀ x, 3 ≤ Nat.card (Γ.neighborSet x))
    {n : ℕ} {x : V} (p : BasedWalk Γ n x) :
    1 < Nat.card {z : V // Forward p z} := by
  cases n with
  | zero => exact lt_of_lt_of_le (by decide : 1 < 3) (hval x)
  | succ n =>
    let : Finite (Γ.neighborSet p.endpoint) := Nat.finite_of_card_ne_zero (by have := hval p.endpoint; omega)
    rw [card_forward_succ]
    have := hval p.endpoint
    omega

/-- A forward choice fixed by the walk fixer prevents right regularity. -/
theorem forward_not_mem_vertices_of_rightRegular
    (hval : ∀ x, 3 ≤ Nat.card (Γ.neighborSet x))
    {n : ℕ} {x z : V} (p : BasedWalk Γ n x) (hr : RightRegular (A := A) p)
    (hz : Forward p z) : z ∉ p.vertices := by
  intro hm
  have hc : 1 < ({w : V | Forward p w} : Set V).ncard := by
    rw [←Nat.card_coe_set_eq]
    exact forward_card_gt_one hval p
  obtain ⟨w,hw,hne⟩ := Set.exists_ne_of_one_lt_ncard hc z
  obtain ⟨a,ha,he⟩ := hr z w hz hw
  exact hne (he.symm.trans (ha z hm))

/-- All nonbacktracking walks through the first nonregular length are simple. -/
theorem isPath_of_short_rightRegular
    (hval : ∀ x, 3 ≤ Nat.card (Γ.neighborSet x)) (s : ℕ)
    (hshort : ∀ n < s, ∀ x, ∀ p : BasedWalk Γ n x,
      p.Nonbacktracking → RightRegular (A := A) p)
    {n : ℕ} {x : V} (p : BasedWalk Γ n x) (hn : n ≤ s)
    (hp : p.Nonbacktracking) : p.toWalk.IsPath := by
  have hnodup : p.vertices.Nodup := by
    induction n generalizing x with
    | zero => simp [BasedWalk.vertices]
    | succ n ih =>
      let q := p.take n (Nat.le_succ n)
      have hq : q.Nonbacktracking := nonbacktracking_take _ p hp
      have hadj : Γ.Adj q.endpoint p.endpoint := by
        simpa only [q, endpoint_take_penultimate] using p.adj_penultimate_endpoint
      have hf : Forward q p.endpoint := by
        apply (forward_iff_snoc_nonbacktracking q hq hadj).mpr
        simpa only [q,snoc_take] using hp
      have hnew := forward_not_mem_vertices_of_rightRegular hval q
        (hshort n (by omega) x q hq) hf
      rw [vertices_eq_prefix_append_endpoint]
      exact (List.nodup_append).mpr ⟨ih q (by omega) hq,by simp,by
        intro a ha b hb _
        simp only [List.mem_singleton] at hb
        subst b
        apply hnew
        rw [← hb]
        simpa [q] using ha⟩
  exact SimpleGraph.Walk.IsPath.mk' (by rwa [support_toWalk])
end Theory.GroupAction.CubicTree
