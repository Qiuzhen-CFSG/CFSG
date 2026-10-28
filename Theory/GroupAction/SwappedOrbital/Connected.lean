module
public import Theory.GroupAction.SwappedOrbital
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Connectivity and a positive nonadjacent intersection number

A nontrivial orbital graph of a primitive group is connected: reachable
components are blocks. A connected noncomplete strongly regular graph has
positive μ, since μ=0 would make adjacency transitive along every walk.
These elementary reductions rule out the empty opposite-class choice in J.5.5.
-/

public section
noncomputable section
open scoped Pointwise
namespace MulAction.SwappedOrbital
open MulAction
variable {G Ω:Type*} [Group G] [MulAction G Ω]
variable (a b:Ω) (hab:a≠b) (t:G) (hta:t•a=b) (htb:t•b=a)

theorem connected [IsPreprimitive G Ω] : (graph a b hab t hta htb).Connected := by
  let Γ:=graph a b hab t hta htb
  let S:Set Ω:={x|Γ.Reachable a x}
  have hs (g:G) : g•S={x|Γ.Reachable (g•a) x}:=by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy.map (automorphism a b hab t hta htb g).toHom
    · intro h
      refine ⟨g⁻¹•x,?_,smul_inv_smul _ _⟩
      have hh:=h.map (automorphism a b hab t hta htb g⁻¹).toHom
      change Γ.Reachable (g⁻¹•(g•a)) (g⁻¹•x) at hh
      change Γ.Reachable a (g⁻¹•x)
      simpa only [inv_smul_smul] using hh
  have hb:IsBlock G S:=by
    intro g h hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    rw [hs] at hx hy
    apply hne
    rw [hs,hs]
    have hh:Γ.Reachable (g•a) (h•a):=hx.trans hy.symm
    ext y
    exact ⟨fun hz=>hh.symm.trans hz,fun hz=>hh.trans hz⟩
  have hu:S=Set.univ:=by
    rcases hb.subsingleton_or_eq_univ with hh|hh
    · exact (hab (hh SimpleGraph.Reachable.rfl
        (show Γ.Adj a b from ⟨1,one_smul _ _,one_smul _ _⟩).reachable)).elim
    · exact hh
  let : Nonempty Ω:=⟨a⟩
  refine ⟨?_⟩
  intro x y
  have hx:Γ.Reachable a x:=by change x∈S; rw [hu]; trivial
  have hy:Γ.Reachable a y:=by change y∈S; rw [hu]; trivial
  exact hx.symm.trans hy

end MulAction.SwappedOrbital

namespace SimpleGraph
variable {Ω:Type*} [Fintype Ω] (Γ:SimpleGraph Ω) [DecidableRel Γ.Adj]

theorem IsSRGWith.mu_pos_of_connected {n k l m:ℕ} (h:Γ.IsSRGWith n k l m)
    (hconn:Γ.Connected) {a c:Ω} (hac:a≠c) (hna:¬Γ.Adj a c) : 0<m := by
  by_contra hm
  have hm0:m=0:=by omega
  have ht {x y z:Ω} (hxy:Γ.Adj x y) (hyz:Γ.Adj y z) (hxz:x≠z) : Γ.Adj x z:=by
    by_contra hnxz
    have hc:0<Fintype.card (Γ.commonNeighbors x z):=by
      apply Fintype.card_pos_iff.mpr
      exact ⟨⟨y,⟨hxy,hyz.symm⟩⟩⟩
    rw [h.of_not_adj hxz hnxz,hm0] at hc
    omega
  have hw {x y:Ω} (p:Γ.Walk x y) : x=y ∨ Γ.Adj x y:=by
    induction p with
    | nil => exact Or.inl rfl
    | @cons u v w huv p ih =>
      rcases ih with hh|hh
      · subst w; exact Or.inr huv
      · by_cases he:u=w
        · exact Or.inl he
        · exact Or.inr (ht huv hh he)
  obtain ⟨p⟩:=hconn a c
  exact (hw p).elim hac hna

end SimpleGraph
