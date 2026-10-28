module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# The exact strongly regular parameters

A vertex-transitive strongly regular graph with fifteen vertices and valency six cannot have zero nonadjacent common-neighbor parameter: its closed neighborhoods would be blocks of size seven. The standard parameter equation then forces lambda one and mu three.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open scoped Pointwise
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G X:Type*} [Group G] [Fintype X] [MulAction G X] [MulAction.IsPretransitive G X]
variable (Γ:SimpleGraph X) [DecidableRel Γ.Adj]

private theorem mu_ne_zero_of_parameters {l m:ℕ} (h:Γ.IsSRGWith 15 6 l m)
    (hinv:∀g:G,∀x y:X,Γ.Adj (g • x) (g • y)↔Γ.Adj x y):m≠0 := by
  classical
  intro hm
  let R:X→X→Prop:=fun x y=>x=y ∨ Γ.Adj x y
  have hs:∀{x y:X},R x y→R y x:=fun {x y} hh=>hh.elim (fun he=>Or.inl he.symm) (fun he=>Or.inr he.symm)
  have ht:∀{x y z:X},R x y→R y z→R x z := by
    intro x y z hxy hyz
    rcases hxy with rfl|hxy
    · exact hyz
    rcases hyz with rfl|hyz
    · exact Or.inr hxy
    by_cases he:x=z
    · exact Or.inl he
    right
    by_contra hn
    have hc:=h.of_not_adj he hn
    rw [hm] at hc
    have hp:0<Fintype.card (Γ.commonNeighbors x z):=Fintype.card_pos_iff.mpr
      ⟨⟨y,hxy,hyz.symm⟩⟩
    omega
  have hR (g:G) {x y:X} (hh:R x y):R (g • x) (g • y) := by
    rcases hh with rfl|hh
    · exact Or.inl rfl
    · exact Or.inr ((hinv g _ _).mpr hh)
  have hx:Nonempty X:=Fintype.card_pos_iff.mp (by rw [h.card]; decide)
  let a:X:=Classical.choice hx
  let S:Set X:={x | R a x}
  have hS:MulAction.IsBlock G S := by
    apply MulAction.isBlock_iff_smul_eq_of_mem.mpr
    intro g b hb hgb
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ht hgb (hR g (ht (hs hb) hy))
    · intro hxS
      refine ⟨g⁻¹ • x,?_,smul_inv_smul g x⟩
      have hh:=hR g⁻¹ (ht (hs hgb) hxS)
      simp only [inv_smul_smul] at hh
      exact ht hb hh
  have hScard:S.ncard=7 := by
    have he:S=insert a (Γ.neighborSet a) := by
      ext x
      simp only [S,R,Set.mem_ofPred_eq,Set.mem_insert_iff,SimpleGraph.mem_neighborSet]
      rw [eq_comm]
    rw [he,Set.ncard_insert_of_notMem (Γ.notMem_neighborSet_self (a:=a))]
    change Nat.card (Γ.neighborSet a)+1=7
    rw [Nat.card_eq_fintype_card]
    rw [Γ.card_neighborSet_eq_degree]
    rw [h.regular a]
  have hd:=hS.ncard_dvd_card (show S.Nonempty from ⟨a,Or.inl rfl⟩)
  rw [hScard,Nat.card_eq_fintype_card,h.card] at hd
  norm_num at hd

theorem exact_rank_three_parameters {l m:ℕ} (h:Γ.IsSRGWith 15 6 l m)
    (hinv:∀g:G,∀x y:X,Γ.Adj (g • x) (g • y)↔Γ.Adj x y):l=1 ∧ m=3 := by
  have hm:=mu_ne_zero_of_parameters Γ h hinv
  have he:=h.param_eq Γ (by decide)
  norm_num at he
  omega
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
