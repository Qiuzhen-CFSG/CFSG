module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Two fixed neighbors in a four-element neighborhood

A nonidentity permutation of four objects fixing two distinct objects fixes
exactly those two. Applied to a graph automorphism fixing a vertex, this
identifies its fixed neighbors. The application to the ternary G₂ torus
makes its fixed graph locally thin without assuming an apartment.

Source context: Aschbacher–Smith F.4.16–17, printed pp.282–283.
-/

@[expose] public section

namespace Equiv.Perm
variable {V : Type*} [Finite V]
theorem fixed_eq_of_card_four (f : Equiv.Perm V) (hcard : Nat.card V = 4)
    {x y z : V} (hx : f x=x) (hy : f y=y) (hxy : x≠y) (hz : f z≠z)
    {w : V} (hw : f w=w) : w=x ∨ w=y := by
  classical
  let := Fintype.ofFinite V
  have hfx : z≠x := by rintro rfl; exact hz hx
  have hfy : z≠y := by rintro rfl; exact hz hy
  have hzx : f z≠x := by intro h; exact hfx (f.injective (h.trans hx.symm))
  have hzy : f z≠y := by intro h; exact hfy (f.injective (h.trans hy.symm))
  have hS : ({x,y,z,f z} : Finset V).card=4 := by
    simp [hxy,hfx.symm,hfy.symm,hzx.symm,hzy.symm,hz.symm]
  have he : ({x,y,z,f z} : Finset V)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [hS,Finset.card_univ,←Nat.card_eq_fintype_card,hcard]
  have hmem : w∈({x,y,z,f z} : Finset V) := he.symm ▸ Finset.mem_univ w
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hz (h ▸ hw)).elim
  · have hfw : f (f z)=f z := h ▸ hw
    exact (hz (f.injective hfw)).elim
end Equiv.Perm

namespace SimpleGraph
variable {V : Type*} {Γ : SimpleGraph V}

theorem fixed_neighbors_of_four (f : Γ ≃g Γ) {x y z w : V}
    [Finite (Γ.neighborSet x)] (hc : Nat.card (Γ.neighborSet x)=4)
    (hx : f x=x) (hy : Γ.Adj x y) (hz : Γ.Adj x z) (hw : Γ.Adj x w)
    (hfy : f y=y) (hfz : f z=z) (hyz : y≠z) (hfw : f w≠w)
    {v : V} (hv : Γ.Adj x v) (hfv : f v=v) : v=y ∨ v=z := by
  have hix : f.symm x=x := by simpa only [hx] using f.symm_apply_apply x
  let e : Equiv.Perm (Γ.neighborSet x) :=
    { toFun := fun v => ⟨f v,by
          have h := f.toHom.map_adj v.property
          change Γ.Adj (f x) (f v) at h
          rwa [hx] at h⟩
      invFun := fun v => ⟨f.symm v,by
          have h := f.symm.toHom.map_adj v.property
          change Γ.Adj (f.symm x) (f.symm v) at h
          rwa [hix] at h⟩
      left_inv := fun v => Subtype.ext (f.symm_apply_apply v)
      right_inv := fun v => Subtype.ext (f.apply_symm_apply v) }
  have h := Equiv.Perm.fixed_eq_of_card_four e hc
    (x := ⟨y,hy⟩) (y := ⟨z,hz⟩) (z := ⟨w,hw⟩)
    (Subtype.ext hfy) (Subtype.ext hfz) (fun h => hyz (congrArg Subtype.val h))
    (fun h => hfw (congrArg Subtype.val h)) (w := ⟨v,hv⟩) (Subtype.ext hfv)
  exact h.imp (congrArg Subtype.val) (congrArg Subtype.val)
end SimpleGraph
