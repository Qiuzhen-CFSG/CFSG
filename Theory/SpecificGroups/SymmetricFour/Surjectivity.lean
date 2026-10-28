module
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Mathlib.Data.Fintype.Perm

/-!
# A full four-point action from an escaping subgroup

A subgroup of S₄ containing a subgroup of order eight is either that subgroup
or S₄, since the former has prime index three. If an action kernel and the
original eight-image subgroup lie in a proper subgroup of the acting group,
the first alternative is impossible. This supplies the full S₄ image in the
Γ-action of Aschbacher–Smith 10.2.1, printed p.743.
-/
public section
namespace Subgroup
variable {H : Type*} [Group H]
theorem surjective_perm_four_of_kernel_le_and_eight_image
    (f : H →* Equiv.Perm (Fin 4)) (S M : Subgroup H)
    (hS : S ≤ M) (hk : f.ker ≤ M) (hM : M ≠ ⊤)
    (hcard : Nat.card (S.map f) = 8) : Function.Surjective f := by
  have hfull : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  have hi : (S.map f).index = 3 := by
    have hc := (S.map f).card_mul_index
    rw [hcard,hfull] at hc
    omega
  rcases (isCoatom_of_index_three (S.map f) hi).le_iff.mp (map_le_range f S) with he | he
  · exact MonoidHom.range_eq_top.mp he
  · have hf : S ⊔ f.ker = ⊤ := by
      have hc := congrArg (Subgroup.comap f) he
      rw [comap_map_eq] at hc
      exact hc.symm.trans (top_unique (fun x _ => ⟨x,rfl⟩))
    exact (hM (top_unique (hf ▸ sup_le hS hk))).elim
end Subgroup
