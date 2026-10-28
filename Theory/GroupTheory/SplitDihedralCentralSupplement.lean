module

public import Theory.GroupTheory.SplitDihedralCenter

/-!
# A central involution outside a dihedral subgroup of C2 times D8

The ambient center has order four, whereas the center of a dihedral-eight
subgroup has order two. Thus the former cannot be contained in the latter
subgroup. Its escaping element is an involution and centralizes that
subgroup. This supplies the actual outer Sylow fixer used to recognize
the field extension in Aschbacher--Smith F.6.18(8), printed p.310.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

theorem exists_central_involution_outside_of_split_sixteen
    {T : Type*} [Group T] [Finite T]
    (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (P : Subgroup T) (hP : Nat.card (center P) = 2) :
    ∃ t : T, t ∈ center T ∧ t ∉ P ∧ orderOf t = 2 := by
  have hc : Nat.card (center T) = 4 := by
    rw [Nat.card_congr (centerCongr eT).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hn : ¬ center T ≤ P := by
    intro hle
    let f : center T →* center P := {
      toFun := fun z => ⟨⟨z, hle z.property⟩, by
        rw [mem_center_iff]
        intro x
        exact Subtype.ext (mem_center_iff.mp z.property x)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : center P => ((z : P) : T)) h)
    have hh := Nat.card_le_card_of_injective f hf
    rw [hc, hP] at hh
    omega
  obtain ⟨t, ht, hout⟩ := Set.not_subset.mp hn
  have hsq : (⟨t, ht⟩ : center T) ^ 2 = 1 := by
    apply (centerCongr eT).injective
    have hall : ∀ z : center (Multiplicative (ZMod 2) × DihedralGroup 4), z ^ 2 = 1 := by
      decide +kernel
    simpa only [map_pow, map_one] using hall (centerCongr eT ⟨t, ht⟩)
  refine ⟨t, ht, hout, orderOf_eq_prime ?_ ?_⟩
  · exact congrArg (center T).subtype hsq
  · intro he
    exact hout (he ▸ P.one_mem)

end Theory.GroupTheory
