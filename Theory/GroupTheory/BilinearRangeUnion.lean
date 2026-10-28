module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Bilinear pairings taking values in two subgroups

A map of groups that is multiplicative in both variables and takes values in
the union of two subgroups takes all its values in one of those subgroups.
First apply the subgroup-union lemma to each row. The sets of rows taking
values in either subgroup are themselves subgroups, so a second application
finishes the proof.

Source: the elementary subgroup-union argument, as formalized in
`SubgroupClass.subset_union`.
-/

namespace Subgroup

/-- A pairing multiplicative in both variables cannot have its image covered
by two subgroups without having its entire image in one of them. -/
public theorem bilinear_range_subset_union
    {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X → Y → Z)
    (hl : ∀ x x' y, f (x * x') y = f x y * f x' y)
    (hr : ∀ x y y', f x (y * y') = f x y * f x y')
    (H K : Subgroup Z) (hf : ∀ x y, f x y ∈ H ∨ f x y ∈ K) :
    (∀ x y, f x y ∈ H) ∨ (∀ x y, f x y ∈ K) := by
  let row (x : X) : Y →* Z := MonoidHom.mk' (f x) (hr x)
  let col (y : Y) : X →* Z := MonoidHom.mk' (fun x => f x y) (fun x x' => hl x x' y)
  let L (S : Subgroup Z) : Subgroup X := ⨅ y, S.comap (col y)
  have hL (S : Subgroup Z) (x : X) : x ∈ L S ↔ ∀ y, f x y ∈ S := by
    simp only [L, mem_iInf, mem_comap, col, MonoidHom.mk'_apply]
  have hrow (x : X) : x ∈ L H ∨ x ∈ L K := by
    have h : (row x).range ≤ H ∨ (row x).range ≤ K :=
      SubgroupClass.subset_union.mp (by
        rintro _ ⟨y, rfl⟩
        exact hf x y)
    exact h.imp (fun hh => (hL H x).mpr (fun y => hh ⟨y, rfl⟩))
      (fun hh => (hL K x).mpr (fun y => hh ⟨y, rfl⟩))
  have h : (⊤ : Subgroup X) ≤ L H ∨ (⊤ : Subgroup X) ≤ L K :=
    SubgroupClass.subset_union.mp (fun x _ => hrow x)
  exact h.imp (fun hh x => (hL H x).mp (hh (mem_top x)))
    (fun hh x => (hL K x).mp (hh (mem_top x)))

end Subgroup
