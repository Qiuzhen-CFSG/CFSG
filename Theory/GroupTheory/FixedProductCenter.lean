module
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Center of a product fixed by a factor conjugator

Let `C` and `D` be abelian subgroups such that `C` normalizes `D`.
If conjugation by `y` sends `C` to `D` and fixes the center of `C ⊔ D`
pointwise, that center, viewed in the ambient group, equals `C ⊓ D`.
No finiteness, prime, or normalization hypothesis on `y` is needed.

Write a central element as `c * d`. Since each factor is abelian,
cancelling the other factor shows that both components centralize both
factors, and hence belong to the product center. Conjugation fixes both
components. It carries the component in `C` into `D`, and injectivity
carries the fixed component in `D` back into `C`. Thus both lie in the
intersection. Conversely, the intersection centralizes both generators.

This general normalized-product argument supplies the center identity used
before the elementary seed construction in Stellmacher (9.1), relation (3),
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Subgroup

/-- A factor conjugator fixing the product center identifies that center
with the intersection of the two abelian factors. -/
public theorem center_sup_eq_inf_of_fixed_conjugator
    {G : Type*} [Group G] (C D : Subgroup G)
    [IsMulCommutative C] [IsMulCommutative D]
    (hn : C ≤ normalizer (D : Set G)) (y : G)
    (hconj : C.conjBy y = D)
    (hfix : y ∈ centralizer
      (((center ↥(C ⊔ D)).map (C ⊔ D).subtype : Subgroup G) : Set G)) :
    (center ↥(C ⊔ D)).map (C ⊔ D).subtype = C ⊓ D := by
  let V := C ⊔ D
  let Z := (center V).map V.subtype
  have hZiff (x : G) : x ∈ Z ↔
      x ∈ V ∧ x ∈ centralizer (C : Set G) ∧ x ∈ centralizer (D : Set G) := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hc (a : G) (ha : a ∈ V) : a * (z : G) = (z : G) * a :=
        congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)
      exact ⟨z.property, fun a ha => hc a (mem_sup_left ha),
        fun a ha => hc a (mem_sup_right ha)⟩
    · rintro ⟨hx, hC, hD⟩
      refine ⟨⟨x, hx⟩, mem_center_iff.mpr ?_, rfl⟩
      have hV : V ≤ centralizer ({x} : Set G) := sup_le
        (fun a ha => mem_centralizer_singleton_iff.mpr (hC a ha))
        (fun a ha => mem_centralizer_singleton_iff.mpr (hD a ha))
      intro a
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hV a.property)
  have hfixed (x : G) (hx : x ∈ Z) : (MulAut.conj y) x = x := by
    change y * x * y⁻¹ = x
    rw [← mem_centralizer_iff.mp hfix x hx, mul_inv_cancel_right]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxC, hxD⟩ := (hZiff x).mp hx
    have hxprod : x ∈ (C : Set G) * (D : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right C D hn]
      exact hxV
    obtain ⟨c, hc, d, hd, hcd⟩ := hxprod
    have hcD : c ∈ centralizer (D : Set G) := by
      have h := (centralizer (D : Set G)).mul_mem hxD
        ((centralizer (D : Set G)).inv_mem (D.le_centralizer hd))
      rw [← hcd] at h
      simpa only [mul_inv_cancel_right] using h
    have hdC : d ∈ centralizer (C : Set G) := by
      have h := (centralizer (C : Set G)).mul_mem
        ((centralizer (C : Set G)).inv_mem (C.le_centralizer hc)) hxC
      rw [← hcd] at h
      simpa only [inv_mul_cancel_left] using h
    have hcZ : c ∈ Z := (hZiff c).mpr ⟨mem_sup_left hc, C.le_centralizer hc, hcD⟩
    have hdZ : d ∈ Z := (hZiff d).mpr ⟨mem_sup_right hd, hdC, D.le_centralizer hd⟩
    have hcD' : c ∈ D := by
      rw [← hconj]
      exact ⟨c, hc, hfixed c hcZ⟩
    have hdC' : d ∈ C := by
      have hd' : d ∈ C.conjBy y := hconj.symm ▸ hd
      obtain ⟨a, ha, he⟩ := hd'
      have had : a = d := (MulAut.conj y).injective (he.trans (hfixed d hdZ).symm)
      exact had ▸ ha
    rw [← hcd]
    exact ⟨C.mul_mem hc hdC', D.mul_mem hcD' hd⟩
  · intro x hx
    exact (hZiff x).mpr ⟨mem_sup_left hx.1, C.le_centralizer hx.1,
      D.le_centralizer hx.2⟩
end Subgroup
