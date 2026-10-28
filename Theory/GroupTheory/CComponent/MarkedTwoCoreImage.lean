module

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Retaining marked C-component images through a two-kernel map

Two C-components covering the same whole quotient by the two-core are
equal, by the solvable-kernel component correspondence. Applied after a
surjection with two-group kernel, this identifies the component image
from its representative-preserving quotient formulas.

Source application: the marked degree-four Levi component in
Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed p.959 (PDF p.976), using the correspondence of A.3.3.
-/

public section

open Subgroup
namespace Subgroup
variable {A B S : Type*} [Group A] [Group B] [Group S] [Finite A] [Finite B]

/-- C-components covering the same two-core quotient are compatible with a
prescribed surjection of two-group kernel, including the chosen quotient maps. -/
theorem cComponent_map_eq_of_twoCore_formulas
    (f : A →* B) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (C : Subgroup A) (D : Subgroup B) (hC : C.IsCComponent) (hD : D.IsCComponent)
    (eC : (C ⧸ pCore 2 C) ≃* S) (eD : (D ⧸ pCore 2 D) ≃* S)
    (eB : (B ⧸ pCore 2 B) ≃* S)
    (hc : ∀ c : C, eC (QuotientGroup.mk' _ c) =
      eB (QuotientGroup.mk' _ (f c.val)))
    (hd : ∀ d : D, eD (QuotientGroup.mk' _ d) =
      eB (QuotientGroup.mk' _ d.val)) : C.map f = D := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsNilpotent (pCore 2 B) := pCore_isPGroup.isNilpotent
  apply (cComponent_map_of_solvable_ker hC f hf).eq_of_map_quotient_eq hD (pCore 2 B)
  have hCtop : (C.map f).map (QuotientGroup.mk' (pCore 2 B)) = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨u, hu⟩ := eC.surjective (eB z)
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C) u
    exact mem_map.mpr ⟨f c.val, mem_map.mpr ⟨c, c.property, rfl⟩,
      eB.injective ((hc c).symm.trans hu)⟩
  have hDtop : D.map (QuotientGroup.mk' (pCore 2 B)) = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨u, hu⟩ := eD.surjective (eB z)
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) u
    exact mem_map.mpr ⟨d, d.property, eB.injective ((hd d).symm.trans hu)⟩
  exact hCtop.trans hDtop.symm
end Subgroup

end
