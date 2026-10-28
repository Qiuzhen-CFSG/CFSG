module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Stabilizers
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow

/-!
# Aligning a binary exterior marking with a Sylow flag

The standard upper-triangular Sylow of GL₅(2) pulls back to the literal
flag group used by the exterior geometry. Sylow conjugacy therefore puts
any two-subgroup into that flag group. This supplies the coordinate change
in the notation preceding Aschbacher--Smith 12.5.2, printed p.817.
-/

@[expose] public noncomputable section
open Subgroup
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional BinaryLinear.OuterCyclic
open BinaryLinear.FiveFlagGeometry.SylowOvergroups

/-- The concrete full-flag Sylow agrees with the wedge geometry's flag group. -/
theorem flagGroup_eq_standardBorel_comap :
    flagGroup = standardBorel.comap (slEquivLinear 5).toMonoidHom := by
  ext g
  simp only [flagGroup, mem_iInf, mem_comap]
  rw [mem_standardBorel_iff]
  change (∀ k : Fin 5, g ∈ parabolic k.val) ↔
    (((slEquivLinear 5).symm ((slEquivLinear 5) g)).val).IsUpperTriangular
  rw [MulEquiv.symm_apply_apply]
  simp only [mem_parabolic_iff_lowerLeft_zero]
  constructor
  · intro h i j hji
    exact h i i j (le_refl _) hji
  · intro h k i j hi hj
    exact h (lt_of_lt_of_le hj hi)

/-- Every two-subgroup can be conjugated into the actual standard flag group. -/
theorem exists_conjugate_le_flagGroup (P : Subgroup Group) (hP : IsPGroup 2 P) :
    ∃ g : Group, P.map (MulAut.conj g).toMonoidHom ≤ flagGroup := by
  let f := slEquivLinear 5
  obtain ⟨Q, hQ⟩ := (hP.map f.toMonoidHom).exists_le_sylow
  let : Finite (LinearGroup 5) :=
    Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
      DFunLike.coe_injective
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (LinearGroup 5) Q standardSylow
  refine ⟨f.symm x, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [flagGroup_eq_standardBorel_comap]
  change f (f.symm x * y * (f.symm x)⁻¹) ∈ standardBorel
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hyQ := hQ (mem_map_of_mem f.toMonoidHom hy)
  have hm : x * f y * x⁻¹ ∈ (x • Q : Sylow 2 (LinearGroup 5)) := by
    change x * f y * x⁻¹ ∈ ((Q : Subgroup (LinearGroup 5)).map
      (MulAut.conj x).toMonoidHom)
    exact mem_map_of_mem _ hyQ
  rw [hx] at hm
  exact hm
end Representation.SL5ExteriorSquare
