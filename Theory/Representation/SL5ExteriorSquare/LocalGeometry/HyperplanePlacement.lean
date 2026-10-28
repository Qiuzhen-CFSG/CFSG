module

public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.Centralizer
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Endpoints

/-!
# Placing binary SL₅ actors in the hyperplane parabolic

The actual standard Sylow subgroup moves every two-subgroup into the
four-space parabolic. Inside that parabolic, conjugation on last-column
shears is its upper-left block action. Centralizing every shear forces that
block to be the identity, leaving exactly the shear radical.

These two group calculations supply the global actor step in
Aschbacher–Smith K.3.2.3, printed p.455.
-/

public section
noncomputable section
open Subgroup Representation Representation.SL5TenDimensional
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry.SylowOvergroups
open scoped Pointwise
namespace Representation.SL5ExteriorSquare

/-- Every two-subgroup has a conjugate in the standard hyperplane stabilizer. -/
theorem pGroup_conjugate_le_parabolic_four (A : Subgroup Group) (hA : IsPGroup 2 A) :
    ∃ c : Group, A.map (MulAut.conj c).toMonoidHom ≤ parabolic 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := slEquivLinear 5
  let : Finite (LinearGroup 5) := Finite.of_equiv Group e.toEquiv
  obtain ⟨S, hS⟩ := (hA.map e.toMonoidHom).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup 5) S standardSylow
  refine ⟨e.symm g, ?_⟩
  rintro x ⟨a, ha, rfl⟩
  have hm : g * e a * g⁻¹ ∈ standardBorel := by
    change g * e a * g⁻¹ ∈ (standardSylow : Subgroup _)
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hS (mem_map_of_mem e.toMonoidHom ha))
  have he : e ((e.symm g) * a * (e.symm g)⁻¹) = g * e a * g⁻¹ := by
    simp only [map_mul, map_inv, e.apply_symm_apply]
  rw [← he] at hm
  have ht := (mem_standardBorel_iff _).mp hm
  change ((e.symm (e ((e.symm g) * a * (e.symm g)⁻¹))).val).IsUpperTriangular at ht
  rw [e.symm_apply_apply] at ht
  apply (mem_parabolic_iff_lowerLeft_zero 4 _).mpr
  intro i j hi hj
  exact ht (by change j < i; omega)

/-- The last-column radical is self-centralizing inside its parabolic. -/
theorem parabolic_centralizer_shear_le {g : Group} (hg : g ∈ parabolic 4)
    (hc : g ∈ Subgroup.centralizer (shearSubgroup : Set Group)) : g ∈ shearSubgroup := by
  have hu (u : ShearParameter) : (upperLeft g).mulVec u = u := by
    apply shear_injective
    rw [← parabolic_conjugate_shear g hg]
    have hcomm := (Subgroup.mem_centralizer_iff.mp hc) (shear u) (shear_mem u)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hleft : upperLeft g = 1 := by
    apply Matrix.ext
    intro i j
    have h := congrFun (hu (Pi.single j 1)) i
    simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using h
  have hrow := parabolic_four_last_row g hg
  apply (mem_shearSubgroup g).mpr
  refine ⟨fun i => g.val i.castSucc 4, ?_⟩
  apply Subtype.ext
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [matrix_shear]
    fin_cases j <;> simp [hrow]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [matrix_shear]
      fin_cases i <;> rfl
    · have hl := congrFun (congrFun hleft i) j
      change g.val i.castSucc j.castSucc = _ at hl
      rw [matrix_shear]
      fin_cases i <;> fin_cases j <;> exact hl.symm
end Representation.SL5ExteriorSquare
