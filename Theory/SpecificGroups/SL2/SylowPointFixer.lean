module

public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
/-!
# One nonidentity Sylow element detects the whole natural fixed space

In a characteristic-two Sylow subgroup of SL₂(F), a nonidentity element
and the whole Sylow subgroup have the same natural fixed vectors. Conjugate
to the upper root group: a nonzero transvection parameter forces the second
coordinate to vanish. This is the point-centralizer input to Campbell
II.6.3, printed pp.30–31, and includes F=𝔽₂.
-/

public section
open Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Pointwise
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]

theorem upper_fixed_of_nonidentity_fixed (x : SL(2,F)) (hx : x ∈ upperUnipotent F)
    (hne : x ≠ 1) (v : Fin 2 → F) (hv : x • v = v) :
    ∀ y ∈ upperUnipotent F, y • v = v := by
  obtain ⟨t,rfl⟩ := (mem_upperUnipotent F x).mp hx
  have ht : t ≠ 0 := by rintro rfl; exact hne (transvection_coeff_zero _)
  have hh := congrFun hv 0
  simp [SpecialLinearGroup.smul_def,transvection_coe,mulVec,dotProduct,Fin.sum_univ_two] at hh
  have hv1 : v 1 = 0 := hh.resolve_left ht
  intro y hy
  obtain ⟨s,rfl⟩ := (mem_upperUnipotent F y).mp hy
  ext i
  fin_cases i <;>
    simp [SpecialLinearGroup.smul_def,transvection_coe,mulVec,dotProduct,Fin.sum_univ_two,hv1]

variable [Finite F] [CharP F 2]
theorem sylow_fixed_of_nonidentity_fixed (S : Sylow 2 SL(2,F)) (x : SL(2,F))
    (hx : x ∈ S) (hne : x ≠ 1) (v : Fin 2 → F) (hv : x • v = v) :
    ∀ y ∈ S, y • v = v := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq SL(2,F) S (upperUnipotentSylow F 2)
  have hS : (S : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom = upperUnipotent F := by
    change ((a • S : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have hxU : a*x*a⁻¹ ∈ upperUnipotent F := hS ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hx
  have hxN : a*x*a⁻¹ ≠ 1 := by
    intro hz
    apply hne
    have he : (MulAut.conj a) x=(MulAut.conj a) 1 := by simpa using hz
    exact (MulAut.conj a).injective he
  have hxv : (a*x*a⁻¹) • (a • v) = a • v := by
    simp only [mul_smul,inv_smul_smul,hv]
  have hh := upper_fixed_of_nonidentity_fixed (a*x*a⁻¹) hxU hxN (a • v) hxv
  intro y hy
  have hyU : a*y*a⁻¹ ∈ upperUnipotent F := hS ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hy
  have he := congrArg (fun w : Fin 2 → F => a⁻¹ • w) (hh _ hyU)
  simpa only [mul_smul,inv_smul_smul] using he
end Matrix.SpecialLinearGroup
