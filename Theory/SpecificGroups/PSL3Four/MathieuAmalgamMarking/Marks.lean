module

public import Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Canonical
import all Theory.SpecificGroups.PSL3Four.MathieuAmalgamMarking.Matrices

/-!
# Exact shared torus, reflection, and exterior cubic

The same canonical point generators retain a cubic torus, its involutory
inverter, and the exterior cubic. Their orders and conjugation identities are
proved in the actual canonical projective quotient, including scalar factors.
-/

public noncomputable section
open Matrix Subgroup
namespace Matrix.PSL3Four.MathieuAmalgamMarking

private theorem project_eq_one_iff (g : NativeSL) : project g = 1 ↔
    ∃ a : NativeF, a^3=1 ∧ scalar (Fin 3) a = g.val := by
  refine ⟨?_,fun ⟨a,ha,hg⟩ => project_scalar g a ha hg⟩
  intro hg
  have hc : fieldMap g ∈ center SL := (QuotientGroup.eq_one_iff (fieldMap g)).mp hg
  obtain ⟨c,hc,hmat⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨Representation.SL2FourNatural.fieldEquiv.symm c,?_,?_⟩
  · rw [←map_pow,show c^3=1 from hc,map_one]
  · funext i j
    apply Representation.SL2FourNatural.fieldEquiv.injective
    have he := congrFun (congrFun hmat i) j
    change (scalar (Fin 3) c) i j = Representation.SL2FourNatural.fieldEquiv (g.val i j) at he
    rw [←he]
    by_cases hij : i=j <;> simp [Matrix.scalar,Matrix.diagonal,hij]

private theorem project_eq_of_scalar (g k : NativeSL)
    (h : ∃ a : NativeF, a^3=1 ∧ scalar (Fin 3) a = (g*k⁻¹).val) :
    project g = project k := by
  have he := (project_eq_one_iff _).mpr h
  rw [map_mul,map_inv] at he
  exact mul_inv_eq_one.mp he

/-- The canonical shared torus and exterior cubic have order3, and their
shared inverter has order2. -/
theorem canonical_orders : orderOf torus = 3 ∧ orderOf reflection = 2 ∧ orderOf cycle = 3 := by
  have ht : nativeTorus^3=1 := by decide +kernel
  have hr : nativeReflection^2=1 := by decide +kernel
  have he : nativeCycle^3=1 := by decide +kernel
  have htn : torus≠1 := by rw [ne_eq,torus,project_eq_one_iff]; decide +kernel
  have hrn : reflection≠1 := by rw [ne_eq,reflection,project_eq_one_iff]; decide +kernel
  have hen : cycle≠1 := by rw [ne_eq,cycle,project_eq_one_iff]; decide +kernel
  refine ⟨orderOf_eq_prime ?_ htn,orderOf_eq_prime ?_ hrn,orderOf_eq_prime ?_ hen⟩
  · exact (map_pow project nativeTorus 3).symm.trans ((congrArg project ht).trans project.map_one)
  · exact (map_pow project nativeReflection 2).symm.trans ((congrArg project hr).trans project.map_one)
  · exact (map_pow project nativeCycle 3).symm.trans ((congrArg project he).trans project.map_one)

/-- These exact literal elements commute and invert in the original projective carrier. -/
theorem canonical_cubic_relations : Commute cycle torus ∧
    reflection*torus*reflection⁻¹=torus⁻¹ ∧
    reflection*cycle*reflection⁻¹=cycle⁻¹ := by
  constructor
  · change project nativeCycle * project nativeTorus = project nativeTorus * project nativeCycle
    rw [←map_mul,←map_mul]
    apply project_eq_of_scalar
    decide +kernel
  constructor
  · change project nativeReflection * project nativeTorus * (project nativeReflection)⁻¹ =
      (project nativeTorus)⁻¹
    rw [←map_inv,←map_mul,←map_mul,←map_inv]
    apply project_eq_of_scalar
    decide +kernel
  · change project nativeReflection * project nativeCycle * (project nativeReflection)⁻¹ =
      (project nativeCycle)⁻¹
    rw [←map_inv,←map_mul,←map_mul,←map_inv]
    apply project_eq_of_scalar
    decide +kernel

end Matrix.PSL3Four.MathieuAmalgamMarking
