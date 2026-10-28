module
public import Theory.SpecificGroups.SL3.PRegularClasses.TraceParameters
public import Mathlib.Algebra.CharP.Two
/-!
# The fixed-point-free cubic calculation in the marked three-space

For a cubic matrix with no nonzero fixed vector, g²+g+1 vanishes, by applying
fixed-point freeness to each column. Cayley--Hamilton in determinant one
then gives trace(g)g=trace(g⁻¹)I. The first identity prevents trace(g) from
vanishing in characteristic two, so g is scalar. The next source module
applies this to the original cubic subgroup; no choice of eigenbasis or
compatibility of the two source fields is needed.

Source: Aschbacher--Smith, printed p.774, the cubic Cartan obstruction.
-/

open Matrix Polynomial
open scoped MatrixGroups
public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {F : Type*} [Field F] [CharP F 2]

/-- Every fixed-point-free cubic in SL₃ in characteristic two is scalar. -/
theorem sl3_cubic_scalar_of_fixed_free (g : SL(3,F)) (hg : g^3 = 1)
    (hf : ∀ v : Fin 3 → F, g.val.mulVec v = v → v = 0) :
    ∃ a : F, g.val = a • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hg3 : g.val^3 = 1 := by
    simpa only [SpecialLinearGroup.coe_pow,SpecialLinearGroup.coe_one] using
      congrArg (fun x : SL(3,F) => x.val) hg
  have hp : g.val * (g.val^2 + g.val + 1) = g.val^2 + g.val + 1 := by
    rw [mul_add,mul_add,←pow_succ',hg3,mul_one,←pow_two]
    abel
  have hq : g.val^2 + g.val + 1 = 0 := by
    apply Matrix.ext
    intro i j
    have hv := hf (fun k => ((g.val^2 + g.val + 1 : Matrix (Fin 3) (Fin 3) F)) k j) (by
      funext k
      exact congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M k j) hp)
    exact congrFun hv i
  have hgi : (g⁻¹).val = g.val^2 := by
    have h : g⁻¹ = g^2 := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [←pow_succ] using hg
    rw [h,SpecialLinearGroup.coe_pow]
  have ht : (g.val^2).trace + g.val.trace + 1 = 0 := by
    have h := congrArg Matrix.trace hq
    simp only [trace_add,trace_zero,trace_one,Fintype.card_fin, Nat.cast_ofNat] at h
    rwa [show (3:F) = 1 by linear_combination (CharTwo.two_eq_zero (R := F))] at h
  have hc := Matrix.aeval_self_charpoly g.val
  rw [Theory.SpecificGroups.SL3.PRegularClasses.charpoly_eq_cubic] at hc
  simp only [map_sub,map_add,map_mul,map_pow,aeval_X,aeval_C,map_one,
    Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,hg3,hgi] at hc
  have hc' : g.val.trace • g.val^2 = (g.val^2).trace • g.val := by
    apply sub_eq_zero.mp
    calc
      _ = -(1 - g.val.trace • g.val^2 + (g.val^2).trace • g.val - 1) := by abel
      _ = 0 := by rw [hc,neg_zero]
  have hcm := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M * g.val) hc'
  simp only [smul_mul_assoc,←pow_succ,hg3,←pow_two] at hcm
  have ht0 : g.val.trace ≠ 0 := by
    intro hz
    have hi : (g.val^2).trace = 1 := by
      rw [hz,add_zero] at ht
      exact (eq_neg_of_add_eq_zero_left ht).trans (CharTwo.neg_eq 1)
    rw [hz,zero_smul,hi,one_smul] at hcm
    have hbad : (1 : Matrix (Fin 3) (Fin 3) F) = 0 := by
      calc
        _ = g.val^2 * g.val := hg3.symm
        _ = 0 := by rw [← hcm,zero_mul]
    exact one_ne_zero hbad
  have hc'' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M * (g⁻¹).val) hc'
  have hmul : g.val * (g⁻¹).val = 1 := by
    exact congrArg (fun x : SL(3,F) => x.val) (mul_inv_cancel g)
  have hm2 : g.val^2 * (g⁻¹).val = g.val := by rw [pow_two,mul_assoc,hmul,mul_one]
  simp only [smul_mul_assoc,hm2,hmul] at hc''
  refine ⟨g.val.trace⁻¹ * (g.val^2).trace, ?_⟩
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => g.val.trace⁻¹ • M) hc''
  simpa only [smul_smul,inv_mul_cancel₀ ht0,one_smul] using he
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
