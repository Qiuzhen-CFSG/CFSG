module

public import Theory.Representation.SL3DoubledNaturalOffenders.Model
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Two

/-!
# Involutory tensor actors are special-linear tensor actors

An actual involutory actor whose action factors through `GL₃(F) × GL₂(F)` can be
rescaled into the literal `SL₃(F) × SL₂(F)` tensor subgroup.  The square of the
factor action first forces reciprocal scalar squares.  In characteristic two,
determinants of the rescaled factors are then one.  This is a normalization of
the concrete tensor action, including the field with two elements; it does not
assume a normalizer, odd degree, or a determinant condition.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.5.9(3) and B.5.10(2), printed pp.107–109.
-/

public section
namespace Representation.SL3DoubledNaturalOffenders
open Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

private theorem square_action (b : Ambient F)
    (g : (Matrix (Fin 3) (Fin 3) F)ˣ) (c : (Matrix (Fin 2) (Fin 2) F)ˣ)
    (hfactors : ∀ (v : Space F) (i : Fin 2),
      (b : Module.End (ZMod 2) (Space F)) v i =
        g.val.mulVec (multiplicity F c.val v i))
    (hb2 : b ^ 2 = 1) (v : Space F) (i : Fin 2) :
    (g.val * g.val).mulVec (multiplicity F (c.val * c.val) v i) = v i := by
  have he := congrArg (fun a : Ambient F => (a : Module.End (ZMod 2) (Space F)) v i) hb2
  change (b : Module.End (ZMod 2) (Space F))
    ((b : Module.End (ZMod 2) (Space F)) v) i = v i at he
  rw [hfactors] at he
  simp only [multiplicity_apply, hfactors, ← Matrix.mulVec_smul, ← Matrix.mulVec_add,
    Matrix.mulVec_mulVec] at he
  rw [multiplicity_mul]
  exact he

/-- A tensor action which is the identity has reciprocal scalar factors. -/
theorem tensor_identity_scalar_factors
    (G : Matrix (Fin 3) (Fin 3) F) (C : Matrix (Fin 2) (Fin 2) F)
    (h : ∀ (v : Space F) (i : Fin 2), G.mulVec (multiplicity F C v i) = v i) :
    ∃ a : F, a ≠ 0 ∧ G = a • (1 : Matrix (Fin 3) (Fin 3) F) ∧
      C = a⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have entry (i j : Fin 2) (k l : Fin 3) :
      C i j * G k l = (1 : Matrix (Fin 2) (Fin 2) F) i j *
        (1 : Matrix (Fin 3) (Fin 3) F) k l := by
    have he := congrFun (h (Pi.single j (Pi.single l 1)) i) k
    fin_cases j <;> fin_cases i <;>
      simpa [multiplicity, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using he
  have hu : C 0 0 * G 0 0 = 1 := by simpa using entry 0 0 0 0
  have hc : C 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hu
  have hg : G 0 0 ≠ 0 := right_ne_zero_of_mul_eq_one hu
  refine ⟨(C 0 0)⁻¹, inv_ne_zero hc, ?_, ?_⟩
  · ext k l
    have he := entry 0 0 k l
    simp only [Matrix.one_apply_eq, one_mul] at he
    change G k l = (C 0 0)⁻¹ * (1 : Matrix (Fin 3) (Fin 3) F) k l
    rw [← he, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · ext i j
    have he := entry i j 0 0
    simp only [Matrix.one_apply_eq, mul_one] at he
    change C i j = ((C 0 0)⁻¹)⁻¹ * (1 : Matrix (Fin 2) (Fin 2) F) i j
    rw [inv_inv]
    apply mul_right_cancel₀ hg
    rw [mul_assoc, mul_comm ((1 : Matrix (Fin 2) (Fin 2) F) i j), ← mul_assoc, hu,
      one_mul, he]

private theorem det_one_of_square_one {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (hM : M * M = 1) : M.det = 1 := by
  let _ : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  apply CharTwo.sq_injective
  simpa only [Matrix.det_mul, Matrix.det_one, pow_two, one_mul] using
    congrArg Matrix.det hM

/-- Reciprocal scalar rescaling makes both involutory factors special linear. -/
theorem tensor_rescale_special
    (g : (Matrix (Fin 3) (Fin 3) F)ˣ) (c : (Matrix (Fin 2) (Fin 2) F)ˣ)
    (a : F) (ha : a ≠ 0)
    (hg : g.val * g.val = a • (1 : Matrix (Fin 3) (Fin 3) F))
    (hc : c.val * c.val = a⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ s : F, s ≠ 0 ∧
      (s⁻¹ • g.val).det = 1 ∧ (s • c.val).det = 1 := by
  have hdg : g.val.det ^ 2 = a ^ 3 := by
    simpa [Matrix.det_mul, Matrix.det_smul, pow_two] using congrArg Matrix.det hg
  have hdc : c.val.det ^ 2 = (a⁻¹) ^ 2 := by
    simpa [Matrix.det_mul, Matrix.det_smul, pow_two] using congrArg Matrix.det hc
  let s := g.val.det * c.val.det
  have hs : s ≠ 0 := mul_ne_zero (Matrix.isUnits_det_units g).ne_zero (Matrix.isUnits_det_units c).ne_zero
  have hs2 : s ^ 2 = a := by
    calc
      s ^ 2 = a ^ 3 * (a⁻¹) ^ 2 := by rw [mul_pow, hdg, hdc]
      _ = a := by field_simp
  refine ⟨s, hs, det_one_of_square_one _ ?_, det_one_of_square_one _ ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two, inv_pow, hs2, hg,
      smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two, hs2, hc,
      smul_smul, mul_inv_cancel₀ ha, one_smul]

private theorem tensor_rescale_action
    (g : Matrix (Fin 3) (Fin 3) F) (c : Matrix (Fin 2) (Fin 2) F)
    (s : F) (hs : s ≠ 0) (v : Space F) (i : Fin 2) :
    (s⁻¹ • g).mulVec (multiplicity F (s • c) v i) =
      g.mulVec (multiplicity F c v i) := by
  have he : multiplicity F (s • c) v i = s • multiplicity F c v i := by
    ext k
    simp [multiplicity, mul_add, mul_assoc]
  rw [he, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hs, one_smul]

/-- An involutory GL₃ × GL₂ tensor actor lies in the actual SL₃ × SL₂ tensor subgroup. -/
theorem involution_mem_tensorSubgroup_of_gl_factors
    [Finite F] (b : Ambient F) (g : (Matrix (Fin 3) (Fin 3) F)ˣ)
    (c : (Matrix (Fin 2) (Fin 2) F)ˣ)
    (hfactors : ∀ (v : Space F) (i : Fin 2),
      (b : Module.End (ZMod 2) (Space F)) v i =
        g.val.mulVec (multiplicity F c.val v i))
    (hb2 : b ^ 2 = 1) : b ∈ tensorSubgroup F := by
  obtain ⟨a, ha, hga, hca⟩ := tensor_identity_scalar_factors
    (g.val * g.val) (c.val * c.val) (fun v i => square_action b g c hfactors hb2 v i)
  obtain ⟨s, hs, hsg, hsc⟩ := tensor_rescale_special g c a ha hga hca
  let g₀ : SL F := ⟨s⁻¹ • g.val, hsg⟩
  let c₀ : MultiplicitySL F := ⟨s • c.val, hsc⟩
  refine ⟨(g₀, c₀), ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  funext i
  change g₀.val.mulVec (multiplicity F c₀.val v i) =
    (b : Module.End (ZMod 2) (Space F)) v i
  dsimp [g₀, c₀]
  exact (tensor_rescale_action g.val c.val s hs v i).trans (hfactors v i).symm

end Representation.SL3DoubledNaturalOffenders
