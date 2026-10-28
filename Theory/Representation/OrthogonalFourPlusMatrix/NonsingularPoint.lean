module

public import Theory.Representation.OrthogonalFourPlusMatrix.Action

/-!
# Nonsingular stabilizers in the determinant action

Projection onto the first special linear factor identifies the stabilizer
of an invertible matrix with SL₂. The inverse projection reconstructs the
second factor by conjugating through that matrix. Scalar multiples have
the same point stabilizer, with the original left-right action retained.

Source application: Aschbacher–Smith 9.1.2(4), printed p.729, and the
diagonal residual used in 9.4.1–2, printed pp.735–736.
-/

@[expose] public noncomputable section

open Matrix Subgroup
namespace ClassicalOrthogonal.FourPlusMatrix
variable {F : Type*} [Field F]

def pointStabilizer (v : Mat (F := F)) : Subgroup (PairSL (F := F)) :=
  (MulAction.stabilizer (Mat (F := F) ≃ₗ[F] Mat (F := F)) v).comap matrixHom

theorem mem_pointStabilizer (g : PairSL (F := F)) (v : Mat (F := F)) :
    g ∈ pointStabilizer v ↔ matrixAction g v = v := Iff.rfl

theorem mem_pointStabilizer_iff (g : PairSL (F := F)) (v : Mat (F := F)) :
    g ∈ pointStabilizer v ↔ g.1.val * v = v * g.2.val := by
  change g.1.val * v * g.2⁻¹.val = v ↔ _
  constructor
  · intro h
    have he := congrArg (fun z : Mat (F := F) => z * g.2.val) h
    simpa only [mul_assoc, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, mul_one] using he
  · intro h
    rw [h, mul_assoc, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, mul_one]

def pointProjection (v : Mat (F := F)) :
    pointStabilizer v →* SpecialLinearGroup (Fin 2) F :=
  (MonoidHom.fst _ _).comp (pointStabilizer v).subtype

theorem pointProjection_bijective (v : Mat (F := F)) (hv : v.det ≠ 0) :
    Function.Bijective (pointProjection v) := by
  have hvv : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v (isUnit_iff_ne_zero.mpr hv)
  have hvv' : v⁻¹ * v = 1 := Matrix.nonsing_inv_mul v (isUnit_iff_ne_zero.mpr hv)
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Prod.ext hab
    apply Subtype.ext
    have ha := (mem_pointStabilizer_iff a.val v).mp a.property
    have hb := (mem_pointStabilizer_iff b.val v).mp b.property
    have he : v * a.val.2.val = v * b.val.2.val := by
      rw [← ha, ← hb]
      exact congrArg (fun z : SpecialLinearGroup (Fin 2) F => z.val * v) hab
    have hh := congrArg (fun z : Mat (F := F) => v⁻¹ * z) he
    change a.val.2.val = b.val.2.val
    simpa only [← mul_assoc, hvv', one_mul] using hh
  · intro a
    let b : SpecialLinearGroup (Fin 2) F := ⟨v⁻¹ * a.val * v, by
      rw [Matrix.det_mul, Matrix.det_mul, a.det_coe, mul_one, Matrix.det_nonsing_inv]
      simpa only [Ring.inverse_eq_inv] using inv_mul_cancel₀ hv⟩
    refine ⟨⟨(a,b), (mem_pointStabilizer_iff (a,b) v).mpr ?_⟩,rfl⟩
    change a.val * v = v * (v⁻¹ * a.val * v)
    simp only [← mul_assoc, hvv, one_mul]

def pointStabilizerEquiv (v : Mat (F := F)) (hv : v.det ≠ 0) :
    pointStabilizer v ≃* SpecialLinearGroup (Fin 2) F :=
  MulEquiv.ofBijective (pointProjection v) (pointProjection_bijective v hv)

theorem pointStabilizer_smul (c : F) (hc : c ≠ 0) (v : Mat (F := F)) :
    pointStabilizer (c • v) = pointStabilizer v := by
  ext g
  simp only [mem_pointStabilizer, LinearEquiv.map_smul]
  exact smul_right_inj hc

end ClassicalOrthogonal.FourPlusMatrix
