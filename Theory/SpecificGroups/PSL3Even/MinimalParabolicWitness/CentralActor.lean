module

public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Center
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner
import Mathlib.Tactic.LinearCombination

/-!
# Central displacement forces an involutory actor to be inner

An actor acting trivially on UT₃ modulo its center preserves each root plane,
so the actual diagram kernel makes it linear-field. Sylow preservation makes
its linear matrix triangular. The first simple-root coordinate then reads
m₀₀ σ(t)=t m₁₁; parameter one and invertibility force σ=1. The remaining
linear involution is inner by the coprime determinant calculation.

Source: the elementary normal subgroup placement in Aschbacher--Smith E.2.7,
printed p.219; standard actor coordinates are GLS3 §§2.5 and 2.7.
-/

public section
open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.RootPlaneGeometry Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3Even.AutomorphismCoverage.RootOrientation
open Matrix.PSL3.OuterSolvable Matrix.PSL3.CartanActions Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3Even.MinimalParabolicWitness
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem center_le_plane (b : Bool) : projectiveCenter F ≤ rootPlane F b := by
  rw [rootPlane_eq_map]
  apply map_mono
  cases b <;> intro u hu
  · exact (mem_V₂ F u).mpr ((mem_Z F u).mp hu).1
  · exact (mem_V₁ F u).mpr ((mem_Z F u).mp hu).2

omit [Finite F] [CharP F 2] in
private theorem plane_le_upper (b : Bool) : rootPlane F b ≤ unipotent F := by
  rw [rootPlane]
  exact (map_mono (rootPlaneSL_le_unipotent F b))

omit [Finite F] [CharP F 2] in
private theorem field_projective (σ : F ≃+* F) (u : U F) :
    fieldAction F σ (projective F u) = projective F ⟨σ u.x, σ u.y, σ u.c⟩ := by
  change fieldAction F σ (QuotientGroup.mk (specialLinear F u)) =
    QuotientGroup.mk (specialLinear F ⟨σ u.x, σ u.y, σ u.c⟩)
  rw [fieldAction_mk]
  congr 1
  apply Subtype.ext
  ext i j
  change σ (matrix F u i j) = matrix F ⟨σ u.x, σ u.y, σ u.c⟩ i j
  fin_cases i <;> fin_cases j <;> simp [matrix]

omit [Finite F] [CharP F 2] in
private theorem scalar_of_projection_eq (x y : SL(3,F))
    (h : projection F x = projection F y) : ∃ r : F, x.val = r • y.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

omit [Finite F] [CharP F 2] in
private theorem triangular_entry_ne_zero (m : GL (Fin 3) F) (hm : m ∈ glBorel F) :
    m.val 0 0 ≠ 0 := by
  have hn : Matrix.det m.val ≠ 0 := (GeneralLinearGroup.det m).ne_zero
  rw [Matrix.det_fin_three] at hn
  simp only [hm.1,hm.2.1,hm.2.2,mul_zero,zero_mul,sub_zero,add_zero] at hn
  exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1

omit [Finite F] [CharP F 2] in
private theorem first_coordinate (m : GL (Fin 3) F) (hm : m ∈ glBorel F)
    (σ : F ≃+* F) (t c : F)
    (h : (linearConj F m * fieldAction F σ) (projective F ⟨t,0,0⟩) =
      projective F ⟨t,0,c⟩) : m.val 0 0 * σ t = t * m.val 1 1 := by
  rw [MulAut.mul_apply, field_projective] at h
  have hp : projection F (linearConjSL F m (specialLinear F ⟨σ t,0,0⟩)) =
      projection F (specialLinear F ⟨t,0,c⟩) := by
    simp only [map_zero] at h
    exact (linearConj_mk F m (specialLinear F ⟨σ t,0,0⟩)).symm.trans h
  obtain ⟨r,hr⟩ := scalar_of_projection_eq F _ _ hp
  have hv : (linearConjSL F m (specialLinear F ⟨σ t,0,0⟩)).val =
      m.val * matrix F ⟨σ t,0,0⟩ * m.inv :=
    congrArg Units.val (linearConjSL_toGL F m _)
  have he : m.val * matrix F ⟨σ t,0,0⟩ = (r • matrix F ⟨t,0,c⟩) * m.val := by
    rw [← show (specialLinear F ⟨t,0,c⟩).val = matrix F ⟨t,0,c⟩ from rfl,
      ← hr, hv, Matrix.mul_assoc, m.inv_val, mul_one]
  have h00 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 0) he
  have h00 : m.val 0 0 = r * m.val 0 0 := by
    simpa [matrix, Matrix.mul_apply, Fin.sum_univ_three, hm.1, hm.2.1] using h00
  have hr1 : r = 1 := (mul_eq_right₀ (triangular_entry_ne_zero F m hm)).mp h00.symm
  rw [hr1, one_smul] at he
  have h01 := congrArg (fun a : Matrix (Fin 3) (Fin 3) F => a 0 1) he
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, hm.2.2] at h01
  linear_combination h01

/-- The conclusion is actual innerness in the full automorphism group. -/
theorem inner_of_central_displacement {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut PSL(3,F)) (ha : (unipotent F).map a.toMonoidHom = unipotent F)
    (hp : a ^ 2 = 1)
    (hd : ∀ u ∈ unipotent F, a u * u⁻¹ ∈ projectiveCenter F) :
    a ∈ MulAut.innerSubgroup PSL(3,F) := by
  have hplane : (rootPlane F true).map a.toMonoidHom = rootPlane F true := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      have hz := center_le_plane F true (hd u (plane_le_upper F true hu))
      have hh := (rootPlane F true).mul_mem hz hu
      change a u ∈ rootPlane F true
      simpa only [inv_mul_cancel_right] using hh
    · rw [Subgroup.card_map_of_injective a.injective]
  have hlin : a ∈ linearField F := by
    apply (mapsParabolicType_self_iff_mem_linearField F hn hF a true).mp
    refine ⟨1, ?_⟩
    rw [← normalizer_rootPlane F true, Subgroup.map_equiv_normalizer_eq, hplane, map_one]
    change _ = (normalizer (rootPlane F true : Set PSL(3,F))).map (MonoidHom.id _)
    rw [Subgroup.map_id]
  obtain ⟨m,σ,he⟩ := linearField_factorization F a hlin
  have hm : m ∈ glBorel F := ResidualLinear.linear_field_upperTriangular m σ (by rwa [← he])
  have heq (t : F) : m.val 0 0 * σ t = t * m.val 1 1 := by
    have hu : projective F ⟨t,0,0⟩ ∈ unipotent F := by
      rw [← projective_range]
      exact ⟨_,rfl⟩
    obtain ⟨c,hc⟩ := (mem_projectiveCenter F _).mp (hd _ hu)
    apply first_coordinate F m hm σ t c
    rw [← he]
    calc
      a (projective F ⟨t,0,0⟩) =
        (a (projective F ⟨t,0,0⟩) * (projective F ⟨t,0,0⟩)⁻¹) *
          projective F ⟨t,0,0⟩ := by simp
      _ = projective F ⟨0,0,c⟩ * projective F ⟨t,0,0⟩ := by rw [hc]
      _ = projective F ⟨t,0,c⟩ := by
        rw [← map_mul]
        congr 1
        ext <;> simp
  have hdiag : m.val 0 0 = m.val 1 1 := by simpa using heq 1
  have hσ : σ = 1 := by
    ext t
    change σ t = t
    apply mul_left_cancel₀ (triangular_entry_ne_zero F m hm)
    simpa only [← hdiag, mul_comm] using heq t
  have ha' : a = linearConj F m := by simpa only [hσ,map_one,mul_one] using he
  rw [ha'] at hp ⊢
  exact ResidualInner.linearConj_twoPower_inner m (k := 1) (by simpa using hp)

end Matrix.PSL3Even.MinimalParabolicWitness
