module

public import Theory.SpecificGroups.SU3.OddRootFixers.NormalForms
public import Theory.SpecificGroups.SU3.BorelTorus.EvenCenterAction
public import Theory.SpecificGroups.SU3.BorelTorus.SemilinearActors.Coordinates
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Central root equations and the residual unitary field action

The trace of a central root matrix is one in characteristic two, so a
projective semilinear fixation equation is an equality of actual matrices.
The parameter-one equation forces an upper triangular representative with
equal outer diagonal entries. The other parameters then force pointwise
fixation of the Hermitian fixed field.

An automorphism fixing that field preserves the norm and trace of every
matrix-field element. Its image is consequently the element itself or its
Hermitian conjugate, and its square is the identity. Finite-field cyclicity
identifies the only nonidentity possibility with Hermitian conjugation.
`FieldElimination` uses these calculations to remove that possibility for an
odd-order actor, on both SU₃ and its actual projective image.

Source: GLS4, Chapter 4, proof of Lemma 3.6(c), especially the action of
Φ on Z(P); matrix conventions from Huppert II.10.12.
-/

public section
open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
open BorelTorus BorelTorus.EvenCenterAction BorelTorus.SemilinearActors
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private theorem intertwining_of_trace_one (A X : GL (Fin 3) E) (σ : E ≃+* E)
    (hX : X.val.trace = 1)
    (h : ProjGenLinGroup.mk X = ProjGenLinGroup.mk A *
      ProjGenLinGroup.map σ.toRingHom (ProjGenLinGroup.mk X) *
      (ProjGenLinGroup.mk A)⁻¹) :
    A.val * X.val.map σ = X.val * A.val := by
  have hp : ProjGenLinGroup.mk (A * GeneralLinearGroup.map σ.toRingHom X * A⁻¹) =
      ProjGenLinGroup.mk X := by
    simpa only [map_mul, map_inv, ProjGenLinGroup.map_mk] using h.symm
  obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have ht := congrArg (fun B : GL (Fin 3) E => B.val.trace) hc
  have hm : ((A * GeneralLinearGroup.map σ.toRingHom X * A⁻¹) *
      GeneralLinearGroup.scalar (Fin 3) c).val =
      (c : E) • (A.val * X.val.map σ * (A⁻¹).val) := by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, Matrix.mul_diagonal, mul_comm]
  rw [hm, trace_smul, trace_units_conj, ← AddMonoidHom.map_trace, hX, map_one,
    smul_eq_mul, mul_one] at ht
  have hc1 : c = 1 := Units.ext ht
  rw [hc1, map_one, mul_one] at hc
  exact congrArg Units.val (mul_inv_eq_iff_eq_mul.mp hc)

/-- Fixing every central root removes the scalar ambiguity and determines
both the matrix shape and the action on the fixed field. -/
theorem central_roots_force_triangular [CharP E 2]
    (σ : E ≃+* E) (u : J.unitarySubgroup)
    (hu : ∀ b : fixedField J,
      ProjGenLinGroup.mk (hermitianUnipotentGL J (centralCoord J (.ofAdd b))) =
        ProjGenLinGroup.mk u.val * ProjGenLinGroup.map σ.toRingHom
          (ProjGenLinGroup.mk (hermitianUnipotentGL J (centralCoord J (.ofAdd b)))) *
        (ProjGenLinGroup.mk u.val)⁻¹) :
    IsRootTriangular J u ∧ ∀ b : E, J.conj b = b → σ b = b := by
  have hm (b : fixedField J) :
      u.val.val * (!![1,0,(b:E);0,1,0;0,0,1]).map σ =
        !![1,0,(b:E);0,1,0;0,0,1] * u.val.val := by
    have h := intertwining_of_trace_one u.val
      (hermitianUnipotentGL J (centralCoord J (.ofAdd b))) σ
      (by simp [hermitianUnipotentGL, hermitianUnipotentMatrix, centralCoord,
        Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]) (hu b)
    change u.val.val * (!![1,0,(b:E);0,1,-J.conj 0;0,0,1]).map σ =
      !![1,0,(b:E);0,1,-J.conj 0;0,0,1] * u.val.val at h
    simpa only [map_zero, neg_zero] using h
  have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 2) (hm 1)
  have h20 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) (hm 1)
  have h21 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 1) (hm 1)
  have hout := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) (hm 1)
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h21 hout
  have hd : u.val.val 0 0 = u.val.val 2 2 := by linear_combination hout
  have h00 : u.val.val 0 0 ≠ 0 := by
    intro hz
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0)
      (show (u.val⁻¹).val * u.val.val = 1 by simp)
    simp [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, hz] at h
  refine ⟨⟨h10, h20, h21, hd⟩, ?_⟩
  intro b hb
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) (hm ⟨b, hb⟩)
  simp [Matrix.mul_apply, Fin.sum_univ_three] at he
  apply mul_left_cancel₀ h00
  rw [hd] at he ⊢
  linear_combination he

/-- A field automorphism fixing the Hermitian fixed field has square one.
The two roots of the norm/trace polynomial are x and its conjugate. -/
theorem field_square_of_fixed [Finite E] (σ : E ≃+* E)
    (hfix : ∀ b : E, J.conj b = b → σ b = b) : σ ^ 2 = 1 := by
  have hs (x : E) : σ x + σ (J.conj x) = x + J.conj x := by
    rw [← map_add]
    exact hfix _ (by rw [map_add, J.conj_involutive, add_comm])
  have hp (x : E) : σ x * σ (J.conj x) = x * J.conj x := by
    rw [← map_mul]
    exact hfix _ (by rw [map_mul, J.conj_involutive, mul_comm])
  have hor (x : E) : σ x = x ∨ σ x = J.conj x := by
    have hz : (σ x - x) * (σ x - J.conj x) = 0 := by
      linear_combination σ x * hs x - hp x
    simpa only [sub_eq_zero] using mul_eq_zero.mp hz
  ext x
  change σ (σ x) = x
  rcases hor x with hx | hx
  · rw [hx, hx]
  · rw [hx, field_conj_commute J σ, hx, J.conj_involutive]

/-- The only two possibilities for the residual field component. -/
theorem field_eq_one_or_conj_of_fixed [Finite E] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (σ : E ≃+* E) (hfix : ∀ b : E, J.conj b = b → σ b = b) :
    σ = 1 ∨ σ = J.conj := by
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr (J.field_involution_eq_conj n hn hcard hfixed σ
      (field_square_of_fixed J σ hfix) h)

end BenderSuzuki.MatrixGroups.HermitianForm.OddRootFixers
