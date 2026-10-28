module

public import Theory.Representation.SL3.AdjointCubicCentralizer.DeterminantTwist
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Two projective extensions of the same restricted adjoint action

Both conjugation and its determinant twist descend from GL₃(F₄) to the
literal PGL₃(F₄): scalar matrices have determinant one. The descended
representations agree on the image of SL₃. Consequently recognizing that
restriction cannot select the untwisted extension.

Source: the extension step in the proof of Aschbacher–Smith B.4.14, printed
p.98. No assertion about the source's chief factors or binary irreducibility
is made in this module.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix
namespace Representation.SL3.AdjointCubicCentralizer
variable (K : Type*) [Field K]

/-- The literal matrix carrier of the adjoint module. -/
abbrev TraceZero := (Matrix.traceLinearMap (Fin 3) K K).ker

/-- Trace-zero matrices are invariant under conjugation. -/
def adjointSubrepresentation : Subrepresentation (conjugation K 3) where
  toSubmodule := TraceZero K
  apply_mem_toSubmodule g X hX := by
    change Matrix.trace (g.val * X * g⁻¹.val) = 0
    rw [Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
    exact hX

/-- Trace-zero matrices are invariant under the determinant twist. -/
def twistedAdjointSubrepresentation : Subrepresentation (determinantTwist K) where
  toSubmodule := TraceZero K
  apply_mem_toSubmodule g X hX := by
    change Matrix.trace (Matrix.det g.val • (g.val * X * g⁻¹.val)) = 0
    rw [Matrix.trace_smul, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
    change Matrix.trace X = 0 at hX
    rw [hX, smul_zero]

abbrev adjointAction := (adjointSubrepresentation K).toRepresentation
abbrev twistedAdjointAction := (twistedAdjointSubrepresentation K).toRepresentation

/-- The determinant twist does not change the restricted adjoint SL₃ action. -/
theorem twistedAdjoint_specialLinear (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    twistedAdjointAction K (Matrix.SpecialLinearGroup.toGL g) =
      adjointAction K (Matrix.SpecialLinearGroup.toGL g) := by
  apply LinearMap.ext
  intro X
  apply Subtype.ext
  exact LinearMap.congr_fun (determinantTwist_specialLinear K g) X.val

private theorem conjugation_scalar (u : Kˣ) :
    conjugation K 3 (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  apply LinearMap.ext
  intro X
  change Matrix.scalar (Fin 3) (u : K) * X * Matrix.scalar (Fin 3) (↑u⁻¹ : K) = X
  ext i j
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  calc
    _ = ((u : K) * (↑u⁻¹ : K)) * X i j := by ac_rfl
    _ = X i j := by simp

private theorem twistedConjugation_scalar (hK : ∀ u : Kˣ, u^3 = 1) (u : Kˣ) :
    determinantTwist K (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  change Matrix.det (Matrix.scalar (Fin 3) (u : K)) •
    conjugation K 3 (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1
  rw [conjugation_scalar]
  have hdet : Matrix.det (Matrix.scalar (Fin 3) (u : K)) = 1 := by
    have h := congrArg Units.val (Matrix.GeneralLinearGroup.det_scalar (n := Fin 3) u)
    simpa only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Fintype.card_fin, Units.val_pow_eq_pow_val, hK, Units.val_one] using h
  rw [hdet, one_smul]

/-- The ordinary adjoint representation of the actual projective group. -/
def projectiveAdjoint : Representation K (Matrix.ProjGenLinGroup (Fin 3) K) (TraceZero K) :=
  QuotientGroup.lift _ (adjointAction K) (by
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u,rfl⟩ := hg
    change adjointAction K (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    exact LinearMap.congr_fun (conjugation_scalar K u) X.val)

/-- Over F₄ the determinant-twisted action also descends to the actual PGL₃. -/
def projectiveTwistedAdjoint (hK : ∀ u : Kˣ, u^3 = 1) :
    Representation K (Matrix.ProjGenLinGroup (Fin 3) K) (TraceZero K) :=
  QuotientGroup.lift _ (twistedAdjointAction K) (by
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u,rfl⟩ := hg
    change twistedAdjointAction K (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = 1
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    exact LinearMap.congr_fun (twistedConjugation_scalar K hK u) X.val)

@[simp] theorem projectiveAdjoint_mk (g : (Mat3 K)ˣ) :
    projectiveAdjoint K (Matrix.ProjGenLinGroup.mk g) = adjointAction K g := rfl

@[simp] theorem projectiveTwistedAdjoint_mk (hK : ∀ u : Kˣ, u^3 = 1) (g : (Mat3 K)ˣ) :
    projectiveTwistedAdjoint K hK (Matrix.ProjGenLinGroup.mk g) = twistedAdjointAction K g := rfl

/-- The two actual projective actions have identical restrictions through SL₃. -/
theorem projective_restrictions_equal (hK : ∀ u : Kˣ, u^3 = 1) :
    (projectiveTwistedAdjoint K hK).comp Matrix.SpecialLinearGroup.toPGL =
      (projectiveAdjoint K).comp Matrix.SpecialLinearGroup.toPGL := by
  apply MonoidHom.ext
  intro g
  exact twistedAdjoint_specialLinear K g

/-- Every scalar in the four-element field has cube one. -/
theorem units_cube_of_card_four [Finite K] (hcard : Nat.card K = 4) (u : Kˣ) : u^3 = 1 := by
  have hc : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hcard]
  simpa only [hc] using (pow_card_eq_one' (x := u))

private def fixedTypeEquiv (ω : Kˣ) (e : TraceZero K ≃ TraceZero K)
    (he : ∀ X, e (adjointAction K (diagonalUnit K ω) X) =
      twistedAdjointAction K (diagonalUnit K ω) (e X)) :
    fixedSpace K ω ≃ twistedFixedSpace K ω where
  toFun X := ⟨(e ⟨X.val, X.property.1⟩).val, by
    refine ⟨(e ⟨X.val, X.property.1⟩).property, ?_⟩
    have hx : adjointAction K (diagonalUnit K ω) ⟨X.val, X.property.1⟩ =
        ⟨X.val, X.property.1⟩ :=
      Subtype.ext ((mem_fixedSpace_iff_fixed K ω X.val).mp X.property).2
    have h := he ⟨X.val, X.property.1⟩
    rw [hx] at h
    exact (congrArg Subtype.val h).symm⟩
  invFun Y := ⟨(e.symm ⟨Y.val, Y.property.1⟩).val, by
    rw [mem_fixedSpace_iff_fixed]
    refine ⟨(e.symm ⟨Y.val, Y.property.1⟩).property, ?_⟩
    have hy : twistedAdjointAction K (diagonalUnit K ω) ⟨Y.val, Y.property.1⟩ =
        ⟨Y.val, Y.property.1⟩ := Subtype.ext Y.property.2
    have hh : adjointAction K (diagonalUnit K ω) (e.symm ⟨Y.val, Y.property.1⟩) =
        e.symm ⟨Y.val, Y.property.1⟩ := by
      apply e.injective
      rw [he, e.apply_symm_apply, hy]
    exact congrArg Subtype.val hh⟩
  left_inv X := by
    exact Subtype.ext (congrArg (fun Z : TraceZero K => Z.val)
      (e.symm_apply_apply ⟨X.val, X.property.1⟩))
  right_inv Y := by
    exact Subtype.ext (congrArg (fun Z : TraceZero K => Z.val)
      (e.apply_symm_apply ⟨Y.val, Y.property.1⟩))

/-- Even a set bijection cannot intertwine the two projective actions over F₄.
In particular, restricting scalars to F₂ cannot make them isomorphic modules. -/
theorem no_projective_intertwining_bijection [Finite K] (hcard : Nat.card K = 4)
    (ω : Kˣ) (hω : (ω : K) ≠ 1) :
    ¬ ∃ e : TraceZero K ≃ TraceZero K, ∀ g X,
      e (projectiveAdjoint K g X) =
        projectiveTwistedAdjoint K (units_cube_of_card_four K hcard) g (e X) := by
  rintro ⟨e,he⟩
  have hω2 := square_ne_one_of_cube K ω hω
    (congrArg Units.val (units_cube_of_card_four K hcard ω))
  let ef := fixedTypeEquiv K ω e
    (he (Matrix.ProjGenLinGroup.mk (diagonalUnit K ω)))
  have hc := Nat.card_congr ef
  rw [Module.natCard_eq_pow_finrank (K := K) (V := fixedSpace K ω),
    Module.natCard_eq_pow_finrank (K := K) (V := twistedFixedSpace K ω),
    finrank_fixedSpace K ω hω, finrank_twistedFixedSpace K ω hω hω2, hcard] at hc
  norm_num at hc

/-- The marked diagonal copy of the coefficient units. -/
def diagonalHom : Kˣ →* (Mat3 K)ˣ where
  toFun := diagonalUnit K
  map_one' := by apply Units.ext; exact block_one K
  map_mul' u v := by
    apply Units.ext
    change block K (↑(u*v) : K) 1 = block K (u : K) 1 * block K (v : K) 1
    rw [block_mul]
    simp

/-- The marked diagonal element remains nonidentity in the projective group. -/
theorem projective_diagonal_ne_one (ω : Kˣ) (hω : (ω : K) ≠ 1) :
    Matrix.ProjGenLinGroup.mk (diagonalUnit K ω) ≠ 1 := by
  intro h
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u,hu⟩ := h
  have h11 := congrArg (fun g : (Mat3 K)ˣ => g.val 1 1) hu
  have h00 := congrArg (fun g : (Mat3 K)ˣ => g.val 0 0) hu
  have hu1 : (u : K) = 1 := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, diagonalUnit, block] using h11
  have huω : (u : K) = (ω : K) := by
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, diagonalUnit, block] using h00
  exact hω (huω.symm.trans hu1)

/-- Over the four-element field the marked projective element has order three. -/
theorem projective_diagonal_order [Finite K] (hcard : Nat.card K = 4)
    (ω : Kˣ) (hω : (ω : K) ≠ 1) :
    orderOf (Matrix.ProjGenLinGroup.mk (diagonalUnit K ω)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [← map_pow]
    change Matrix.ProjGenLinGroup.mk ((diagonalHom K ω)^3) = 1
    rw [← map_pow, units_cube_of_card_four K hcard, map_one, map_one]
  · exact projective_diagonal_ne_one K ω hω

/-- Matrix coordinates identify this carrier with the existing trace-zero
endomorphism model, preserving the actual linear maps. -/
def matrixAdjointEquiv : BinaryDefiningFactors.AdjointSpace K ≃ₗ[K] TraceZero K where
  toFun X := ⟨LinearMap.toMatrix' X.val, by
    change Matrix.trace (LinearMap.toMatrix' X.val) = 0
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact X.property⟩
  invFun X := ⟨Matrix.toLin' X.val, by
    change LinearMap.trace K (Fin 3 → K) (Matrix.toLin' X.val) = 0
    rw [Matrix.trace_toLin'_eq]
    exact X.property⟩
  left_inv X := Subtype.ext (Matrix.toLin'_toMatrix' X.val)
  right_inv X := Subtype.ext (LinearMap.toMatrix'_toLin' X.val)
  map_add' X Y := Subtype.ext (map_add LinearMap.toMatrix' X.val Y.val)
  map_smul' c X := Subtype.ext (map_smul LinearMap.toMatrix' c X.val)

/-- The source model's restriction is the existing concrete adjoint SL₃ action. -/
def adjointRestrictionEquiv :
    (BinaryDefiningFactors.factorRep (RingHom.id K) .adjoint).Equiv
      ((projectiveAdjoint K).comp Matrix.SpecialLinearGroup.toPGL) :=
  .mk (matrixAdjointEquiv K) (by
    intro g
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    change LinearMap.toMatrix'
      (BinaryDefiningFactors.natural (RingHom.id K) g ∘ₗ X.val ∘ₗ
        BinaryDefiningFactors.natural (RingHom.id K) g⁻¹) =
      g.val * LinearMap.toMatrix' X.val * g⁻¹.val
    have hn (a : Matrix.SpecialLinearGroup (Fin 3) K) :
        LinearMap.toMatrix' (BinaryDefiningFactors.natural (RingHom.id K) a) = a.val := by
      change LinearMap.toMatrix' (Matrix.toLin' (a.val.map (RingHom.id K))) = a.val
      rw [LinearMap.toMatrix'_toLin']
      rfl
    simp only [LinearMap.toMatrix'_comp, hn, Matrix.mul_assoc])

end Representation.SL3.AdjointCubicCentralizer
