module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Quadratic regular multiplication and its involution in GL2

For an actual degree-two field extension E/F with a nonidentity involutory
F-automorphism, multiplication by units embeds E's unit group into GL2(F).
The automorphism is represented by an external involution which conjugates
unit multiplication by its given field action. Base-field units map to the
actual scalar matrices.

Choose a basis of the two-dimensional F-vector space E. The algebra
equivalence from endomorphisms to matrices transports multiplication and the
automorphism. Multiplication is faithful by evaluation at one. If the
automorphism were multiplication by a unit, its value at one would force
that unit to be one, contradicting nontriviality. Its multiplicativity gives
the conjugation relation; algebra-map compatibility gives the scalar equation.

This supplies the concrete quadratic representation for the nonsplit linear
Sylow model in Alperin--Brauer--Gorenstein II.2 Lemma 1 and II.3 Proposition 3
(article pages 17 and 26). The lemma itself needs no finiteness, parity, or
group-recognition assumption.
-/

namespace Matrix.GeneralLinearGroup

public theorem exists_quadratic_regular_representation
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (hdim : Module.finrank F E = 2)
    (σ : E ≃ₐ[F] E) (hσ : σ ^ 2 = 1) (hσne : σ ≠ 1) :
    ∃ (ρ : Eˣ →* GL (Fin 2) F) (w : GL (Fin 2) F),
      Function.Injective ρ ∧ w ^ 2 = 1 ∧ w ∉ ρ.range ∧
      (∀ a : Eˣ, w * ρ a * w⁻¹ = ρ (Units.map σ.toRingHom.toMonoidHom a)) ∧
      ∀ c : Fˣ, ρ (Units.map (algebraMap F E).toMonoidHom c) = scalar (Fin 2) c := by
  let b := Module.finBasisOfFinrankEq F E hdim
  let j : LinearMap.GeneralLinearGroup F E ≃* GL (Fin 2) F :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv
  let r : Eˣ →* LinearMap.GeneralLinearGroup F E :=
    Units.map (Algebra.lmul F E).toMonoidHom
  let v := LinearMap.GeneralLinearGroup.ofLinearEquiv σ.toLinearEquiv
  let ρ := j.toMonoidHom.comp r
  have hr : Function.Injective r :=
    Units.map_injective Algebra.lmul_injective
  have hv : v ^ 2 = 1 := by
    apply Units.ext
    ext x
    change σ (σ x) = x
    have h := DFunLike.congr_fun hσ x
    exact h
  refine ⟨ρ, j v, j.injective.comp hr, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hv, map_one]
  · rintro ⟨a, ha⟩
    have ha' : r a = v := j.injective ha
    have hval := congrArg (fun z : LinearMap.GeneralLinearGroup F E => z.val 1) ha'
    have haone : a = 1 := by
      apply Units.ext
      change (a : E) * 1 = σ 1 at hval
      simpa using hval
    rw [haone, map_one] at ha'
    apply hσne
    ext x
    exact (congrArg (fun z : LinearMap.GeneralLinearGroup F E => z.val x) ha').symm
  · intro a
    change j v * j (r a) * (j v)⁻¹ = j (r _)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg j
    apply Units.ext
    ext x
    change σ ((a : E) * σ.symm x) = σ (a : E) * x
    rw [map_mul, σ.apply_symm_apply]
  · intro c
    apply Units.ext
    change (LinearMap.toMatrixAlgEquiv b)
      (Algebra.lmul F E (algebraMap F E (c : F))) = Matrix.scalar (Fin 2) (c : F)
    rw [(Algebra.lmul F E).commutes, (LinearMap.toMatrixAlgEquiv b).commutes]
    rfl

end Matrix.GeneralLinearGroup
